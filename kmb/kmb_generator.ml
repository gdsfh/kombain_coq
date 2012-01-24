open Kmb_grammar
open Camlp4.PreCast;;
open Printf

module Caml =
  Camlp4.Printers.OCaml.Make
    (Camlp4OCamlParser.Make
       (Camlp4OCamlRevisedParser.Make(Syntax)))


open Syntax
    
let rec should_export rules names = function
  | Epsilon -> false
  | Name name -> (
    if List.mem name names then
      false
    else
      try should_export rules (name :: names)
            (List.assoc name rules) with Not_found ->
              printf "Warning: Not found rule: %s\n" name;
              false
  )
  | Transform _ -> true
  | Action (_, ts) ->
    List.fold_left (fun flag t -> flag && should_export rules names t) true ts
  | Tokenizer _ -> true
  | Pattern (_, expr) -> should_export rules names expr
  | PredicateNOT _ -> false
  | PredicateAND _ -> false
  | Opt expr -> should_export rules names expr
  | Plus expr -> should_export rules names expr
  | Star expr -> should_export rules names expr
  | Literal _ -> false
  | Class _ -> false
  | Any -> false
  | Alternate (e1, e2) -> should_export rules names e1
  | Sequence (e1, e2) ->
    should_export rules names e1 || should_export rules names e2

let rec make_rule_expr _loc rules names = function
  | Epsilon ->
    <:expr< peg_stub >>

  | Name name ->
    <:expr< $lid:name$ >>

  | Sequence (Pattern (name, expr), xs) ->
    let rules = (name, Epsilon) :: rules in
      <:expr< fun input ->
        match get_pattern $make_rule_expr _loc rules names expr$ input with
          | Parsed (r, input) ->
            let $lid:name$ = match_pattern r in
              $make_rule_expr _loc rules names xs$ input
          | Failed as failed -> failed
            >>

  | Pattern _ -> assert false

  | Sequence (x1, x2) ->
    let export_left = should_export rules names x1
    and export_right = should_export rules names x2 in
    let seq =
      match export_left, export_right with
        | true, true -> "seq_b"
        | true, false -> "seq_l"
        | false, true -> "seq_r"
        | false, false -> "seq_n"
    in
      <:expr< $lid:seq$ 
        $make_rule_expr _loc rules names x1$
        $make_rule_expr _loc rules names x2$ >>

  | Alternate (x1, x2) ->
    <:expr< alt $make_rule_expr _loc rules names x1$
      $make_rule_expr _loc rules names x2$ >>

  | Tokenizer t ->
    <:expr< get_lexeme $make_rule_expr _loc rules names t$ >>
 
  | Transform ({Kmb_input.start = (line, col); Kmb_input.lexeme = code}, expr) ->
    let code_expr =
      try Caml.AntiquotSyntax.parse_expr Loc.ghost code
      with exn ->
        printf "Bad action %d:%d %S\n" line col code;
        printf "Exception: %s\n" (Printexc.to_string exn);
        Pervasives.exit 1
    in
      <:expr< transform
        $make_rule_expr _loc rules names expr$
        $code_expr$
      >>

  | Action (expr, ts) ->
    List.fold_left
      (fun expr t -> <:expr< $expr$ $make_rule_expr _loc rules names t$ >>)
      expr ts
        
  | Opt t ->
    let export = should_export rules names t in
      if export then
        <:expr< opt_accu $make_rule_expr _loc rules names t$ >>
      else
        <:expr< opt $make_rule_expr _loc rules names t$ >>
      
  | Star t ->
    let export = should_export rules names t in
      if export then
        <:expr< star_accu $make_rule_expr _loc rules names t$ >>
      else
        <:expr< star $make_rule_expr _loc rules names t$ >>

  | Plus t ->
    let export = should_export rules names t in
      if export then
        <:expr< plus_accu $make_rule_expr _loc rules names t$ >>
      else
        <:expr< plus $make_rule_expr _loc rules names t$ >>
      
  | PredicateNOT t ->
    <:expr< predicate_not $make_rule_expr _loc rules names t$ >>

  | PredicateAND t ->
    <:expr< predicate_and $make_rule_expr _loc rules names t$ >>
      
  | Any ->
    <:expr< test_any >>
      
  | Literal chars -> (
    match chars with
      | [] -> <:expr< >>
      | [x] -> <:expr< test_char $`int:x$ >>
      | _ ->
        <:expr< match_pattern
          $List.fold_right (fun c acc ->
            <:expr< $`int:c$ :: $acc$ >>) chars <:expr< [] >> $ >>
  )
  | Class classes ->
    let make_expr = function
      | Range (x1, x2) ->
        <:expr< c >= $`int:x1$ && c <= $`int:x2$ >>
      | Char x -> <:expr< c = $`int:x$ >>
    in
    let exprs =
      List.fold_left (fun acc s ->
        <:expr< $make_expr s$ || $acc$ >>
      ) <:expr< $make_expr (List.hd classes)$ >> (List.tl classes) in
      <:expr< test_class (fun c -> $exprs$) >>
        

let make_rule_function _loc verbose name expr rules =
  printf "Generating for rule %s\n" name;
  if verbose then
    <:str_item<
      let $lid:name$ input =
        Printf.printf "Trying %s %s... " $str:name$
          $str:String.escaped (string_of_token expr)$;
        match $make_rule_expr _loc  rules [name] expr$ input with
          | Failed as result -> Printf.printf "Failed %s\n" $str:name$; result
          | Parsed _ as result -> Printf.printf "Success %s\n" $str:name$; result
            >>
  else
    <:str_item< let $lid:name$ input =
                  $make_rule_expr _loc rules [name] expr$ input
                  >>

let generate verbose declaration rules output_file =
  let (start_rule, _) = List.hd rules in
  let sorted = rearrange_grammar rules in
  let _loc = Loc.ghost in
  let bindings =
    List.fold_left (fun acc -> function
      | Simple simples ->
        List.fold_left (fun acc (name, expr) ->
          make_rule_function _loc verbose name expr rules :: acc) acc simples
      | Recursive rs ->
        let bs = List.map (fun (name, expr) ->
          <:binding< $lid:name$ input =
            $make_rule_expr _loc rules [name] expr$ input >>) rs in
          <:str_item< let rec $Ast.biAnd_of_list bs$ >> :: acc
    ) [] sorted
  in

    Caml.print_implem ~output_file
    <:str_item<
      open Kmb_lib
      
      $match declaration with
        | Some dcl ->
          Caml.parse_implem _loc (Stream.of_string dcl)
        | None ->
          <:str_item< >>
      $
            
$list:List.rev bindings$
            
let parse string =
  let input = Kmb_input.make_input string in
    $lid:start_rule$ input
    >>;
    
    printf "\n\nDone!\n"


