open Kmb_input
open Kmb_lib
open Printf

exception Error of string

type 'char class_t =
  | Char of 'char
  | Range of 'char * 'char

type 'char token =
  | Epsilon
  | Name of string
  | Literal of char list
  | Class of 'char class_t list
  | Action of (int * int) * string * 'char token
  | Any
  | Tokenizer of 'char token
  | Opt of 'char token
  | Plus of 'char token
  | Star of 'char token
  | PredicateNOT of 'char token
  | PredicateAND of 'char token
  | Sequence of 'char token * 'char token
  | Alternate of 'char token * 'char token
  | Pattern of string * 'char token

let rec print_token = function
  | Epsilon ->
    printf "Epsilon\n"
  | Name str ->
    printf "Name %S\n" str
  | Literal chars ->
    printf "Literal ";
    List.iter (fun c -> printf "%C " c) chars;
    printf "\n"
  | Class cs ->
    printf "Class\n"
  | Action ((line, col), str, expr) ->
    printf "Action %d:%d %S\n" line col str
  | Any ->
    printf "Any\n"
  | Tokenizer t ->
    printf "Tokenizer ["; print_token t; printf "]\n"
  | PredicateNOT token ->
    printf "Predicate NOT "; print_token token
  | PredicateAND token ->
    printf "Predicate AND "; print_token token    
  | Sequence (t1, t2) ->
    printf "Sequence [\n";
    print_token t1;
    print_token t2;
    printf "]\n"
  | Alternate (t1, t2) ->
    printf "Alternate [\n";
    printf "   "; print_token t1;
    printf "   "; print_token t2;
  | Opt t ->
    printf "Opt "; print_token t;
  | Plus t ->
    printf "Plus "; print_token t;
  | Star token ->
    printf "Star "; print_token token
  | Pattern (name, expr) ->
    printf "Pattern %s [\n" name;
    print_token expr;
    printf "]\n"

let make_declaration {lexeme} = lexeme

let make_name {lexeme} = Name lexeme

let make_char {lexeme} =
  lexeme.[0]
    
let make_escaped_char {lexeme} =
  match lexeme with
    | "b" -> '\b'
    | "n" -> '\n'
    | "r" -> '\r'
    | "t" -> '\t'
    | "\\" -> '\\'
    | c -> c.[0] 
      
let make_dec_char {lexeme} =
  Char.chr (int_of_string lexeme)

let make_hex_char {lexeme} =
  Char.chr (int_of_string ("0x" ^ lexeme))

let make_any_char _ _ lexeme =
  lexeme.[0]

let make_literal chars =
  Literal chars

let make_tokenizer expr = Tokenizer expr

let print_remaining input =
  printf "Remaining input:\n%S\n" 
    (String.sub input.buf input.pos (input.len - input.pos))
  
let make_alternates (s1, s2) =
  match List.rev s2 with
    | [] -> s1
    | [x] -> Alternate (s1, x)
    | x :: xs ->
      Alternate (s1, 
                 List.fold_left (fun acc s -> Alternate (s, acc)) x xs)

let make_sequence (items, a) =
  let expr =
    match List.rev items with
      | [] -> Epsilon
      | [x] -> x
      | x :: xs ->
        List.fold_left (fun acc i -> Sequence (i, acc)) x xs
  in
    match a with
      | None -> expr
      | Some {start; lexeme} -> Action (start, lexeme, expr)
    
let make_pattern ({lexeme}, expr) =
  Pattern (lexeme, expr)

let make_predicate_not () v = PredicateNOT v
let make_predicate_and () v = PredicateAND v

let make_class cs = Class cs

let make_prefix (f, s) =
  match f with
    | None -> s
    | Some f -> f s

let make_definition ({lexeme}, expr) =
  (lexeme, expr)

let unmatched {start = (line, col) ; lexeme} =
  raise (Error (sprintf "Unmatched %S at line %d col %d" lexeme line col))

let invalid_char {start = (line, col); lexeme} =
  raise (Error (sprintf "Invalid char %S at line %d col %d" lexeme line col))

let rec is_productive known = function
  | Name name -> List.mem name known
  | Class _ -> true
  | Literal _ -> true
  | Any -> true
  | Pattern (_, t) -> is_productive known t
  | PredicateAND t -> is_productive known t
  | PredicateNOT t -> is_productive known t
  | Tokenizer t -> is_productive known t
  | Action (_, _, t) -> is_productive known t
  | Star t -> is_productive known t
  | Opt t -> is_productive known t
  | Plus t -> is_productive known t
  | Epsilon -> true
  | Sequence (t1, t2) ->    
    is_productive known t1 && is_productive known t2
  | Alternate (t1, t2) ->
    is_productive known t1 && is_productive known t2
    

let simple_productive known rules =
  let rec aux_rearrange result known rest =
    let sorted, known, unsorted =
      List.fold_left (fun (acc, known, unsorted) (name, expr) ->
        if is_productive known expr then
          (name, expr) :: acc, name :: known, unsorted
        else
          acc, known, (name, expr) :: unsorted
      ) (result, known, []) rest in
      if sorted = result then
        List.rev result, known, List.rev unsorted
      else
        aux_rearrange sorted known unsorted
  in
    aux_rearrange [] known rules

type 'char productive =
  | Simple of (string * 'char token) list
  | Recursive of (string * 'char token) list


let string_of_char = function
  | '\n' -> "\\n"
  | '\r' -> "\\r"
  | '\b' -> "\\b"
  | '\t' -> "\\t"
  | '[' -> "\\["
  | ']' -> "\\]"
  | '-' -> "\\-"
  | c -> String.make 1 c

let rec string_of_token = function
  | Epsilon -> ""
  | Name name -> name
  | Literal cs ->
    let str = String.create (List.length cs) in
    let _ = List.fold_left (fun i c -> str.[i] <- c; succ i) 0 cs in
      "\"" ^ String.escaped str ^ "\""
  | Class cs ->
    List.fold_left (fun str -> function
      | Range (c1, c2) ->
        sprintf "%s%s-%s" str (string_of_char c1) (string_of_char c2)
      | Char c ->
        sprintf "%s%s" str (string_of_char c)
    ) "[" cs ^ "]"
  | PredicateNOT t -> "!" ^ string_of_token t
  | PredicateAND t -> "&" ^ string_of_token t
  | Opt t -> string_of_token t ^ "?"
  | Star t -> string_of_token t ^ "*"
  | Plus t -> string_of_token t ^ "+"
  | Sequence (s1, s2) ->
    sprintf "(%s %s)" (string_of_token s1) (string_of_token s2)
  | Alternate (a1, a2) ->
    sprintf "(%s / %s)" (string_of_token a1) (string_of_token a2)
  
let rearrange_grammar rules =
  let sorted, known, unsorted = simple_productive [] rules in
    match unsorted with
      | [] -> [Simple sorted]
      | _ ->
        [Simple sorted; Recursive unsorted]
