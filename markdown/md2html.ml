open HTML5.M
open HTML5.P
open Markdown_lib


let parse s =
  let result = Markdown_parser.parse s in
    match result with
      | Kmb_lib.Failed -> failwith "Failed to parse"
      | Kmb_lib.Parsed (ast, rest) -> ast

let rec render els =
  let r =
    List.fold_right (fun el acc ->
      match el with
        | Text s -> s :: acc
        | Strong xs -> render xs :: acc
        | Emph xs -> render xs :: acc
        | LineBreak -> acc;
        | Space -> " " :: acc
        | Link _ | Image _ -> acc
        | _ -> acc
    ) els [] in
    String.concat " " r

let lookup r refs =
  try Some (List.assoc r refs) with Not_found -> None


let make_image (l, (u, t)) =
  match t with
    | None -> img ~src:u ~alt:(render l) ()
    | Some t -> img ~src:u ~alt:(render l) ~a:[a_title t] ()
    
let rec link_inline refs (els:inline list) =
  List.fold_right (fun el acc ->
    match el with
      | Text s -> pcdata s :: acc
      | Entity s -> pcdata ("&" ^ s ^ ";") :: acc
      | Space -> pcdata " " :: acc
      | LineBreak -> br () :: acc
      | Emph xs -> em (link_inline refs xs) :: acc
      | Strong xs -> strong (link_inline refs xs) :: acc
      | Image (l, Src (u,t)) -> make_image (l,(u,t)) :: acc
      | Image (l, Nothing) -> (
        match lookup l refs with
          | Some (u, t) -> make_image (l, (u,t)) :: acc
          | None -> link_inline refs (Text "![" :: l @ [Text "]"]) @ acc
      )
      | Image (l, Ref (r, s)) -> (
        let r' = if r = [] then l else r in
          match lookup r' refs with
            | Some (u, t) -> make_image (l, (u, t)) :: acc
            | None -> link_inline refs (Text "![" :: l @
                                          (Text "]" :: Text s ::
                                             Text "[" :: r @ [Text "]"]))
              @ acc
      )
      | Code s -> print_endline "code in link"; acc
      | Html s -> print_endline ("html in link " ^ s); acc
      | Link (l, Nothing) -> link_inline refs (Text "[" :: l @ [Text "]"]) @ acc
      | Link (l, _) -> print_endline ("link in link " ^ render l) ; acc
  ) els []

and make_link refs (l, target) =
  match target with
    | Src (u, None) ->
      a ~a:[a_href u] (link_inline refs l)
    | Src (u, Some t) ->
      a ~a:[a_href u; a_title t] (link_inline refs l)

let rec html_of_inline refs els =
  List.fold_right (fun el acc ->
    match el with
      | Text s -> pcdata s :: acc
      | Entity s -> pcdata ("&" ^ s ^ ";") :: acc
      | Space -> pcdata " " :: acc
      | LineBreak -> br () :: acc
      | Code s -> code [pcdata s] :: acc
      | Emph xs -> em ~a:[] (html_of_inline refs xs) :: acc
      | Strong xs -> strong ~a:[] (html_of_inline refs xs) :: acc
      | Html s -> print_endline ("html in inline " ^ s); acc
      | Image (l, Src (u,t)) ->
        make_image (l, (u,t)) :: acc
      | Image (l, Nothing) -> (
        match lookup l refs with
          | Some (u, t) -> make_image (l, (u,t)) :: acc
          | None -> html_of_inline refs (Text "![" :: l @ [Text "]"]) @ acc
      )
      | Image (l, Ref (r, s)) -> (
        let r' = if r = [] then l else r in
          match lookup r' refs with
            | Some (u, t) -> make_image (l, (u, t)) :: acc
            | None -> html_of_inline refs (Text "![" :: l @
                                             (Text "]" :: Text s ::
                                                Text "[" :: r @ [Text "]"]))
              @ acc
      )
      | Link (l, Src (u, t)) ->
        make_link refs (l, Src (u,t)) :: acc
      | Link (l, Nothing) -> (
        match lookup l refs with
          | Some (u, t) -> make_link refs (l, Src (u, t)) :: acc
          | None ->
            List.concat [[pcdata "["]; html_of_inline refs l;
                         (pcdata "]" :: acc)]
      )
      | Link (l, Ref (r, s)) -> (
        let r' = if r = [] then l else r in
          match lookup r' refs with
            | Some (u, t) -> make_link refs (l, Src (u, t)) :: acc
            | None ->
              List.concat [[pcdata "["]; html_of_inline refs l; [pcdata "]"];
                           [pcdata s]; [pcdata "["];
                           html_of_inline refs r; [pcdata "]"]; acc]
      )
  ) els []

let rec html_of_block refs els =
  List.fold_right (fun el acc ->
    match el with
      | Para xs -> p (html_of_inline refs xs) :: acc
      | Plain xs -> p (html_of_inline refs xs) :: acc
      | Heading (lev, xs) -> (
        match lev with
          | 1 -> h1 (html_of_inline refs xs) :: acc
          | 2 -> h2 (html_of_inline refs xs) :: acc
          | 3 -> h3 (html_of_inline refs xs) :: acc
          | 4 -> h4 (html_of_inline refs xs) :: acc
          | 5 -> h5 (html_of_inline refs xs) :: acc
          | 6 -> h6 (html_of_inline refs xs) :: acc
          | _ -> assert false
      )
      | HorizontalRule -> hr () :: acc
      | BlockQuote xs -> blockquote (html_of_block refs xs) :: acc
      | Verbatim s -> pre [code  [pcdata s]] :: acc
      | BulletList  items ->
        ul (List.map (fun i -> li  (html_of_block refs i)) items) :: acc
      | OrderedList items ->
        ol (List.map (fun i -> li  (html_of_block refs i)) items) :: acc
      | Markdown m ->
        let ast = parse m in
          html_of_block refs ast @ acc
      | Reference _ -> acc
      | HTMLBlock s -> print_endline "htmlblock in block"; acc
  ) els []
    
let make_html5 ast =
  let refs =
    List.fold_left (fun acc -> function
      | Reference (l, Src (s, t)) -> (l, (s, t)) :: acc
      | _ -> acc
    ) [] ast in
    html (head (title (pcdata "abc")) [])
      (body (html_of_block refs ast))

let () =
  let mdfile = Sys.argv.(1) in
  let content = Kmb_input.read_file mdfile in
  let ast = parse content in
  let outfile = Sys.argv.(2) in
  let oc = open_out outfile in
  let output str = output oc str 0 (String.length str) in
    print ~output  (make_html5 ast);
    close_out oc
  
