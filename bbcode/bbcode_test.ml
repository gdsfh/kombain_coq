
let () =
  let file = Sys.argv.(1) in
  let content = Kmb_input.read_file file in
  let result = Bbcode_parser.parse content in
    match result with
      | Kmb_lib.Failed ->
        Printf.printf "failed"
      | Kmb_lib.Parsed (ast, rest) ->
        Printf.printf "Parsed\n";
        (* List.iter print_token ast *)
        
