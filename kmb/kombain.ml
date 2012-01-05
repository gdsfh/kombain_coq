open Kmb_input
open Kmb_lib
open Kmb_grammar

let _ = Printexc.record_backtrace true

let () =
  let file = Sys.argv.(1) in
  let content = read_file file in
  let result = Peg_parser.parse content in
    match result with
      | Failed ->
        Printf.printf "failed";
      | Parsed ((dcl, ast), rest) ->
        List.iter (fun (name, rule) ->
          Printf.printf "Rule %s "; print_token rule) ast;
        Kmb_generator.generate dcl ast Sys.argv.(2)
