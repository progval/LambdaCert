

let rec chain_files (main : Syntax.expression) (args : string list) : Syntax.expression =
  match args with
  | [] -> main
  | (head :: tail) -> chain_files ((Run.parse_es5_env (Run.get_channel head) head) main) tail

let eval = function
  | [] -> failwith "No arguments."
  | (filename :: envs) -> chain_files (Run.parse_es5 (Run.get_channel filename) filename) envs

let _ =
  Run.print_result (Run.eval_ast (eval (List.rev (List.tl (Array.to_list Sys.argv)))))
