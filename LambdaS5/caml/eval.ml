

let rec chain_files (main : Syntax.expression) (args : string list) (st : Store.store) : (Store.store * Syntax.expression) =
  match args with
  | [] -> (st, main)
  | (head :: ("-load" :: tail)) -> chain_files main tail (Marshal.from_channel (open_in head))
  | "-load" :: tail -> failwith "-load at last position."
  | (head :: tail) -> chain_files ((Run.parse_es5_env (Run.get_channel head) head) main) tail st

let eval_args = function
  | [] -> failwith "No arguments."
  | (filename :: ("-save" :: args)) -> (Some filename, chain_files (Syntax.String (CoqUtils.explode "dumped")) args (Store.create_store))
 
  | (filename :: args) -> (None, chain_files (Run.parse_es5 (Run.get_channel filename) filename) args (Store.create_store))

let _ =
  let (dump_filename_option, (store, ast)) = eval_args (List.rev (List.tl (Array.to_list Sys.argv))) in
  match (dump_filename_option) with
  | None -> Run.print_result (Run.eval_ast store ast)
  | Some dump_filename ->
    let (store, res) = Run.eval_ast Store.create_store ast in
    let dump_channel = open_out dump_filename in
    Marshal.to_channel dump_channel store [Marshal.Closures];
    Run.print_result (store, res)
