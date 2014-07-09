let _ =
  match (Array.to_list Sys.argv) with
  | [] -> failwith "Sys.argv empty"
  | (prog :: (env_filename :: (dump_filename :: []))) -> (
      let env_channel = Run.get_channel env_filename in
      let dump_channel = open_out dump_filename in
      let env = Run.parse_es5_env env_channel env_filename in
      let (store, res) = Run.eval_ast (env (Syntax.String [])) in
      Marshal.to_channel dump_channel store [Marshal.Closures];
      Run.print_result (store, res)
    )
  | (prog :: _) -> Printf.printf "Syntax: %s <env> <output>\n" prog
