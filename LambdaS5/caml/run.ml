let parse_es5 cin name =
  let lexbuf = Lexing.from_channel cin in
    try 
      (* Set the correct filename in lexbuf (for source-tracking). *)
      lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name };
      Ljs_parser.prog Ljs_lexer.token lexbuf
    with
      |  Failure "lexing: empty token" ->
           failwith "lexical error"
      | Failure "utf8_of_point not implemented" ->
        failwith "Parser doesn't do some UTF8 encoding crap"
      | _ -> failwith (Printf.sprintf "parse error; unexpected token %s"
                       (Lexing.lexeme lexbuf))


let _ =
  let (store, result) = Interpreter.runs_eval 1000 Values.create_store (parse_es5 stdin "stdin") in
  (match result with
  | Context.Return v -> print_string (PrettyPrint.string_of_value_loc store v)
  | Context.Exception e -> print_string "Uncaught exception: "; print_string (PrettyPrint.string_of_value_loc store e)
  | Context.Fail f -> print_string "Fail: "; print_string (CoqUtils.implode f)
  );
  print_string "\n"
