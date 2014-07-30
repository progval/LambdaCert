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

let parse_es5_env cin name =
  let lexbuf = Lexing.from_channel cin in
    try
      (* Set the correct filename in lexbuf (for source-tracking). *)
      lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name };
      Ljs_parser.env Ljs_lexer.token lexbuf
    with
      |  Failure "lexing: empty token" ->
           failwith "lexical error"
      | Failure "utf8_of_point not implemented" ->
        failwith "Parser doesn't do some UTF8 encoding crap"
      | _ -> failwith (Printf.sprintf "parse error; unexpected token %s"
                       (Lexing.lexeme lexbuf))


let eval_ast store ast =
  Interpreter.runs_eval max_int store ast

let print_result (store, result) =
  (match result with
  | Context.Return v -> print_string (PrettyPrint.string_of_value_loc 5 store v)
  | Context.Exception e -> print_string "Uncaught exception: "; print_string (PrettyPrint.string_of_value_loc 5 store e)
  | Context.Break (l, v) -> Printf.printf "Uncaught break %s: %s" (CoqUtils.implode l) (PrettyPrint.string_of_value_loc 5 store v)
  | Context.Fail f -> print_string "Fail: "; print_string (CoqUtils.implode f)
  | Context.Impossible f -> print_string "The impossible happened: "; print_string (CoqUtils.implode f)
  );
  print_string "\n"

let get_channel filename =
  if (filename = "stdin") then
    stdin
  else
    open_in filename
