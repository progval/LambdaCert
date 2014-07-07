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


let eval_ast ast =
  Interpreter.runs_eval 1000 Store.create_store ast

let print_result (store, result) =
  (match result with
  | Context.Return v -> print_string (PrettyPrint.string_of_value_loc 5 store v)
  | Context.Exception e -> print_string "Uncaught exception: "; print_string (PrettyPrint.string_of_value_loc 5 store e)
  | Context.Fail f -> print_string "Fail: "; print_string (CoqUtils.implode f)
  );
  print_string "\n"

let get_channel filename =
  if (filename = "stdin") then
    stdin
  else
    open_in filename

let rec chain_files (main : Syntax.expression) (args : string list) : Syntax.expression =
  match args with
  | [] -> main
  | (head :: tail) -> chain_files ((parse_es5_env (get_channel head) head) main) tail

let run = function
  | [] -> failwith "No arguments."
  | (filename :: envs) -> chain_files (parse_es5 (get_channel filename) filename) envs

let _ =
  print_result (eval_ast (run (List.rev (List.tl (Array.to_list Sys.argv)))))
