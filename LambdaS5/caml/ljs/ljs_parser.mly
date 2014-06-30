%{

open Syntax

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
      exp (String.length s - 1) []

%}

%token <int> INT
%token <float> NUM
%token <char list> STRING
%token <char list> HINT
%token <bool> BOOL
%token <char list> ID
%token UNDEFINED NULL FUNC LET DELETE LBRACE RBRACE LPAREN RPAREN LBRACK
  RBRACK EQUALS COMMA DEREF REF COLON COLONEQ PRIM IF ELSE SEMI
  LABEL BREAK TRY CATCH FINALLY THROW EQEQEQUALS TYPEOF
  AMPAMP PIPEPIPE RETURN BANGEQEQUALS FUNCTION REC WRITABLE GETTER SETTER
  CONFIG VALUE ENUM LT GT PROTO CODE EXTENSIBLE CLASS EVAL GETFIELDS PRIMVAL


%token EOF
%left COLONEQ
%left PIPEPIPE
%left AMPAMP
%left EQEQEQUALS BANGEQEQUALS
%left LBRACK
%left ELSE
%left LPAREN

%type <Syntax.expression> prog
%type <Syntax.expression -> Syntax.expression> env

%start prog
%start env

%%

const :
 | NUM { Number $1 }
 | INT {  Number (float_of_int $1) }
 | STRING { String $1 }
 | UNDEFINED { Undefined  }
 | NULL { Null }
 | BOOL { if $1
          then True
          else False }

more_oattrs :
 | COMMA oattrsv { $2 }
 | COMMA { default_object_attributes }
 | { default_object_attributes }

oattrsv :
 | PRIMVAL COLON exp more_oattrs { match $4 with ObjectAttributes (p, c, p', k, e) -> ObjectAttributes (Some $3, c, p', k, e) }
 | EXTENSIBLE COLON BOOL more_oattrs { match $4 with ObjectAttributes (p, c, p', k, e) -> ObjectAttributes (p, c, p', k, $3) }
 | PROTO COLON exp more_oattrs { match $4 with ObjectAttributes (p, c, p', k, e) -> ObjectAttributes (p, c, Some $3, k, e) }
 | CODE COLON exp more_oattrs { match $4 with ObjectAttributes (p, c, p', k, e) -> ObjectAttributes (p, Some $3, p', k, e) }
 | CLASS COLON STRING more_oattrs { match $4 with ObjectAttributes (p, c, p', k, e) -> ObjectAttributes (p, c, p', $3, e) }

oattr_name :
 | PRIMVAL { Primval }
 | PROTO { Proto }
 | CODE { Code }
 | CLASS { Class }
 | EXTENSIBLE { Extensible }

attr_name :
 | WRITABLE { Writable }
 | CONFIG { Config }
 | VALUE { Value }
 | SETTER { Setter }
 | GETTER { Getter }
 | ENUM { Enum }

prop_attrs :
 | VALUE exp COMMA WRITABLE BOOL
     { DataProperty (Data ($2, $5), false, false) }
 | VALUE exp COMMA WRITABLE BOOL COMMA CONFIG BOOL
     { DataProperty (Data ($2, $5), false, $8) }
 | VALUE exp COMMA WRITABLE BOOL COMMA CONFIG BOOL COMMA ENUM BOOL
     { DataProperty (Data ($2, $5), $11, $8) }
 | VALUE exp COMMA WRITABLE BOOL COMMA ENUM BOOL COMMA CONFIG BOOL
     { DataProperty (Data ($2, $5), $8, $11) }
 | GETTER exp COMMA SETTER exp
     { AccessorProperty (Accessor ($2, $5), false, true) }

prop :
 | STRING COLON LBRACE prop_attrs RBRACE { ($1, $4) }
 | ID COLON LBRACE prop_attrs RBRACE { ($1, $4) }

props :
 | { [] }
 | prop { [$1] }
 | prop COMMA props { $1 :: $3 }

exps :
 | { [] }
 | unbraced_seq_exp { [$1] }
 | unbraced_seq_exp COMMA exps { $1 :: $3 }

ids :
 | { [] }
 | ID { [$1] }
 | ID COMMA ids { $1 :: $3 }

func :
 | FUNC LPAREN ids RPAREN braced_seq_exp { Lambda ($3, $5) }

atom :
 | const { $1 }
 | ID { Id $1 }
 | LBRACE LBRACK oattrsv RBRACK props RBRACE { ObjectDecl ($3, $5)}
 | LBRACE LBRACK RBRACK props RBRACE { ObjectDecl (default_object_attributes, $4 )}
 | braced_seq_exp { $1 }
 | LPAREN unbraced_seq_exp RPAREN { $2 }
 | func { $1 }
 | TYPEOF atom { Op1 (explode "typeof", $2) }
     
exp :
 | atom { $1 }
 | exp LPAREN exps RPAREN 
   { App ($1, $3) }
 | GETFIELDS LPAREN exp RPAREN
   { OwnFieldNames $3 }
 | EVAL LPAREN exp COMMA exp RPAREN
     { Eval ($3, $5) }
 | PRIM LPAREN STRING COMMA unbraced_seq_exp COMMA unbraced_seq_exp RPAREN
   { Op2 ($3, $5, $7) }
 | PRIM LPAREN STRING COMMA unbraced_seq_exp RPAREN
   { Op1 ($3, $5) }
 | ID COLONEQ exp
   { SetBang ($1, $3) }
 | exp EQEQEQUALS exp
     { Op2 (explode "stx=", $1, $3) }
 | exp BANGEQEQUALS exp
     { If (Op2 (explode "stx=", $1, $3), False, True) }
 | exp LBRACK unbraced_seq_exp EQUALS unbraced_seq_exp RBRACK
   { Let (explode "$newVal", $5,
	     SetField ($1, $3, 
		       Id (explode "$newVal"), 
		       ObjectDecl (default_object_attributes,
            [(explode "0", DataProperty (Data (Id (explode "$newVal"), true),
              true, true))])))
    }
 | exp LBRACK unbraced_seq_exp EQUALS unbraced_seq_exp COMMA unbraced_seq_exp RBRACK
   { SetField ($1, $3, $5, $7) }
 | exp LBRACK unbraced_seq_exp RBRACK
   { GetField ($1,  $3,
		       ObjectDecl (default_object_attributes, [])) }
 | exp LBRACK unbraced_seq_exp COMMA unbraced_seq_exp RBRACK
   { GetField ($1, $3, $5) }
 | exp LBRACK DELETE unbraced_seq_exp RBRACK
     { DeleteField ($1, $4) }
 | exp LBRACK unbraced_seq_exp LT attr_name GT RBRACK
     { GetAttr ($5, $1, $3) }
 | exp LBRACK unbraced_seq_exp LT attr_name GT EQUALS unbraced_seq_exp RBRACK
     { SetAttr ($5, $1, $3, $8) }
 | exp LBRACK LT oattr_name GT RBRACK
     { GetObjAttr($4, $1) }
 | exp LBRACK LT oattr_name GT EQUALS unbraced_seq_exp RBRACK
     { SetObjAttr($4, $1, $7) }
 | exp AMPAMP exp { If ($1, $3, False) }
 | exp PIPEPIPE exp
     { Let (explode "%or", $1, If (Id (explode "%or"), Id (explode "%or"), $3)) }


cexp :
 | exp { $1 }
 | ifexp { $1 }
 | LPAREN HINT cexp RPAREN
     { Hint ($2, $3) }
 | LABEL ID COLON braced_seq_exp
     { Label ($2, $4) } 
 | BREAK ID cexp
   { Break ($2, $3) }
 | THROW cexp
   { Throw ($2) }
 | TRY braced_seq_exp CATCH braced_seq_exp
   { TryCatch ($2, $4) }
 | TRY braced_seq_exp FINALLY braced_seq_exp
   { TryFinally ($2, $4) }

ifexp :
 | IF LPAREN unbraced_seq_exp RPAREN braced_seq_exp ELSE ifexp
     { If ($3, $5, $7) }
 | IF LPAREN unbraced_seq_exp RPAREN braced_seq_exp ELSE braced_seq_exp
     { If ($3, $5, $7) }
 | IF LPAREN unbraced_seq_exp RPAREN braced_seq_exp
     { If ($3, $5, Undefined) }

braced_seq_exp :
 | LBRACE unbraced_seq_exp RBRACE { $2 }

unbraced_seq_exp :
 | unbraced_seq_item SEMI unbraced_seq_exp { Seq ($1, $3) }
 | unbraced_seq_item { $1 }

unbraced_seq_item :
 | cexp { $1 }
 | LET LPAREN ID EQUALS unbraced_seq_exp RPAREN unbraced_seq_item
   { Let ($3, $5, $7) }
 | REC LPAREN ID EQUALS func RPAREN unbraced_seq_item
   { Rec ($3, $5, $7) }

env :
 | EOF
     { fun x -> x }
 | LET LBRACK ID RBRACK EQUALS unbraced_seq_exp env
     { fun x -> 
           Let ($3, $6, $7 x) }
 | REC LBRACK ID RBRACK EQUALS unbraced_seq_exp env
     { fun x -> Rec ($3, $6, $7 x) }
 | braced_seq_exp env { fun x -> Seq ($1, $2 x) }

prog :
 | unbraced_seq_exp EOF { $1 }
%%
