Require Import List.
Require Import Coq.Strings.String.
Require Import Fappli_IEEE Fappli_IEEE_bits.

Definition id : Type := string.

Definition number : Type := Fappli_IEEE_bits.binary64.

Inductive object_attribute_name : Type :=
| Proto
| Class
| Extensible
| Primval
| Code
.

Inductive property_attribute_name : Type :=
| Value
| Getter
| Setter
| Config
| Writable
| Enum
.


Inductive expression : Type :=
| Null
| Undefined
| String : string -> expression
| Number : number -> expression
| True
| False
| Id : id -> expression
| ObjectDecl : object_attributes -> list (string * property) -> expression
| GetAttr : property_attribute_name -> expression -> expression -> expression (* property -> object -> field_name -> expression *)
| SetAttr : property_attribute_name -> expression -> expression -> expression -> expression (* property -> object -> field_name -> new_value -> expression *)
| GetObjAttr : object_attribute_name -> expression -> expression
| SetObjAttr : object_attribute_name -> expression -> expression -> expression
| GetField : expression -> expression -> expression -> expression (* left -> right -> args_object -> expression *)
| SetField : expression -> expression -> expression -> expression -> expression (* object -> field -> new_val -> args -> expression *)
| DeleteField : expression -> expression -> expression (* object -> field -> expression *)
| OwnFieldNames : expression -> expression
| SetBang : id -> expression -> expression
| Op1 : string -> expression -> expression
| Op2 : string -> expression -> expression -> expression
| If : expression -> expression -> expression -> expression
| App : expression -> list expression -> expression
| Seq : expression -> expression -> expression
| Let : id -> expression -> expression -> expression
| Rec : id -> expression -> expression -> expression (* Value bound must be lambda *)
| Label : id -> expression -> expression
| Break : id -> expression -> expression
| TryCatch : expression -> expression -> expression (* Catch block must be a lambda *)
| TryFinally : expression -> expression -> expression
| Throw : expression -> expression
| Lambda : list id -> expression -> expression
| Eval : expression -> expression -> expression (* string -> env_object -> expression *)
| Hint : string -> expression -> expression
with data : Type :=
| Data : expression -> bool -> data (* expression -> writable -> data *)
with accessor : Type :=
| Accessor : expression -> expression -> accessor (* getter -> setter -> accessor *)
with property : Type := 
| DataProperty : data -> bool -> bool -> property (* value -> enumerable -> configurable *)
| AccessorProperty : accessor -> bool -> bool -> property
with object_attributes : Type :=
| ObjectAttributes: option expression -> option expression -> option expression -> string -> bool -> object_attributes (* primval -> code -> prototype -> class -> extensible -> object_attributes *)
.

Definition default_object_attributes := ObjectAttributes None None None "Object" true.
