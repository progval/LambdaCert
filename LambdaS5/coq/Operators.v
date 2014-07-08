Require Import String.
Require Import Store.
Require Import Monads.
Require Import Values.
Require Import Context.
Open Scope string_scope.

Implicit Type runs : Context.runs_type.
Implicit Type store : Store.store.

(****** Unary operators ******)

Definition typeof store (v : Values.value) :=
  match v with
  | Values.Undefined => Context.add_value_return store (String "undefined")
  | Values.Null => Context.add_value_return store (String  "null")
  | Values.String _ => Context.add_value_return store (String  "string")
  | Values.Number _ => Context.add_value_return store (String  "number")
  | Values.True | Values.False => Context.add_value_return store (String  "boolean")
  | Values.Object ptr =>
    assert_get_object_from_ptr store ptr (fun obj =>
      match (Values.object_code obj) with
      | Some  _ => Context.add_value_return store (String "function")
      | None => Context.add_value_return store (String  "object")
      end
    )
  | Values.Closure _ _ _ _ => (store, Fail "typeof got lambda")
  end
.

Definition prim_to_str store (v : Values.value) :=
  match v with
  | Undefined => Context.add_value_return store (String "undefined")
  | Null => Context.add_value_return store (String "null")
  | String s => Context.add_value_return store (String s)
  | Number n => (store, Fail "prim_to_str not implemented for numbers.") (* TODO *)
  | True => Context.add_value_return store (String "true")
  | False => Context.add_value_return store (String "false")
  | _ => (store, Fail "prim_to_str not implemented for this type.")
  end
.


Definition unary (op : string) : (Store.store -> Values.value -> Store.store * (@Context.result Values.value_loc)) :=
  match op with
  | "typeof" => typeof
  | "prim->str" => prim_to_str
  | _ => fun store _ => (store, Context.Fail ("Unary operator " ++ op ++ " not implemented."))
  end
.

(****** Binary operators ******)

Definition stx_eq store v1 v2 :=
  match (v1, v2) with
  | (String s1, String s2) => Context.add_value_return store (if (string_dec s1 s2) then True else False)
  | (Null, Null) => Context.add_value_return store True
  | (Undefined, Undefined) => Context.add_value_return store True
  | (True, True) => Context.add_value_return store True
  | (False, False) => Context.add_value_return store True
  | (Number n1, Number n2) => (store, Fail "Number comparison not implemented.") (* TODO *)
  | _ => Context.add_value_return store False
  end
.

Definition has_own_property store v1 v2 :=
  match (v1, v2) with
  | (Object ptr, String s) =>
    assert_get_object_from_ptr store ptr (fun obj =>
      match (Values.get_object_property obj s) with
      | Some _ => Context.add_value_return store True
      | None => Context.add_value_return store False
      end
    )
  | _ => (store, Fail "hasOwnProperty expected an object and a string.")
  end
.
      

Definition binary (op : string) : (Store.store -> Values.value -> Values.value -> Store.store * (@Context.result Values.value_loc)) :=
  match op with
  | "stx=" => stx_eq 
  | "hasOwnProperty" => has_own_property
  | _ => fun store _ _ => (store, Context.Fail ("Binary operator " ++ op ++ " not implemented."))
  end
.
