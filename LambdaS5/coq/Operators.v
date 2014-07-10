Require Import JsNumber.
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

Definition prim_to_bool store (v : Values.value) :=
  match v with
  | True => Context.add_value_return store True
  | False => Context.add_value_return store False
  | Undefined => Context.add_value_return store False
  | Null => Context.add_value_return store False
  | Number n => Context.add_value_return store (
      if (decide(n = JsNumber.nan)) then
        False
      else if (decide(n = JsNumber.zero)) then
        False
      else if (decide(n = JsNumber.neg_zero)) then
        False
      else
        True
    )
  | String "" => Context.add_value_return store False
  | String _ => Context.add_value_return store True
  | _ => Context.add_value_return store True
  end
.


Definition unary (op : string) : (Store.store -> Values.value -> Store.store * (@Context.result Values.value_loc)) :=
  match op with
  | "typeof" => typeof
  | "prim->str" => prim_to_str
  | "prim->bool" => prim_to_bool
  | _ => fun store _ => (store, Context.Fail ("Unary operator " ++ op ++ " not implemented."))
  end
.

(****** Binary operators ******)

Definition stx_eq store v1 v2 :=
  match (v1, v2) with
  | (String s1, String s2) => Context.add_value_return store (if (decide(s1 = s2)) then True else False)
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
      

Definition prop_to_obj store v1 v2 :=
  let make_attr := (fun x => attributes_data_of (attributes_data_intro x false false false)) in
  match (v1, v2) with
  | (Object ptr, String s) =>
    assert_get_object_from_ptr store ptr (fun obj =>
      match (Values.get_object_property obj s) with
      | Some (attributes_data_of (attributes_data_intro val writ enum config)) =>
        let (store, proto_loc) := Store.add_value store Undefined in
        let (store, config_loc) := Store.add_bool store config in
        let (store, enum_loc) := Store.add_bool store enum in
        let (store, writable_loc) := Store.add_bool store writ in
        let props := Heap.write Heap.empty "configurable" (make_attr config_loc) in
        let props := Heap.write props "enumerable" (make_attr enum_loc) in
        let props := Heap.write props "writable" (make_attr writable_loc) in
        let props := Heap.write props "value" (make_attr val) in
        let obj := object_intro proto_loc "Object" false None props None in
        let (store, loc) := Store.add_object store obj in
        (store, Return loc)
      | Some (attributes_accessor_of (attributes_accessor_intro get set enum config)) =>
        let (store, proto_loc) := Store.add_value store Undefined in
        let (store, config_loc) := Store.add_bool store config in
        let (store, enum_loc) := Store.add_bool store enum in
        let props := Heap.write Heap.empty "configurable" (make_attr config_loc) in
        let props := Heap.write props "enumerable" (make_attr enum_loc) in
        let props := Heap.write props "setter" (make_attr set) in
        let props := Heap.write props "getter" (make_attr get) in
        let obj := object_intro proto_loc "Object" false None props None in
        let (store, loc) := Store.add_object store obj in
        (store, Return loc)
      | None => Context.add_value_return store Undefined
      end
    )
  | _ => (store, Fail "hasOwnProperty expected an object and a string.")
  end
.

Definition binary (op : string) : (Store.store -> Values.value -> Values.value -> Store.store * (@Context.result Values.value_loc)) :=
  match op with
  | "stx=" => stx_eq 
  | "hasOwnProperty" => has_own_property
  | "__prop->obj" => prop_to_obj (* For debugging purposes *)
  | _ => fun store _ _ => (store, Context.Fail ("Binary operator " ++ op ++ " not implemented."))
  end
.
