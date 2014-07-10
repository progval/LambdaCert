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
  | Number n => Context.add_value_return store (String (JsNumber.to_string n))
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

Definition nnot store (v : Values.value) :=
  match v with
  | Undefined => Context.add_value_return store True
  | Null => Context.add_value_return store True
  | True => Context.add_value_return store False
  | False => Context.add_value_return store True
  | Number d => Context.add_value_return store (
      if (decide(d = JsNumber.zero)) then
        True
      else if (decide(d = JsNumber.neg_zero)) then
        True
      else if (decide(d <> d)) then
        True
      else
        False
    )
  | String "" => Context.add_value_return store True
  | String _ => Context.add_value_return store False
  | Object _ => Context.add_value_return store False
  | Closure _ _ _ _ => Context.add_value_return store False
  end
.

Parameter _print_string : string -> unit.
Definition _seq {X Y : Type} (x : X) (y : Y) : Y :=
  y
.

Definition print store (v : Values.value) :=
  match v with
  | String s => _seq (_print_string s) (Context.add_value_return store Undefined)
  | Number n => _seq (_print_string (JsNumber.to_string n)) (Context.add_value_return store Undefined)
  | _ => (store, Fail "print of non-string and non-number.")
  end
.

Definition unary (op : string) runs store v_loc : (Store.store * (@Context.result Values.value_loc)) :=
  assert_deref store v_loc (fun v =>
    match op with
    | "print" => print store v
    | "typeof" => typeof store v
    | "prim->str" => prim_to_str store v
    | "prim->bool" => prim_to_bool store v
    | "!" => nnot store v
    | _ => (store, Context.Fail ("Unary operator " ++ op ++ " not implemented."))
    end
  )
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

Definition has_property runs store v1_loc v2 :=
  match v2 with
  | String s =>
    let (store, res) := Context.runs_type_get_property runs store (v1_loc, s) in
    if_return store res (fun ret =>
      match ret with
      | Some _ => Context.add_value_return store True
      | None => Context.add_value_return store False
      end
    )
  | _ => (store, Fail "hasProperty expected a string.")
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
        let obj := object_intro proto_loc "Object" false None props nil None in
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
        let obj := object_intro proto_loc "Object" false None props nil None in
        let (store, loc) := Store.add_object store obj in
        (store, Return loc)
      | None => Context.add_value_return store Undefined
      end
    )
  | _ => (store, Fail "hasOwnProperty expected an object and a string.")
  end
.

Definition arith store (op : number -> number -> number) (v1 v2 : Values.value) : (Store.store * Context.result) :=
  match (v1, v2) with
  | (Number n1, Number n2) => Context.add_value_return store (Number (op n1 n2))
  | _ => (store, Fail "Arithmetic with non-numbers.")
  end
.

Definition binary (op : string) runs store v1_loc v2_loc : (Store.store * (@Context.result Values.value_loc)) :=
  assert_deref store v1_loc (fun v1 =>
    assert_deref store v2_loc (fun v2 =>
      match op with
      | "+" => arith store JsNumber.add v1 v2
      | "stx=" => stx_eq store v1 v2
      | "hasProperty" => has_property runs store v1_loc v2
      | "hasOwnProperty" => has_own_property store v1 v2
      | "__prop->obj" => prop_to_obj store v1 v2 (* For debugging purposes *)
      | _ => (store, Context.Fail ("Binary operator " ++ op ++ " not implemented."))
      end
  ))
.
