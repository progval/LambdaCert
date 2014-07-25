Require Import LibInt.
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
  | Values.Closure _ _ _ _ => (store, Fail Values.value_loc "typeof got lambda")
  end
.

Definition is_primitive store v :=
  match v with
  | Undefined | Null | String _ | Number _ | True | False =>
    Context.add_value_return store True
  | _ =>
    Context.add_value_return store False
  end
.

Definition void store (v : Values.value) :=
  Context.add_value_return store Undefined
.

Definition prim_to_str store (v : Values.value) :=
  match v with
  | Undefined => Context.add_value_return store (String "undefined")
  | Null => Context.add_value_return store (String "null")
  | String s => Context.add_value_return store (String s)
  | Number n => Context.add_value_return store (String (JsNumber.to_string n))
  | True => Context.add_value_return store (String "true")
  | False => Context.add_value_return store (String "false")
  | _ => (store, Fail Values.value_loc "prim_to_str not implemented for this type.")
  end
.

Definition prim_to_num store (v : Values.value) :=
  match v with
  | Undefined => Context.add_value_return store (Number JsNumber.nan)
  | Null => Context.add_value_return store (Number JsNumber.zero)
  | True => Context.add_value_return store (Number JsNumber.one)
  | False => Context.add_value_return store (Number JsNumber.zero)
  | Number n => Context.add_value_return store (Number n)
  | String "" => Context.add_value_return store (Number JsNumber.zero)
  | String s => Context.add_value_return store (Number (JsNumber.from_string s))
  | _ => (store, Fail value_loc "prim_to_num got invalid value.")
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
Parameter _pretty : nat -> store -> value -> unit.
Definition _seq {X Y : Type} (x : X) (y : Y) : Y :=
  y
.

Definition print store (v : Values.value) :=
  match v with
  | String s => _seq (_print_string s) (Context.add_value_return store Undefined)
  | Number n => _seq (_print_string (JsNumber.to_string n)) (Context.add_value_return store Undefined)
  | _ => (store, Fail Values.value_loc "print of non-string and non-number.")
  end
.

Definition pretty runs store v :=
  _seq
  (_pretty (Context.runs_type_nat_fuel runs) store v)
  (Context.add_value_return store Undefined)
.

Definition strlen store v :=
  match v with
  | String s => add_value_return store (Number (JsNumber.of_int (String.length s)))
  | _ => (store, Fail value_loc "strlen got non-string.")
  end
.

Definition numstr_to_num store (v : Values.value) :=
  match v with
  | String "" => Context.add_value_return store (Number JsNumber.zero)
  | String s => Context.add_value_return store (Number (JsNumber.from_string s))
  | _ => (store, Fail value_loc "numstr_to_num got invalid value.")
  end
.

Definition unary_arith store (op : number -> number) (v : Values.value) : (Store.store * Context.result Values.value_loc) :=
  match v with
  | Number n => Context.add_value_return store (Number (op n))
  | _ => (store, Fail Values.value_loc "Arithmetic with non-number.")
  end
.

Definition unary (op : string) runs store v_loc : (Store.store * (@Context.result Values.value_loc)) :=
  assert_deref store v_loc (fun v =>
    match op with
    | "print" => print store v
    | "pretty" => pretty runs store v
    | "strlen" => strlen store v
    | "typeof" => typeof store v
    | "primitive?" => is_primitive store v
    | "abs" => unary_arith store JsNumber.absolute v
    | "void" => void store v
    | "floor" => unary_arith store JsNumber.floor v
    | "prim->str" => prim_to_str store v
    | "prim->num" => prim_to_num store v
    | "prim->bool" => prim_to_bool store v
    | "!" => nnot store v
    | "numstr->num" => numstr_to_num store v
    | _ => (store, Context.Fail Values.value_loc ("Unary operator " ++ op ++ " not implemented."))
    end
  )
.

(****** Binary operators ******)

Parameter _number_eq_bool : number -> number -> bool.

Definition stx_eq store v1 v2 :=
  match (v1, v2) with
  | (String s1, String s2) => Context.add_value_return store (if (decide(s1 = s2)) then True else False)
  | (Null, Null) => Context.add_value_return store True
  | (Undefined, Undefined) => Context.add_value_return store True
  | (True, True) => Context.add_value_return store True
  | (False, False) => Context.add_value_return store True
  | (Number n1, Number n2) =>
    let (store, loc) := Store.add_bool store (_number_eq_bool n1 n2) in
    (store, Return Values.value_loc loc)
  | (Object ptr1, Object ptr2) => Context.add_value_return store (if (beq_nat ptr1 ptr2) then True else False)
  | (Closure id1 _ _ _, Closure id2 _ _ _) => Context.add_value_return store (if (beq_nat id1 id2) then True else False)
  | _ => Context.add_value_return store False
  (*| _ => Context.add_value_return store (if (beq_nat v1_loc v2_loc) then True else False)*)
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
  | _ => (store, Fail Values.value_loc "hasProperty expected a string.")
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
  | _ => (store, Fail Values.value_loc "hasOwnProperty expected an object and a string.")
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
        (store, Return Values.value_loc loc)
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
        (store, Return Values.value_loc loc)
      | None => Context.add_value_return store Undefined
      end
    )
  | _ => (store, Fail Values.value_loc "hasOwnProperty expected an object and a string.")
  end
.

Definition string_plus store v1 v2 : (Store.store * Context.result Values.value_loc) :=
  match (v1, v2) with
  | (String s1, String s2) => Context.add_value_return store (String (s1++s2))
  | _ => (store, Fail Values.value_loc "Only strings can be concatenated.")
  end
.

Parameter _nat_of_float : number -> nat.

Definition char_at store v1 v2 :=
  match (v1, v2) with
  | (Values.String s, Number n) =>
      match (String.get (_nat_of_float n) s) with
      | Some char => add_value_return store (Values.String (String.String char String.EmptyString))
      | None => (store, Fail Values.value_loc "char_at called with index larger than length.")
      end
  | _ => (store, Fail Values.value_loc "char_at called with wrong argument types.")
  end
.

Definition is_accessor runs store v1_loc v2 :=
  match v2 with
  | String s =>
    let (store, res) := Context.runs_type_get_property runs store (v1_loc, s) in
    if_return store res (fun ret =>
      match ret with
      | Some (attributes_data_of _) => Context.add_value_return store False
      | Some (attributes_accessor_of _) => Context.add_value_return store True
      | None => (store, Fail Values.value_loc "isAccessor topped out.")
      end
    )
  | _ => (store, Fail Values.value_loc "isAccessor expected an object and a string.")
  end
.

Parameter _same_value : value -> value -> bool.

Definition same_value store v1 v2 :=
  return_bool store (_same_value v1 v2)
.

Definition arith store (op : number -> number -> number) (v1 v2 : Values.value) : (Store.store * Context.result Values.value_loc) :=
  match (v1, v2) with
  | (Number n1, Number n2) => Context.add_value_return store (Number (op n1 n2))
  | _ => (store, Fail Values.value_loc "Arithmetic with non-numbers.")
  end
.

Definition cmp store undef_left undef_both undef_right (op : number -> number -> bool) (v1 v2 : Values.value) : (Store.store * Context.result Values.value_loc) :=
  match (v1, v2) with
  | (Number n1, Number n2) => Context.add_value_return store (if (op n1 n2) then True else False)
  | (Undefined, Number _) => Context.add_value_return store undef_left
  | (Undefined, Undefined) => Context.add_value_return store undef_both
  | (Number _, Undefined) => Context.add_value_return store undef_right
  | _ => (store, Fail Values.value_loc "Comparison/order of non-numbers.")
  end
.

Parameter le_bool : number -> number -> bool.
Parameter gt_bool : number -> number -> bool.
Parameter ge_bool : number -> number -> bool.


Definition binary (op : string) runs store v1_loc v2_loc : (Store.store * (Context.result Values.value_loc)) :=
  assert_deref store v1_loc (fun v1 =>
    assert_deref store v2_loc (fun v2 =>
      match op with
      | "+" => arith store JsNumber.add v1 v2
      | "-" => arith store JsNumber.sub v1 v2
      | "*" => arith store JsNumber.mult v1 v2
      | "/" => arith store JsNumber.div v1 v2
      | "%" => arith store JsNumber.fmod v1 v2
      | "<" => cmp store True False False JsNumber.lt_bool v1 v2
      | "<=" => cmp store True True False le_bool v1 v2
      | ">" => cmp store False False True gt_bool v1 v2
      | ">=" => cmp store False True True ge_bool v1 v2
      | "stx=" => stx_eq store v1 v2
      | "sameValue" => same_value store v1 v2
      | "hasProperty" => has_property runs store v1_loc v2
      | "hasOwnProperty" => has_own_property store v1 v2
      | "string+" => string_plus store v1 v2
      | "char-at" => char_at store v1 v2
      | "isAccessor" => is_accessor runs store v1_loc v2
      | "__prop->obj" => prop_to_obj store v1 v2 (* For debugging purposes *)
      | _ => (store, Context.Fail Values.value_loc ("Binary operator " ++ op ++ " not implemented."))
      end
  ))
.
