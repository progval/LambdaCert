Require Import Utils.
Require Import String.
Require Import Values.
Require Import Store.

(* Utilities for the Interpreter. *)

(* Used for passing data through continuations/return values.
* It is mostly used for returning a Javascript value, either as
* Return or Exception, but sometimes we want to return another kind
* of result, which is the reason why this type is parametered by
* value_type. *)
Inductive result (value_type : Type) : Type :=
  | Return : value_type -> result value_type (* value *)
  | Exception : Values.value_loc -> result value_type (* exception message *)
  | Break : string -> Values.value_loc -> result value_type (* label, expression *)
  | Fail : string -> result value_type (* reason *)
.

Definition runner_type (runner_arg : Type) (runner_ret : Type) :=
  Store.store -> runner_arg -> (Store.store * (@result runner_ret))
.
Record runs_type : Type := runs_type_intro {
    runs_type_nat_fuel : nat;
    runs_type_eval : runner_type Syntax.expression Values.value_loc;
    runs_type_get_closure : runner_type Values.value_loc Values.value_loc;
    runs_type_get_property : runner_type (Values.value_loc * Values.prop_name) (option Values.attributes)
}.

(* Shortcut for instanciating and throwing an exception of the given name. *)
Definition raise_exception store (name : string) : (Store.store * (Context.result Values.value_loc)) :=
  let (store, proto_loc) := (Store.add_value store Values.Undefined) in
  match (Store.add_object store (Values.object_intro proto_loc name true None Heap.empty None)) with
  | (new_st, loc) => (new_st, Exception Values.value_loc loc)
  end
.

(* Unpacks a store to get an object, calls the predicate with this
* object, and updates the object to the returned value. *)
Definition update_object {return_type : Type} store (ptr : Values.object_ptr) (pred : Values.object -> (Store.store * Values.object * (@result return_type))) : (Store.store * (@result return_type)) :=
  match (Store.get_object store ptr) with
  | Some obj =>
      match (pred obj) with (store, new_obj, ret) =>
        (Store.update_object store ptr new_obj, ret)
      end
  | None => (store, Fail return_type "Pointer to a non-existing object.")
  end
.


(* Fetches the object pointed by the ptr, gets the property associated
* with the name and passes it to the predicate (as an option).
* If the predicate returns None as the now property, the property is
* destroyed; otherwise it is updated/created with the one returned by
* the predicate. *)
Definition update_object_property {return_type : Type} store (ptr : Values.object_ptr) (name : Values.prop_name) (pred : option Values.attributes -> (Store.store * option Values.attributes * (@result return_type))) : (Store.store * (@result return_type)) :=
  update_object store ptr (fun obj =>
    match obj with (Values.object_intro prot cl ext prim props code) =>
      match (pred (Values.get_object_property obj name)) with
      | (store, Some prop, res) =>
          let new_props := (Heap.write props name prop) in
          (store, Values.object_intro prot cl ext prim new_props code, res)
      | (store, None, res) =>
          let new_props := props in
          (* TODO: Remove property *)
          (store, Values.object_intro prot cl ext prim new_props code, res)
      end
    end
  )
.


Definition add_value_return store v :=
  let (store, loc) := Store.add_value store v in
  (store, Return Values.value_loc loc)
.

Definition return_bool store (b : bool) :=
  add_value_return store (if b then Values.True else Values.False)
.
