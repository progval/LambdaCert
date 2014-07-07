Require Import String.
Require Import Values.
Require Import Store.

(* Utilities for the Interpreter. *)

(* Used for passing data through continuations/return values.
* It is mostly used for returning a Javascript value, either as
* Return or Exception, but sometimes we want to return another kind
* of result, which is the reason why this type is parametered by
* value_type. *)
Inductive result {value_type : Type} : Type :=
  | Return : value_type -> result (* value *)
  | Exception : Values.value_loc -> result (* exception message *)
  | Fail : string -> result (* reason *)
.

Definition runner_type (runner_arg : Type) :=
  Store.store -> runner_arg -> (Store.store * (@result Values.value_loc))
.
Record runs_type : Type := runs_type_intro {
    runs_type_eval : runner_type Syntax.expression;
    runs_type_get_closure : runner_type Values.value_loc
}.

(* Shortcut for instanciating and throwing an exception of the given name. *)
Definition raise_exception store (name : string) : (Store.store * (@Context.result Values.value_loc)) :=
  let (store, proto_loc) := (Store.add_value store Values.Undefined) in
  match (Store.add_object store (Values.object_intro proto_loc name true None Heap.empty None)) with
  | (new_st, loc) => (new_st, Exception loc)
  end
.


(* Unpacks a store to get an object, calls the predicate with this
* object, and updates the object to the returned value. *)
Definition update_object {return_type : Type} store (ptr : Values.object_ptr) (pred : Values.object -> (Values.object * (@result return_type))) : (Store.store * (@result return_type)) :=
  match (Store.get_object store ptr) with
  | Some obj =>
      let (new_obj, ret) := pred obj in
      (Store.update_object store ptr new_obj, ret)
  | None => (store, Fail "Pointer to a non-existing object.")
  end
.
