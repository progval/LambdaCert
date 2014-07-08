Require Import String.
Require Import Values.
Require Import Store.
Require Import Context.

Implicit Type runs : Context.runs_type.
Implicit Type store : Store.store.

(*
* The monadic constructors, which mostly take a store, some
* data, and a continuation; performing a test on the data; and calling
* the continuation in one case, and doing something else in other cases
* (either calling the continuation with a default, or returning a default,
* or returning the data verbatim).
*)

(* Evaluate an expression, and calls the continuation with
* the new store and the Context.result of the evaluation. *)
Definition eval_cont {value_type : Type} runs store (e : Syntax.expression) (cont : Store.store -> (@Context.result Values.value_loc) -> (Store.store * (@Context.result value_type))) : (Store.store * (@Context.result value_type)) :=
  match ((Context.runs_type_eval runs) store e) with (store, res) =>
    cont store res
  end
.
(* Alias for calling eval_cont with an empty continuation *)
Definition eval_cont_terminate runs store (e : Syntax.expression) : (Store.store * Context.result) :=
  eval_cont runs store e (fun store res => (store, res))
.

(* Calls the continuation if the variable is a value.
* Returns the variable and the store verbatim otherwise. *)
Definition if_return {value_type : Type} {value_type_2 : Type} store (var : @Context.result value_type) (cont : value_type -> (Store.store * (@Context.result value_type_2))) : (Store.store * (@Context.result value_type_2)) :=
  match var with
  | Return v => cont v
  | Exception exc => (store, Exception exc)
  | Fail f => (store, Fail f)
  end
.

(* Evaluates an expression, and calls the continuation if
* the evaluation returned a value.
* Returns the store and the variable verbatim otherwise. *)
Definition if_eval_return {value_type : Type} runs store (e : Syntax.expression) (cont : Store.store -> Values.value_loc -> (Store.store * (@Context.result value_type))) : (Store.store * (@Context.result value_type)) :=
  eval_cont runs store e (fun store res => match res with
  | Return v => cont store v
  | Exception exc => (store, Exception exc)
  | Fail f => (store, Fail f)
  end
  )
.

(* Evaluates an expression with if it is Some, and calls the continuation
* if the evaluation returned value. Calls the continuation with the default
* value if the expression is None. *)
Definition if_some_eval_else_default {value_type : Type} runs store (oe : option Syntax.expression) (default : Values.value_loc) (cont : Store.store -> Values.value_loc -> (Store.store * (@Context.result value_type))) : (Store.store * (@Context.result value_type)) :=
  match oe with
  | Some e => if_eval_return runs store e cont
  | None => cont store default
  end
.

(* Same as if_some_and_eval_value, but returns an option as the Context.result, and
* None is used as the default value passed to the continuation. *)
Definition if_some_eval_return_else_none {value_type : Type} runs store (oe : option Syntax.expression) (cont : Store.store -> option Values.value_loc -> (Store.store * (@Context.result value_type))) : (Store.store * (@Context.result value_type)) :=
  match oe with
  | Some e => if_eval_return runs store e (fun ctx res => cont ctx (Some res))
  | None => cont store None
  end
.

(* Calls the continuation with the referenced value. Fails if the reference
* points to a non-existing object (never actually happens). *)
Definition assert_deref {value_type : Type} store (loc : Values.value_loc) (cont : Values.value -> (Store.store * (@Context.result value_type))) : (Store.store * (@Context.result value_type)) :=
  match (Store.get_value store loc) with
  | Some val => cont val
  | None => (store, Fail "Location of non-existing value.")
  end
.

(* Calls the continuation if the value is a location to a value (always!), and passes the value to the continuation.
* Fails otherwise. *)
Definition assert_get {value_type : Type} store (loc : Values.value_loc) (cont : Values.value -> (Store.store * (@Context.result value_type))) : (Store.store * (@Context.result value_type)) :=
  match (Store.get_value store loc) with
  | Some val => cont val
  | None => (store, Fail "Location of non-existing value.")
  end
.

(* Calls the continuation if the value is an object pointer, and passes the pointer to the continuation.
* Fails otherwise. *)
Definition assert_get_object_ptr {value_type : Type} store (loc : Values.value_loc) (cont : Values.object_ptr -> (Store.store * (@Context.result value_type))) : (Store.store * (@Context.result value_type)) :=
  match (Store.get_value store loc) with
  | Some (Values.Object ptr) => cont ptr
  | Some _ => (store, Fail "Expected an object pointer.")
  | None => (store, Fail "Location of non-existing value.")
  end
.

Definition assert_get_object_from_ptr {value_type : Type} store (ptr : Values.object_ptr) (cont : Values.object -> (Store.store * (@Context.result value_type))) : (Store.store * (@Context.result value_type)) :=
  match (Store.get_object store ptr) with
  | Some obj => cont obj
  | None => (store, Fail "Pointer to a non-existing object.")
  end
.

(* Calls the continuation if the value is an object pointer, and passes the object to the continuation *)
Definition assert_get_object {value_type : Type} store (loc : Values.value_loc) (cont : Values.object -> (Store.store * (@Context.result value_type))) : (Store.store * (@Context.result value_type)) :=
  assert_get_object_ptr store loc (fun ptr =>
    assert_get_object_from_ptr store ptr cont
  )
.

(* Calls the continuation if the value is a string.
* Fails otherwise. *)
Definition assert_get_string {value_type : Type} store (loc : Values.value_loc) (cont : string -> (Store.store * (@Context.result value_type))) : (Store.store * (@Context.result value_type)) :=
  match (Store.get_value store loc) with
  | Some (Values.String s) => cont s
  | Some _ => (store, Fail "Expected String but did not get one.")
  | None => (store, Fail "Location of non-existing value.")
  end
.

(* Calls the continuation if the value is a boolean.
* Fails otherwise. *)
Definition assert_get_bool_3 {value_type : Type} {X : Type} store (loc : Values.value_loc) (default : X) (cont : bool -> (Store.store * X * (@Context.result value_type))) : (Store.store * X * (@Context.result value_type)) :=
  match (Store.get_value store loc) with
  | Some Values.True => cont true
  | Some Values.False => cont false
  | Some _ => (store, default, Fail "Expected True or False but got none of them.")
  | None => (store, default, Fail "Location of non-existing value.")
  end
.

