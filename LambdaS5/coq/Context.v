Require Import String.
Require Import Values.

(* Utilities for the Interwriter. Defines the Context.result and context
* structures, and helper functions to manipulate the store embedded in the
* context structure.
*)

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

(* The interpreter environment (“context”) used to evaluate an expression.
* We mostly use EvaluationContext, which contains a reference to `runs`
* (defined at the bottom of this file) applied to an integer (the strictly
* decreasing argument, needed by Coq; and a store.
* BottomEvaluationContext is used when the integer reached 0, and we have
* to stop the execution (hopefully never actually happens).
* We add a store to BottomEvaluationContext because it makes writing some
* functions easier (no need for returning an option).
*)
Inductive context : Type :=
  | BottomEvaluationContext : Values.store -> context
  | EvaluationContext : (Values.store -> Syntax.expression -> (context * (@result Values.value_loc))) -> Values.store -> context
.

Implicit Type ctx : Context.context.

(* Unpacks the store from the context, calls the predicate with the store,
* gets the store returned by the predicate, and creates a new context with
* this store. *)
Definition update_store_simple ctx (pred : Values.store -> Values.store) : context :=
  match ctx with
  | BottomEvaluationContext store =>
      BottomEvaluationContext (pred store)
  | EvaluationContext runs store =>
      EvaluationContext runs (pred store)
  end
.

(* Same as update_store_simple, but allows a return value. *)
Definition update_store {return_type : Type} ctx (pred : Values.store -> (Values.store * return_type)) : (context * return_type) :=
  match ctx with
  | BottomEvaluationContext store =>
      let (store, ret) := pred store in
      (BottomEvaluationContext store, ret)
  | EvaluationContext runs store =>
      let (store, ret) := pred store in
      (EvaluationContext runs store, ret)
  end
.

(* Unpacks the store from the context, calls the predicate with the store,
* and returns the return value of the predicate. *)
Definition read_store {return_type : Type} ctx (pred : Values.store -> return_type) : return_type :=
  match ctx with
  | BottomEvaluationContext store
  | EvaluationContext _ store =>
    pred store
  end
.

(* Generates a new locations, assigns the value to this location in the
* context's store, and returns the new context and this location.
*)
Definition add_value ctx (val : Values.value) : (Context.context * Values.value_loc) :=
  update_store ctx (fun st => Values.add_value_to_store st val)
.
(* Same as add_value, but wraps the loc in a Return. *)
Definition add_value_return ctx val :=
  let (ctx, loc) := add_value ctx val in
  (ctx, Return loc)
.

(* Same as add_value, but also adds the object on the object heap *)
Definition add_object ctx (obj : Values.object) : (Context.context * Values.value_loc) :=
  update_store ctx (fun st => Values.add_object_to_store st obj)
.
(* Same as add_object, but wraps the loc in a return *)
Definition add_object_return ctx obj :=
  let (ctx, loc) := add_object ctx obj in
  (ctx, Return loc)
.

Definition add_named_value ctx (name : Values.id) (val : Values.value) : (Context.context * Values.value_loc) :=
  update_store ctx (fun st => Values.add_named_value_to_store st name val)
.

Definition add_value_at_location ctx (loc : Values.value_loc) (val : Values.value) : Context.context :=
  update_store_simple ctx (fun store => Values.add_value_at_location store loc val)
.

(* Same as add_value, but works for options. *)
Definition add_option_value ctx (oval : option Values.value) : (Context.context * option Values.value_loc) :=
  match oval with
  | Some val => let (ctx, loc) := add_value ctx val in (ctx, Some loc)
  | None => (ctx, None)
  end
.

(* Returns a new context, which is the old context where the store
* has been replaced by a new one using the predicate. *)
Definition replace_store {return_value : Type} ctx (pred : store -> (store * return_value)) : (Context.context * return_value) :=
  match ctx with
  | BottomEvaluationContext st =>
    let (new_st, ret) := (pred st) in (BottomEvaluationContext new_st, ret)
  | EvaluationContext runs st =>
    let (new_st, ret) := (pred st) in (EvaluationContext runs new_st, ret)
  end
.

(* Shortcut for instanciating and throwing an exception of the given name. *)
Definition raise_exception ctx (name : string) : (Context.context * (@Context.result Values.value_loc)) :=
  let (ctx, proto_loc) := (add_value ctx Values.Undefined) in
    replace_store ctx (fun st =>
    match (Values.add_object_to_store st (Values.object_intro proto_loc name true None Heap.empty None)) with
    | (new_st, loc) => (new_st, Exception loc)
    end
  )
.

(* Fetches the location in the context's store that has this name, if any. *)
Definition get_loc_of_name ctx (name : Values.id) : option Values.value_loc :=
  read_store ctx (fun st => Values.get_loc_from_store st name)
.

(* Fetches the value in the context's store that has this location, if any.
* Note: Should never return None, unless the code calling this function is
* inconsistent (asks for a location that does not exist…). *)
Definition get_value_of_loc ctx (loc : Values.value_loc) : option Values.value :=
  read_store ctx (fun st => Values.get_value_from_store st loc)
.

(* Returns the value associated to a variable name (aka. id) in the current
* context. *)
Definition get_value_of_name ctx (name : Values.id) : option Values.value :=
  read_store ctx (fun st =>
    match (get_loc_of_name ctx name) with
    | Some loc => Values.get_value_from_store st loc
    | None => None (* This should never happen (see the note of get_value_of_loc) *)
    end
  )
.


Definition get_object_of_ptr ctx (ptr : Values.object_ptr) : option Values.object :=
  read_store ctx (fun st => Values.get_object_from_store st ptr)
.

(* Unpacks a context to get an object, calls the predicate with this
* object, and updates the object to the returned value. *)
Definition update_object {return_type : Type} ctx (ptr : Values.object_ptr) (pred : Values.object -> (Values.object * (@result return_type))) : (context * (@result return_type)) :=
  update_store ctx (fun st =>
    match (Context.get_object_of_ptr ctx ptr) with
    | Some obj =>
        let (new_obj, ret) := pred obj in
        (Values.update_object st ptr new_obj, ret)
    | None => (st, Fail "Pointer to a non-existing object.")
    end
  )
.
