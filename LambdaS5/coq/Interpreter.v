Require Import List.
Require Import Coq.Strings.String.
Require Import Syntax.
Require Import Values.
Require Import LibHeap.
Require Import LibStream.
Open Scope list_scope.
Open Scope string_scope.

(* Basic idea of how this file works:
* There are four sections in this file:
* * The utilities, which are the result and context structures,
*   and helper functions to manipulate the store embedded in the
*   context structure.
* * The monadic constructors, which mostly take a context, some
*   data, and a continuation; performing a test on the data; and calling
*   the continuation in one case, and doing something else in other cases
*   (either calling the continuation with a default, or returning a default,
*   or returning the data verbatim).
* * The evaluators, which actually define the semantics of LambdaJS.
*   There is one evaluator per node constructor (defined in coq/Syntax.v),
*   with eventually helper functions.
* * The “looping” functions, which call the evaluators. The “runs”
*   function calls eval at every iteration, with a reference to itself
*   applied to a strictly decreasing integer, to make Coq accept the
*   code.
*)


(******* Utilities *******)

(* Used for passing data through continuations/return values.
* It is mostly used for returning a Javascript value, either as
* Success or Exception, but sometimes we want to return another kind
* of result, which is the reason why this type is parametered by
* value_type. *)
Inductive result {value_type : Type} : Type :=
  | Success : value_type -> result (* value *)
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
Inductive evaluation_context : Type :=
  | BottomEvaluationContext : Values.store -> evaluation_context
  | EvaluationContext : (Values.store -> Syntax.expression -> (evaluation_context * (@result Values.value_loc))) -> Values.store -> evaluation_context
.

(* Unpacks the store from the context, calls the predicate with the store,
* gets the store returned by the predicate, and creates a new context with
* this store. *)
Definition update_store {return_type : Type} (context : evaluation_context) (pred : Values.store -> (Values.store * return_type)) : (evaluation_context * return_type) :=
  match context with
  | BottomEvaluationContext store =>
      let (store, ret) := pred store in
      (BottomEvaluationContext store, ret)
  | EvaluationContext runs store =>
      let (store, ret) := pred store in
      (EvaluationContext runs store, ret)
  end
.

(* Generates a new locations, assigns the value to this location in the
* context's store, and returns the new context and this location.
*)
Definition add_value_to_context (context : evaluation_context) (val : Values.value) : (evaluation_context * Values.value_loc) :=
  update_store context (fun store => Values.add_value_to_store store val)
.
(* Same as add_value_to_context, but wraps the loc in a Success. *)
Definition add_value_to_context_success context val :=
  let (context, loc) := add_value_to_context context val in
  (context, Success loc)
.

Definition add_named_value_to_context (context : evaluation_context) (name : Values.id) (val : Values.value) : (evaluation_context * Values.value_loc) :=
  update_store context (fun store => Values.add_named_value_to_store store name val)
.

Definition add_value_to_context_at_location (context : evaluation_context) (loc : Values.value_loc) (val : Values.value) : evaluation_context :=
  let (context, _) := update_store context (fun store => (Values.add_value_at_location store loc val, 0)) in (* We have to return something... *)
  context
.

(* Same as add_value_to_context, but works for options. *)
Definition add_option_value_to_context (context : evaluation_context) (oval : option Values.value) : (evaluation_context * option Values.value_loc) :=
  match oval with
  | Some val => let (context, loc) := add_value_to_context context val in (context, Some loc)
  | None => (context, None)
  end
.

(* Returns a new context, which is the old context where the store
* has been replaced by a new one using the predicate. *)
Definition replace_store {return_value : Type} (context : evaluation_context) (pred : store -> (store * return_value)) : (evaluation_context * return_value) :=
  match context with
  | BottomEvaluationContext st =>
    let (new_st, ret) := (pred st) in (BottomEvaluationContext new_st, ret)
  | EvaluationContext runs st =>
    let (new_st, ret) := (pred st) in (EvaluationContext runs new_st, ret)
  end
.

(* Shortcut for instanciating and throwing an exception of the given name. *)
Definition raise_exception (context : evaluation_context) (name : string) : (evaluation_context * (@result Values.value_loc)) :=
  replace_store context (fun st =>
    let (context, proto_loc) := (add_value_to_context context Values.Undefined) in
    match (Values.add_value_to_store st (Values.Object (Values.object_intro proto_loc name true None Heap.empty None))) with
    | (new_st, loc) => (new_st, Exception loc)
    end
  )
.

(* Fetches the location in the context's store that has this name, if any. *)
Definition get_loc_of_name (context : evaluation_context) (name : Values.id) : option Values.value_loc :=
  match context with
  | BottomEvaluationContext store
  | EvaluationContext _ store =>
      Values.get_loc_from_store store name
  end
.

(* Fetches the value in the context's store that has this location, if any.
* Note: Should never return None, unless the code calling this function is
* inconsistent (asks for a location that does not exist…). *)
Definition get_value_of_loc (context : evaluation_context) (loc : Values.value_loc) : option Values.value :=
  match context with
  | BottomEvaluationContext store
  | EvaluationContext _ store =>
      Values.get_value_from_store store loc
  end
.

(* Returns the value associated to a variable name (aka. id) in the current
* context. *)
Definition get_value_of_name (context : evaluation_context) (name : Values.id) : option Values.value :=
  match context with
  | BottomEvaluationContext store
  | EvaluationContext _ store =>
      match (get_loc_of_name context name) with
      | Some loc => Values.get_value_from_store store loc
      | None => None (* This should never happen (see the note of get_value_of_loc) *)
      end
  end
.

(* Evaluate an expression in a context, and calls the continuation with
* the new context and the result of the evaluation. *)
Definition eval_cont {value_type : Type} (context : evaluation_context) (e : Syntax.expression) (cont : evaluation_context -> (@result Values.value_loc) -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match context with
  | BottomEvaluationContext store => (BottomEvaluationContext store, Fail "bottom")
  | EvaluationContext runs store =>
    match (runs store e) with (context, result) =>
      cont context result
    end
  end
.
(* Alias for calling eval_cont with an empty continuation *)
Definition eval_cont_terminate (context : evaluation_context) (e : Syntax.expression) : (evaluation_context * result) :=
  eval_cont context e (fun context result => (context, result))
.

(* Unpacks a context to get the store, replaced the value at the given
* location by a new value, and returns the new context. *)
Definition replace_value_in_store (context : evaluation_context) (loc : Values.value_loc) (val : Values.value) : evaluation_context :=
  match context with
  | BottomEvaluationContext store =>
    BottomEvaluationContext (Values.add_value_at_location store loc val)
  | EvaluationContext runs store =>
    EvaluationContext runs (Values.add_value_at_location store loc val)
  end
.


(********* Monadic constructors ********)

(* Calls the continuation if the variable is a value.
* Returns the variable and the context verbatim otherwise. *)
Definition if_success {value_type : Type} {value_type_2 : Type} (context : evaluation_context) (var : @result value_type) (cont : evaluation_context -> value_type -> (evaluation_context * (@result value_type_2))) : (evaluation_context * (@result value_type_2)) :=
  match var with
  | Success v => cont context v
  | Exception exc => (context, Exception exc)
  | Fail f => (context, Fail f)
  end
.

(* Evaluates an expression in a context, and calls the continuation if
* the evaluation returned a value.
* Returns the context and the variable verbatim otherwise. *)
Definition if_eval_value {value_type : Type} (context : evaluation_context) (e : Syntax.expression) (cont : evaluation_context -> Values.value_loc -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  eval_cont context e (fun context res => match res with
  | Success v => cont context v
  | Exception exc => (context, Exception exc)
  | Fail f => (context, Fail f)
  end
  )
.

(* Evaluates an expression with if it is Some, and calls the continuation
* if the evaluation returned value. Calls the continuation with the default
* value if the expression is None. *)
Definition if_some_eval_else_default {value_type : Type} (context : evaluation_context) (oe : option Syntax.expression) (default : Values.value_loc) (cont : evaluation_context -> Values.value_loc -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match oe with
  | Some e => if_eval_value context e cont
  | None => cont context default 
  end
.

(* Same as if_some_and_eval_value, but returns an option as the result, and
* None is used as the default value passed to the continuation. *)
Definition if_eval_value_option_default {value_type : Type} (context : evaluation_context) (oe : option Syntax.expression) (cont : evaluation_context -> option Values.value_loc -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match oe with
  | Some e => if_eval_value context e (fun ctx res => cont ctx (Some res))
  | None => cont context None
  end
.

(* Calls the continuation with the referenced value. Fails if the reference
* points to a non-existing object (never actually happens). *)
Definition assert_deref {value_type : Type} (context : evaluation_context) (loc : Values.value_loc) (cont : evaluation_context -> Values.value -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match (get_value_of_loc context loc) with
  | Some val => cont context val
  | None => (context, Fail "Location of non-existing value.")
  end
.


(* Calls the continuation if the value is an object location, and passes the object to the continuation.
* Fails otherwise. *)
Definition assert_get_object {value_type : Type} (context : evaluation_context) (loc : Values.value_loc) (cont : evaluation_context -> Values.object -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match (get_value_of_loc context loc) with
  | Some (Object obj) => cont context obj
  | Some _ => (context, Fail "Expected an object.")
  | None => (context, Fail "Location of non-existing value.")
  end
.

(* Calls the continuation if the value is a string.
* Fails otherwise. *)
Definition assert_get_string {value_type : Type} (context : evaluation_context) (loc : Values.value_loc) (cont : evaluation_context -> string -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match (get_value_of_loc context loc) with
  | Some (Values.String s) => cont context s
  | Some _ => (context, Fail "Expected String but did not get one.")
  | None => (context, Fail "Location of non-existing value.")
  end
.


(********* Evaluators ********)

(* a lonely identifier *)
Definition eval_id (context : evaluation_context) (name : string) : (evaluation_context * result) :=
  match (get_loc_of_name context name) with
  | Some v => (context, Success v)
  | None => raise_exception context "ReferenceError"
  end
.


(* if e_cond e_true else e_false *)
Definition eval_if (context : evaluation_context) (e_cond e_true e_false : Syntax.expression) : (evaluation_context * result) :=
  if_eval_value context e_cond (fun context v =>
  match (get_value_of_loc context v) with
  | Some Values.True => eval_cont_terminate context e_true
  | Some Values.False => eval_cont_terminate context e_false
  | Some _ => (context, Fail "if with neither true or false")
  | None => (context, Fail "Location of non-existing value.")
  end
  )
.

(* e1 ; e2 *)
Definition eval_seq (context : evaluation_context) (e1 e2 : Syntax.expression) : (evaluation_context * result) :=
  if_eval_value context e1 (fun context v => eval_cont_terminate context e2 )
.


(* A tail-recursive helper for eval_object_properties, that constructs
* the list of properties. *)
Fixpoint eval_object_properties_aux (context : evaluation_context) (l : list (string * Syntax.property)) (acc : Values.object_properties) : (evaluation_context * (@result Values.object_properties)) :=
  match l with
  | nil => (context, Success acc)
  | (name, Syntax.DataProperty (Syntax.Data value_expr writable) enumerable configurable) :: tail =>
    (* The order of the evaluation follows the original implementation. *)
    if_eval_value context value_expr (fun context value_loc =>
      eval_object_properties_aux context tail (Heap.write acc name (
        Values.attributes_data_of {|
            Values.attributes_data_value := value_loc;
            Values.attributes_data_writable := writable;
            Values.attributes_data_enumerable := enumerable;
            Values.attributes_data_configurable := configurable |}
      )))
  | (name, Syntax.AccessorProperty (Syntax.Accessor getter_expr setter_expr) enumerable configurable) :: tail =>
    (* The order of the evaluation follows the original implementation. *)
    if_eval_value context getter_expr (fun context getter_loc =>
      if_eval_value context setter_expr (fun context setter_loc =>
        eval_object_properties_aux context tail (Heap.write acc name (
           Values.attributes_accessor_of {|
              Values.attributes_accessor_get := getter_loc;
              Values.attributes_accessor_set := setter_loc;
              Values.attributes_accessor_enumerable := enumerable;
              Values.attributes_accessor_configurable := configurable |}
    ))))
  end
.
(* Reads a list of syntax trees of properties and converts it to a heap
* bindable to an object. *)
Definition eval_object_properties (context : evaluation_context) (l : list (string * Syntax.property)) : (evaluation_context * (@result Values.object_properties)) :=
  eval_object_properties_aux context l Heap.empty
.

(* { [ attrs ] props } *)
Definition eval_object_decl (context : evaluation_context) (attrs : Syntax.object_attributes) (l : list (string * Syntax.property)) : (evaluation_context * result) :=

  match attrs with
  | Syntax.ObjectAttributes primval_expr code_expr prototype_expr class extensible =>
    (* Following the order in the original implementation: *)
    if_eval_value_option_default context primval_expr (fun context primval_loc =>
      let (context, proto_default) := add_value_to_context context Values.Undefined in
      if_some_eval_else_default context prototype_expr proto_default (fun context prototype_loc =>
        if_eval_value_option_default context code_expr (fun context code =>
          let (context, props) := (eval_object_properties context l)
          in if_success context props (fun context props =>
            add_value_to_context_success context (Values.Object {|
                Values.object_proto := prototype_loc;
                Values.object_class := class;
                Values.object_extensible := extensible;
                Values.object_prim_value := primval_loc;
                Values.object_properties_ := props;
                Values.object_code := code_expr |})
          ))))
  end
.

(* left[right, attrs] *)
Definition eval_get_field (context : evaluation_context) (left_expr right_expr attrs_expr : Syntax.expression) : (evaluation_context * result) :=
  if_eval_value context left_expr (fun context left =>
    if_eval_value context right_expr (fun context right =>
      if_eval_value context attrs_expr (fun context attrs =>
        assert_get_object context left (fun context object =>
          assert_get_string context right (fun context name =>
            match (Values.get_object_property object name) with
            | Some (attributes_data_of data) => (context, Success (Values.attributes_data_value data))
            | Some (attributes_accessor_of accessor) => (BottomEvaluationContext Values.create_store, Fail "getter not implemented.")
            | None => add_value_to_context_success context Values.Undefined
            end)))))
.

(* left[right, attrs] = new_val *)
Definition eval_set_field (context : evaluation_context) (left_expr right_expr new_val_expr attrs_expr : Syntax.expression) : (evaluation_context * result) :=
  if_eval_value context left_expr (fun context left =>
    if_eval_value context right_expr (fun context right =>
      if_eval_value context new_val_expr (fun context new_val =>
        assert_get_object context left (fun context object =>
          if_eval_value context attrs_expr (fun context attrs =>
            assert_get_string context right (fun context name =>
              match (Values.get_object_property object name) with
              | Some (attributes_data_of (Values.attributes_data_intro _ w e c)) =>
                let attrs := Values.attributes_data_of (attributes_data_intro new_val w e c) in
                let new_obj := Values.Object (Values.set_object_property object name attrs) in
                let context := add_value_to_context_at_location context left new_obj in
                (context, Success new_val)
              | Some (attributes_accessor_of accessor) => (BottomEvaluationContext Values.create_store, Fail "setter not implemented.")
              | None => add_value_to_context_success context Values.Undefined
              end))))))
.


(* let (id = expr) body *)
Definition eval_let (context : evaluation_context) (id : string) (value_expr body_expr : Syntax.expression) : (evaluation_context * result) :=
  if_eval_value context value_expr (fun context value_loc =>
    assert_deref context value_loc (fun context value =>
      let (new_context, loc) := add_named_value_to_context context id value in
        eval_cont_terminate new_context body_expr
  ))
.



(******** Closing the loop *******)

(* Main evaluator *)
Definition eval (context : evaluation_context) (e : Syntax.expression) : (evaluation_context * (@result Values.value_loc)) :=
  let return_value := (fun v => add_value_to_context_success context v) in
  match e with
  | Syntax.Undefined => return_value Values.Undefined
  | Syntax.String s => return_value (Values.String s)
  | Syntax.Number n => return_value (Values.Number n)
  | Syntax.True => return_value Values.True
  | Syntax.False => return_value Values.False
  | Syntax.Id s => eval_id context s
  | Syntax.If e_cond e_true e_false => eval_if context e_cond e_true e_false
  | Syntax.Seq e1 e2 => eval_seq context e1 e2
  | Syntax.ObjectDecl attrs l => eval_object_decl context attrs l
  | Syntax.GetField left_ right_ attributes => eval_get_field context left_ right_ attributes
  | Syntax.SetField left_ right_ new_val attributes => eval_set_field context left_ right_ new_val attributes
  | Syntax.Let id value body => eval_let context id value body
  | _ => (context, Fail "not implemented")
  end
.

(* Evaluates expression and ensure there is a decreasing argument. *)
Fixpoint runs (max_steps : nat) (store : Values.store) (e : Syntax.expression) : (evaluation_context * result) :=
  match (max_steps) with
  | 0 => (BottomEvaluationContext store, Fail "Coq is not Turing-complete")
  | S max_steps' => eval (EvaluationContext (runs max_steps')  store) e
  end
.

(* Alias for calling runs with only an expression and getting only a result *)
Definition runs_call (e : Syntax.expression) : result :=
  match (runs 1000 Values.create_store e) with
  | (context, result) => result
  end
.


