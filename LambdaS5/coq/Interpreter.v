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
* Value or Exception, but sometimes we want to return another kind
* of result, which is the reason why this type is parametered by
* value_type. *)
Inductive result {value_type : Type} : Type :=
  | Value : value_type -> result (* value *)
  | Exception : Values.value -> result (* exception message *)
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
  | EvaluationContext : (Values.store -> Syntax.expression -> (evaluation_context * (@result Values.value))) -> Values.store -> evaluation_context
.

(* Generates a new locations, assigns the object to this location in the
* context's store, and returns the new context and this location.
*)
Definition add_object_to_loc (context : evaluation_context) (object : Values.object) : (evaluation_context * (@result Values.object_loc)) :=
  match context with
  | BottomEvaluationContext store => 
      let (new_store, loc) := Values.add_object_to_store store object in
      (BottomEvaluationContext new_store, Value loc)
  | EvaluationContext runs store =>
      let (new_store, loc) := Values.add_object_to_store store object in
      (EvaluationContext runs new_store, Value loc)
  end
.
(* Fetches the object in the context's store that has this location, if any.
* Note: Should never return None, unless the code calling this function is
* inconsistent (asks for a location that does not exist…). *)
Definition get_object_of_loc (context : evaluation_context) (loc : Values.object_loc) : option Values.object :=
  match context with
  | BottomEvaluationContext store
  | EvaluationContext _ store =>
      Values.get_object_from_store store loc
  end
.

(* Returns the value associated to a variable name (aka. id) in the current
* context. *)
Definition get_value_of_name (context : evaluation_context) (name : Values.id) : option Values.value :=
  match context with
  | BottomEvaluationContext store
  | EvaluationContext _ store =>
      Values.get_value_from_store store name
  end
.

(* Evaluate an expression in a context, and calls the continuation with
* the new context and the result of the evaluation. *)
Definition eval_cont {value_type : Type} (context : evaluation_context) (e : Syntax.expression) (cont : evaluation_context -> (@result Values.value) -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
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

(* Returns a new context, which is the old context where the store
* has been replaced by a new one. *)
Definition replace_store (context : evaluation_context) (st : store) : evaluation_context :=
  match context with
  | BottomEvaluationContext (Values.store_intro obj_heap val_heap stream) =>
    BottomEvaluationContext st
  | EvaluationContext runs (Values.store_intro obj_heap val_heap stream) =>
    EvaluationContext runs st
  end
.

(* Unpacks a context to get the store's heaps, applies the predicate to the
* two heaps of the store, and returns a new context with a new store where
* the new store's heaps are the heaps returned by the predicated. *)
Definition update_store (context : evaluation_context) (pred : Values.object_heap_type -> Values.value_heap_type -> (Values.object_heap_type * Values.value_heap_type)) : evaluation_context :=
  let aux := (fun x stream =>
    match x with (new_obj_heap, new_val_heap) =>
      Values.store_intro new_obj_heap new_val_heap stream
    end
  ) in
  match context with
  | BottomEvaluationContext (Values.store_intro obj_heap val_heap stream) =>
    BottomEvaluationContext (aux (pred obj_heap val_heap) stream)
  | EvaluationContext runs (Values.store_intro obj_heap val_heap stream) =>
    EvaluationContext runs (aux (pred obj_heap val_heap) stream)
  end
.

(* Shortcut for instanciating and throwing an exception of the given name. *)
Definition raise_exception (context : evaluation_context) (name : string) : (evaluation_context * (@result Values.value)) :=
  match context with
  | BottomEvaluationContext st
  | EvaluationContext _ st =>
    match (Values.add_object_to_store st (Values.object_intro Values.Undefined name true None Heap.empty None)) with
    | (new_st, loc) =>
      (replace_store context new_st, Exception (Values.ObjectLoc loc))
    end
  end
.


(********* Monadic constructors ********)

(* Calls the continuation if the variable is a value.
* Returns the variable and the context verbatim otherwise. *)
Definition if_value {value_type : Type} {value_type_2 : Type} (context : evaluation_context) (var : @result value_type) (cont : evaluation_context -> value_type -> (evaluation_context * (@result value_type_2))) : (evaluation_context * (@result value_type_2)) :=
  match var with
  | Value v => cont context v
  | Exception exc => (context, Exception exc)
  | Fail f => (context, Fail f)
  end
.

(* Evaluates an expression in a context, and calls the continuation if
* the evaluation returned a value.
* Returns the context and the variable verbatim otherwise. *)
Definition if_eval_value {value_type : Type} (context : evaluation_context) (e : Syntax.expression) (cont : evaluation_context -> Values.value -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  eval_cont context e (fun context res => match res with
  | Value v => cont context v
  | Exception exc => (context, Exception exc)
  | Fail f => (context, Fail f)
  end
  )
.

(* Evaluates an expression with if it is Some, and calls the continuation
* if the evaluation returned value. Calls the continuation with the default
* value if the expression is None. *)
Definition if_some_eval_else_default {value_type : Type} (context : evaluation_context) (oe : option Syntax.expression) (default : Values.value) (cont : evaluation_context -> Values.value -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match oe with
  | Some e => if_eval_value context e cont
  | None => cont context default 
  end
.

(* Same as if_some_and_eval_value, but returns an option as the result, and
* None is used as the default value passed to the continuation. *)
Definition if_eval_value_option_default {value_type : Type} (context : evaluation_context) (oe : option Syntax.expression) (cont : evaluation_context -> option Values.value -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match oe with
  | Some e => if_eval_value context e (fun ctx res => cont ctx (Some res))
  | None => cont context None
  end
.

(* Calls the continuation if the value is an object location.
* Fails otherwise. *)
Definition assert_objloc {value_type : Type} (context : evaluation_context) (v : Values.value) (cont : evaluation_context -> Values.object_loc -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match v with
  | Values.ObjectLoc loc => cont context loc
  | _ => (context, Fail "Expected ObjectLoc but did not get one.")
  end
.

(* Calls the continuation if the value is an object location, and passes it the object.
* Fails otherwise. *)
Definition assert_get_object {value_type : Type} (context : evaluation_context) (v : Values.value) (cont : evaluation_context -> Values.object_loc -> Values.object -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  assert_objloc context v (fun context loc =>
    match (get_object_of_loc context loc) with
    | Some obj => cont context loc obj
    | None => (context, Fail "reference to non-existing object")
    end
  )
.

(* Calls the continuation if the value is a string.
* Fails otherwise. *)
Definition assert_string {value_type : Type} (context : evaluation_context) (v : Values.value) (cont : evaluation_context -> string -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match v with
  | Values.String s => cont context s
  | _ => (context, Fail "Expected String but did not get one.")
  end
.


(********* Evaluators ********)

(* a lonely identifier *)
Definition eval_id (context : evaluation_context) (name : string) : (evaluation_context * result) :=
  match (get_value_of_name context name) with
  | Some v => (context, Value v)
  | None => raise_exception context "ReferenceError"
  end
.


(* if e_cond e_true else e_false *)
Definition eval_if (context : evaluation_context) (e_cond e_true e_false : Syntax.expression) : (evaluation_context * result) :=
  if_eval_value context e_cond (fun context v =>
  match v with
  | Values.True => eval_cont_terminate context e_true
  | Values.False => eval_cont_terminate context e_false
  | _ => (context, Fail "if with neither true or false")
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
  | nil => (context, Value acc)
  | (name, Syntax.DataProperty (Syntax.Data value_expr writable) enumerable configurable) :: tail =>
    (* The order of the evaluation follows the original implementation. *)
    if_eval_value context value_expr (fun context value =>
        eval_object_properties_aux context tail (Heap.write acc name (
          Values.attributes_data_of {|
              Values.attributes_data_value := value;
              Values.attributes_data_writable := writable;
              Values.attributes_data_enumerable := enumerable;
              Values.attributes_data_configurable := configurable |}
        )))
  | (name, Syntax.AccessorProperty (Syntax.Accessor getter_expr setter_expr) enumerable configurable) :: tail =>
    (* The order of the evaluation follows the original implementation. *)
    if_eval_value context getter_expr (fun context getter =>
      if_eval_value context setter_expr (fun context setter =>
        eval_object_properties_aux context tail (Heap.write acc name (
           Values.attributes_accessor_of {|
              Values.attributes_accessor_get := getter;
              Values.attributes_accessor_set := setter;
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
    if_eval_value_option_default context primval_expr (fun context primval =>
      if_some_eval_else_default context prototype_expr Undefined (fun context prototype =>
        if_eval_value_option_default context code_expr (fun context code =>
          let (context, props) := (eval_object_properties context l)
          in if_value context props (fun context props =>
              let (context, loc) := (add_object_to_loc context {|
                  Values.object_proto := prototype;
                  Values.object_class := class;
                  Values.object_extensible := extensible;
                  Values.object_prim_value := primval;
                  Values.object_properties_ := props;
                  Values.object_code := code_expr |})
                in if_value context loc (fun context loc => (context, Value (Values.ObjectLoc loc)))
          ))))
  end
.

(* left[right, attrs] *)
Definition eval_get_field (context : evaluation_context) (left_expr right_expr attrs_expr : Syntax.expression) : (evaluation_context * result) :=
  if_eval_value context left_expr (fun context left =>
    if_eval_value context right_expr (fun context right =>
      if_eval_value context attrs_expr (fun context attrs =>
        assert_get_object context left (fun context loc object =>
          assert_string context right (fun context name =>
            match (Values.get_object_property object name) with
            | Some (attributes_data_of data) => (context, Value (Values.attributes_data_value data))
            | Some (attributes_accessor_of accessor) => (BottomEvaluationContext Values.create_store, Fail "getter not implemented.")
            | None => (context, Value Values.Undefined)
            end)))))
.

(* If Some Data attributes are given, returns them with the #value replaced.
* TODO: If Some Accessor, should fail.
* If None, returns None. *)
Definition build_attrs (old_attrs : option Values.attributes) (new_val : Values.value) : Values.attributes :=
  (* TODO: Test writable/configurable *)
  match old_attrs with
  | Some (Values.attributes_data_of (Values.attributes_data_intro v w e c)) =>
    Values.attributes_data_of (Values.attributes_data_intro new_val w e c)
  | None => Values.attributes_data_of (attributes_data_intro new_val true true true)
  | _ => Values.attributes_data_of (Values.attributes_data_intro new_val true false true) (* TODO: Implement this *)
  end
.

(* Takes an object (which has to be the object pointed by loc in the context),
* replaces one of its properties (designated by its name) by the new value,
* and returns the new context. *)
Definition set_object_field_value (context : evaluation_context) (loc : Values.object_loc) (obj : Values.object) (name : string) (new_val : Values.value) : evaluation_context :=
  update_store context (fun obj_heap val_heap =>
    match obj with object_intro prot c e prim props code =>
      let attrs := build_attrs (Heap.read_option props name) new_val in
      let props2 := Heap.write props name attrs in
      (Heap.write obj_heap loc (object_intro prot c e prim props2 code), val_heap)
    end
  )
.

(* left[right, attrs] = new_val *)
Definition eval_set_field (context : evaluation_context) (left_expr right_expr new_val_expr attrs_expr : Syntax.expression) : (evaluation_context * result) :=
  if_eval_value context left_expr (fun context left =>
    if_eval_value context right_expr (fun context right =>
      if_eval_value context new_val_expr (fun context new_val =>
        assert_get_object context left (fun context loc object =>
          if_eval_value context attrs_expr (fun context attrs =>
            assert_string context right (fun context name =>
              match (Values.get_object_property object name) with
              | Some (attributes_data_of data) => (set_object_field_value context loc object name new_val, Value new_val)
              | Some (attributes_accessor_of accessor) => (BottomEvaluationContext Values.create_store, Fail "setter not implemented.")
              | None => (context, Value Values.Undefined)
              end))))))
.


(* let id = value in body *)
Definition eval_let (context : evaluation_context) (id : string) (value_expr body_expr : Syntax.expression) : (evaluation_context * result) :=
  if_eval_value context value_expr (fun context value =>
    let new_context := update_store context (fun obj_heap val_heap => 
        (obj_heap, Heap.write val_heap id value))
      in eval_cont_terminate new_context body_expr
  )
.


(******** Closing the loop *******)

(* Main evaluator *)
Definition eval (context : evaluation_context) (e : Syntax.expression) : (evaluation_context * result) :=
  let return_value := (fun v => (context, Value v)) in
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


