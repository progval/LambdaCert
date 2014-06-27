Require Import List.
Require Import String.
Require Import Syntax.
Require Import Values.
Require Import LibHeap.
Require Import LibStream.
Open Scope list_scope.

(* The result of the execution of a program *)
Inductive result {value_type : Type} : Type :=
  | Value : value_type -> result (* value *)
  | Exception : Values.value -> result (* exception message *)
  | Fail : string -> result (* reason *)
.

(* The interpreter environment (“context”) used to evaluate an expression *)
Inductive evaluation_context : Type :=
  | BottomEvaluationContext
  (* EvaluationContext (runs max_steps) store *)
  | EvaluationContext : (Values.store -> Syntax.expression -> (evaluation_context * (@result Values.value))) -> Values.store -> evaluation_context
.

Definition add_object_to_heap (context : evaluation_context) (object : Values.object) : (evaluation_context * (@result Values.object_loc)) :=
  match context with
  | BottomEvaluationContext => (BottomEvaluationContext, Fail "bottom")
  | EvaluationContext runs store =>
      let (new_store, loc) := Values.add_object_to_store store object in
      (EvaluationContext runs new_store, Value loc)
  end
.

(* Evaluate an expression in a context, and calls the continuation *)
Definition eval_cont {value_type : Type} (context : evaluation_context) (e : Syntax.expression) (cont : evaluation_context -> (@result Values.value) -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match context with
  | BottomEvaluationContext => (BottomEvaluationContext, Fail "bottom")
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


(********* Monadic constructors ********)

(* Evaluates an expression in a context, and calls the continuation if
* the evaluation returned a value. *)
Definition if_value {value_type : Type} (context : evaluation_context) (e : Syntax.expression) (cont : evaluation_context -> Values.value -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  eval_cont context e (fun context res => match res with
  | Value v => cont context v
  | Exception exc => (context, Exception exc)
  | Fail f => (context, Fail f)
  end
  )
.

(* Evaluates an expression with if it is Some, and calls the continuation
* if the evaluation returned value. Calls the continuation of the default
* value if the expression is None. *)
Definition if_some_and_value (context : evaluation_context) (oe : option Syntax.expression) (default : Values.value) (cont : evaluation_context -> Values.value -> (evaluation_context * result)) : (evaluation_context * result) :=
  match oe with
  | Some e => if_value context e cont
  | None => (context, Value default)
  end
.

(* Same as if_some_and_value, but returns an option as the result, and
* None is used as the default. *)
Definition if_some_and_value_option {value_type : Type} (context : evaluation_context) (oe : option Syntax.expression) (cont : evaluation_context -> option Values.value -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match oe with
  | Some e => if_value context e (fun ctx res => cont ctx (Some res))
  | None => cont context None
  end
.

(********* Evaluators ********)

(* if e_cond e_true else e_false *)
Definition eval_if (context : evaluation_context) (e_cond e_true e_false : expression) : (evaluation_context * result) :=
  if_value context e_cond (fun context v =>
  match v with
  | Values.True => eval_cont_terminate context e_true
  | Values.False => eval_cont_terminate context e_false
  | _ => (context, Fail "if with neither true or false")
  end
  )
.

(* e1 ; e2 *)
Definition eval_seq (context : evaluation_context) (e1 e2 : expression) : (evaluation_context * result) :=
  if_value context e1 (fun context v => eval_cont_terminate context e2 )
.


Fixpoint eval_object_properties_aux (context : evaluation_context) (l : list (string * Syntax.property)) (acc : Values.object_properties) : (evaluation_context * (@result Values.object_properties)) :=
  match l with
  | nil => (context, Value Heap.empty)
  | (name, Syntax.DataProperty (Syntax.Data value_expr writable) enumerable configurable) :: tail =>
    (* Note: we have to evaluate properties' expressions in the right order *)
    if_value context value_expr (fun context value =>
        eval_object_properties_aux context tail (Heap.write acc name (
          Values.attributes_data_of {|
              Values.attributes_data_value := value;
              Values.attributes_data_writable := writable;
              Values.attributes_data_enumerable := enumerable;
              Values.attributes_data_configurable := configurable |}
        )))
  | (name, Syntax.AccessorProperty (Syntax.Accessor getter_expr setter_expr) enumerable configurable) :: tail =>
    if_value context getter_expr (fun context getter =>
      if_value context setter_expr (fun context setter =>
        eval_object_properties_aux context tail (Heap.write acc name (
           Values.attributes_accessor_of {|
              Values.attributes_accessor_get := getter;
              Values.attributes_accessor_set := setter;
              Values.attributes_accessor_enumerable := enumerable;
              Values.attributes_accessor_configurable := configurable |}
    ))))
  end
.
(* Reads a syntax tree of properties and converts it to a heap
* bindable to an object. *)
Definition eval_object_properties (context : evaluation_context) (l : list (string * Syntax.property)) : (evaluation_context * (@result Values.object_properties)) :=
  eval_object_properties_aux context l Heap.empty
.

(* { [ attrs ] props } *)
Definition eval_object_decl (context : evaluation_context) (attrs : Syntax.object_attributes) (e : expression) (l : list (string * Syntax.property)) : (evaluation_context * result) :=

  match attrs with
  | Syntax.ObjectAttributes primval_expr code_expr prototype_expr class extensible =>
    (* Following the order in the original implementation: *)
    if_some_and_value_option context primval_expr (fun context primval =>
      if_some_and_value context prototype_expr Undefined (fun context prototype =>
        if_some_and_value_option context code_expr (fun context code => 
          match (eval_object_properties context l) with
          | (context, Value props) =>
              match (add_object_to_heap context {|
                Values.object_proto := prototype;
                Values.object_class := class;
                Values.object_extensible := extensible;
                Values.object_prim_value := primval;
                Values.object_properties_ := props;
                Values.object_code := code_expr |}) with
              | (context, Value loc) => (context, Value (Values.ObjectLoc loc))
              | (context, Exception exc) => (context, Exception exc)
              | (context, Fail f) => (context, Fail f)
              end
          | (context, Exception exc) => (context, Exception exc)
          | (context, Fail f) => (context, Fail f)
          end)))
  end
.


(* Main evaluator *)
Definition eval (context : evaluation_context) (e : Syntax.expression) : (evaluation_context * result) :=
  let return_value := (fun v => (context, Value v)) in
  match e with
  | Syntax.Undefined => return_value Values.Undefined
  | Syntax.String s => return_value (Values.String s)
  | Syntax.Number n => return_value (Values.Number n)
  | Syntax.True => return_value Values.True
  | Syntax.False => return_value Values.False
  | Syntax.If e_cond e_true e_false => eval_if context e_cond e_true e_false
  | Syntax.Seq e1 e2 => eval_seq context e1 e2
  | Syntax.ObjectDecl attrs e l => eval_object_decl context attrs e l
  | _ => (context, Fail "not implemented")
  end
.

(* Evaluates expression and ensure there is a decreasing argument. *)
Fixpoint runs (max_steps : nat) (store : Values.store) (e : Syntax.expression) : (evaluation_context * result) :=
  match (max_steps) with
  | 0 => (BottomEvaluationContext, Fail "Coq is not Turing-complete")
  | S max_steps' => eval (EvaluationContext (runs max_steps')  store) e
  end
.

(* Alias for calling runs with only an expression and getting only a result *)
Definition runs_call (e : Syntax.expression) : result :=
  match (runs 1000 Values.create_store e) with
  | (context, result) => result
  end
.


Eval vm_compute in (runs_call (Syntax.If Syntax.False (Syntax.String "true") (Syntax.String "false"))).

