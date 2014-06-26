Require Import String.
Require Import Syntax.
Require Import Values.
Require Import List.
Open Scope list_scope.

(* The result of the execution of a program *)
Inductive result : Type :=
  | Value : Values.value -> result (* value, store *)
  | Exception : Values.value -> result (* exception, store *)
  | Fail : string -> result (* reason *)
.

(* The interpreter environment (“context”) used to evaluate an expression *)
Inductive evaluation_context : Type :=
  | BottomEvaluationContext
  (* EvaluationContext (runs max_steps) store *)
  | EvaluationContext : (Values.store -> Syntax.expression -> (evaluation_context * result)) -> Values.store -> evaluation_context
.

(* Evaluate an expression in a context, and calls the continuation *)
Definition eval_cont (context : evaluation_context) (e : Syntax.expression) (cont : evaluation_context -> result -> (evaluation_context * result)) : (evaluation_context * result) :=
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
Definition if_value (context : evaluation_context) (e : Syntax.expression) (cont : evaluation_context -> Values.value -> (evaluation_context * result)) : (evaluation_context * result) :=
  eval_cont context e (fun context res => match res with
  | Value v => cont context v
  | Exception exc => (context, Exception exc)
  | Fail f => (context, Fail f)
  end
  )
.

(********* Evaluators ********)

(* if e_cond then e_true else e_false *)
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
  | _ => (context, Fail "not implemented")
  end
.

(* Evaluates expression and ensure there is a decreasing argument. *)
Fixpoint runs (max_steps : nat) (store : Values.store) (e : Syntax.expression) : (evaluation_context * result) :=
  match (max_steps) with
  | 0 => (BottomEvaluationContext, Fail "Coq is not Turing-complete")
  | S max_steps' => eval (EvaluationContext (runs max_steps') store) e
  end
.

(* Alias for calling runs with only an expression and getting only a result *)
Definition runs_call (e : Syntax.expression) : result :=
  match (runs 1000 Values.create_store e) with
  | (context, result) => result
  end
.


Eval vm_compute in (runs_call (Syntax.If Syntax.False (Syntax.String "true") (Syntax.String "false"))).

