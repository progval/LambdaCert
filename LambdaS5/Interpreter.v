Require Import String.
Require Import Syntax.
Require Import Values.
Require Import List.
Open Scope list_scope.

(*
Record evaluator :=
  Evaluator { 
      evaluate : expression -> expression;
      max_step : nat
  }
.
*)

Inductive result : Type :=
  | Value : Values.value -> Values.store -> result (* value, store *)
  | Exception : Values.value -> Values.store -> result (* exception, store *)
  | Fail : string -> result (* reason *)
.

(*Fixpoint call_eval (E : evaluator) (st : store) (e : expression) : result :=
  eval {| evaluate := cal
*)

Fixpoint if_value (steps : nat) (st : store) (e : Syntax.expression) (cont : Values.value -> Values.store -> result) :=
  match steps with
  | 0 => Fail "Coq is not Turing-complete"
  | S steps' =>
    match (eval steps' st e) with
    | Value v st2 => cont v st2
    | Exception exc st2 => Exception exc st2
    | Fail f => Fail f
    end
  end
with eval (steps : nat) (st : Values.store) (e : Syntax.expression) : result :=
  match steps with
  | 0 => Fail "Coq is not Turing-complete"
  | S steps' =>
    let if_value_l := (if_value steps' st) in
    match e with
    | Syntax.Undefined => Value Values.Undefined st
    | Syntax.String s => Value (Values.String s) st
    | Syntax.Number n => Value (Values.Number n) st
    | Syntax.True => Value Values.True st
    | Syntax.False => Value Values.False st
    | Syntax.If e_cond e_true e_false =>
      if_value_l e_cond (fun v st2 =>
      match v with
      | Values.True => eval steps' st2 e_true
      | Values.False => eval steps' st2 e_false
      | _ => Fail "if with neither true or false"
      end
      )
    | Syntax.Seq e1 e2 =>
      if_value_l e1 (fun v st2 => eval steps' st2 e2)
    | _ => Fail "not implemented"
    end
  end
.


Eval compute in (eval 1000 Values.create_store (Syntax.If Syntax.False (Syntax.String "true") (Syntax.String "false"))).

