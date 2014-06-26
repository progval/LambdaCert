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
Fixpoint eval (n : nat) (st : Values.store) (e : Syntax.expression) : result :=
  match n with
  | 0 => Fail "Coq is not Turing-complete"
  | S n' =>
    match e with
    | Syntax.Undefined => Value Values.Undefined st
    | Syntax.String s => Value (Values.String s) st
    | Syntax.Number n => Value (Values.Number n) st
    | Syntax.True => Value Values.True st
    | Syntax.False => Value Values.False st
    | Syntax.If e_cond e_true e_false =>
      match (eval n' st e_cond) with
      | Value Values.True st2 => eval n' st2 e_true
      | Value Values.False st2 => eval n' st2 e_false
      | Value _ st2 => Fail "if with neither true or false"
      | Exception exc st2 => Exception exc st2
      | Fail f => Fail f
      end
    | _ => Fail "not implemented"
    end
  end
.


Eval compute in (eval 1000 Values.create_store (Syntax.If Syntax.False (Syntax.String "true") (Syntax.String "false"))).

