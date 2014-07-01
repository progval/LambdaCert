Require Import List.
Require Import Coq.Strings.String.
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
  (* We put the store here to make functions using the following ones easier to read and to write. *)
  | BottomEvaluationContext : Values.store -> evaluation_context
  (* EvaluationContext (runs max_steps) store *)
  | EvaluationContext : (Values.store -> Syntax.expression -> (evaluation_context * (@result Values.value))) -> Values.store -> evaluation_context
.

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
Definition get_object_from_loc (context : evaluation_context) (loc : Values.object_loc) : option Values.object :=
  match context with
  | BottomEvaluationContext store =>
      Values.get_object_from_store store loc
  | EvaluationContext runs store =>
      Values.get_object_from_store store loc
  end
.

(* Evaluate an expression in a context, and calls the continuation *)
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


(********* Monadic constructors ********)

(* calls the continuation if the variable is a value. *)
Definition if_value {value_type : Type} {value_type_2 : Type} (context : evaluation_context) (var : @result value_type) (cont : evaluation_context -> value_type -> (evaluation_context * (@result value_type_2))) : (evaluation_context * (@result value_type_2)) :=
  match var with
  | Value v => cont context v
  | Exception exc => (context, Exception exc)
  | Fail f => (context, Fail f)
  end
.

(* Evaluates an expression in a context, and calls the continuation if
* the evaluation returned a value. *)
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
Definition if_eval_value_default {value_type : Type} (context : evaluation_context) (oe : option Syntax.expression) (default : Values.value) (cont : evaluation_context -> Values.value -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match oe with
  | Some e => if_eval_value context e cont
  | None => cont context default 
  end
.

(* Same as if_some_and_eval_value, but returns an option as the result, and
* None is used as the default. *)
Definition if_eval_value_option_default {value_type : Type} (context : evaluation_context) (oe : option Syntax.expression) (cont : evaluation_context -> option Values.value -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match oe with
  | Some e => if_eval_value context e (fun ctx res => cont ctx (Some res))
  | None => cont context None
  end
.

(* Calls the continuation if the value is an object location *)
Definition if_objloc {value_type : Type} (context : evaluation_context) (v : Values.value) (cont : evaluation_context -> Values.object_loc -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match v with
  | Values.ObjectLoc loc => cont context loc
  | _ => (context, Fail "Expected ObjectLoc but did not get one.")
  end
.

(* Calls the continuation if the value is an object location, and passes it the object *)
Definition if_get_object {value_type : Type} (context : evaluation_context) (v : Values.value) (cont : evaluation_context -> Values.object -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  if_objloc context v (fun context loc =>
    match (get_object_from_loc context loc) with
    | Some obj => cont context obj
    | None => (context, Fail "reference to non-existing object")
    end
  )
.

(* Calls the continuation if the value is an object location *)
Definition if_string {value_type : Type} (context : evaluation_context) (v : Values.value) (cont : evaluation_context -> string -> (evaluation_context * (@result value_type))) : (evaluation_context * (@result value_type)) :=
  match v with
  | Values.String s => cont context s
  | _ => (context, Fail "Expected String but did not get one.")
  end
.


(********* Evaluators ********)

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


Fixpoint eval_object_properties_aux (context : evaluation_context) (l : list (string * Syntax.property)) (acc : Values.object_properties) : (evaluation_context * (@result Values.object_properties)) :=
  match l with
  | nil => (context, Value acc)
  | (name, Syntax.DataProperty (Syntax.Data value_expr writable) enumerable configurable) :: tail =>
    (* Note: we have to evaluate properties' expressions in the right order *)
    if_eval_value context value_expr (fun context value =>
        eval_object_properties_aux context tail (Heap.write acc name (
          Values.attributes_data_of {|
              Values.attributes_data_value := value;
              Values.attributes_data_writable := writable;
              Values.attributes_data_enumerable := enumerable;
              Values.attributes_data_configurable := configurable |}
        )))
  | (name, Syntax.AccessorProperty (Syntax.Accessor getter_expr setter_expr) enumerable configurable) :: tail =>
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
(* Reads a syntax tree of properties and converts it to a heap
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
      if_eval_value_default context prototype_expr Undefined (fun context prototype =>
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
        if_get_object context left (fun context object =>
          if_string context right (fun context name =>
            match (Values.get_object_property object name) with
            | Some (attributes_data_of data) => (context, Value (Values.attributes_data_value data))
            | Some (attributes_accessor_of accessor) => (context, Value (Values.attributes_accessor_get accessor))
            | None => (context, Value Values.Undefined)
            end)))))
.
        
        

(* left[right, attrs] = new_val *)

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
  | Syntax.ObjectDecl attrs l => eval_object_decl context attrs l
  | Syntax.GetField left_ right_ attributes => eval_get_field context left_ right_ attributes
  (*| Syntax.SetField left_ right_ new_val attributes => eval_set_field context left_ right_ new_val attributes*)
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


