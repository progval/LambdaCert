Require Import List.
Require Import Coq.Strings.String.
Require Import Syntax.
Require Import Values.
Require Import Context.
Require Import Utils.
Require Import LibHeap.
Require Import LibStream.
Open Scope list_scope.
Open Scope string_scope.

(* Basic idea of how this file works:
* There are four sections in this file:
* * The utilities, for evaluating sub-terms.
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

Implicit Type context : Context.context.


(******* Utilities *******)


(* Evaluate an expression in a context, and calls the continuation with
* the new context and the Context.result of the evaluation. *)
Definition eval_cont {value_type : Type} ctx (e : Syntax.expression) (cont : Context.context -> (@Context.result Values.value_loc) -> (Context.context * (@Context.result value_type))) : (Context.context * (@Context.result value_type)) :=
  match ctx with
  | BottomEvaluationContext store => (BottomEvaluationContext store, Fail "bottom")
  | EvaluationContext runs store =>
    match (runs store e) with (ctx, res) =>
      cont ctx res
    end
  end
.
(* Alias for calling eval_cont with an empty continuation *)
Definition eval_cont_terminate ctx (e : Syntax.expression) : (Context.context * Context.result) :=
  eval_cont ctx e (fun ctx res => (ctx, res))
.

(********* Monadic constructors ********)

(* Calls the continuation if the variable is a value.
* Returns the variable and the context verbatim otherwise. *)
Definition if_return {value_type : Type} {value_type_2 : Type} context (var : @Context.result value_type) (cont : Context.context -> value_type -> (Context.context * (@Context.result value_type_2))) : (Context.context * (@Context.result value_type_2)) :=
  match var with
  | Return v => cont context v
  | Exception exc => (context, Exception exc)
  | Fail f => (context, Fail f)
  end
.

(* Evaluates an expression in a context, and calls the continuation if
* the evaluation returned a value.
* Returns the context and the variable verbatim otherwise. *)
Definition if_eval_return {value_type : Type} context (e : Syntax.expression) (cont : Context.context -> Values.value_loc -> (Context.context * (@Context.result value_type))) : (Context.context * (@Context.result value_type)) :=
  eval_cont context e (fun context res => match res with
  | Return v => cont context v
  | Exception exc => (context, Exception exc)
  | Fail f => (context, Fail f)
  end
  )
.

(* Evaluates an expression with if it is Some, and calls the continuation
* if the evaluation returned value. Calls the continuation with the default
* value if the expression is None. *)
Definition if_some_eval_else_default {value_type : Type} context (oe : option Syntax.expression) (default : Values.value_loc) (cont : Context.context -> Values.value_loc -> (Context.context * (@Context.result value_type))) : (Context.context * (@Context.result value_type)) :=
  match oe with
  | Some e => if_eval_return context e cont
  | None => cont context default 
  end
.

(* Same as if_some_and_eval_value, but returns an option as the Context.result, and
* None is used as the default value passed to the continuation. *)
Definition if_some_eval_return_else_none {value_type : Type} context (oe : option Syntax.expression) (cont : Context.context -> option Values.value_loc -> (Context.context * (@Context.result value_type))) : (Context.context * (@Context.result value_type)) :=
  match oe with
  | Some e => if_eval_return context e (fun ctx res => cont ctx (Some res))
  | None => cont context None
  end
.

(* Calls the continuation with the referenced value. Fails if the reference
* points to a non-existing object (never actually happens). *)
Definition assert_deref {value_type : Type} context (loc : Values.value_loc) (cont : Context.context -> Values.value -> (Context.context * (@Context.result value_type))) : (Context.context * (@Context.result value_type)) :=
  match (get_value_of_loc context loc) with
  | Some val => cont context val
  | None => (context, Fail "Location of non-existing value.")
  end
.

(* Calls the continuation if the value is a location to a value (always!), and passes the value to the continuation.
* Fails otherwise. *)
Definition assert_get {value_type : Type} context (loc : Values.value_loc) (cont : Context.context -> Values.value -> (Context.context * (@Context.result value_type))) : (Context.context * (@Context.result value_type)) :=
  match (Context.get_value_of_loc context loc) with
  | Some val => cont context val
  | None => (context, Fail "Location of non-existing value.")
  end
.

(* Calls the continuation if the value is an object pointer, and passes the pointer to the continuation.
* Fails otherwise. *)
Definition assert_get_object_ptr {value_type : Type} context (loc : Values.value_loc) (cont : Context.context -> Values.object_ptr -> (Context.context * (@Context.result value_type))) : (Context.context * (@Context.result value_type)) :=
  match (Context.get_value_of_loc context loc) with
  | Some (Values.Object ptr) => cont context ptr
  | Some _ => (context, Fail "Expected an object pointer.")
  | None => (context, Fail "Location of non-existing value.")
  end
.

Definition assert_get_object_of_ptr {value_type : Type} context (ptr : Values.object_ptr) (cont : Context.context -> Values.object -> (Context.context * (@Context.result value_type))) : (Context.context * (@Context.result value_type)) :=
  match (Context.get_object_of_ptr context ptr) with
  | Some obj => cont context obj
  | None => (context, Fail "Pointer to a non-existing object.")
  end
.

(* Calls the continuation if the value is an object pointer, and passes the object to the continuation *)
Definition assert_get_object {value_type : Type} context (loc : Values.value_loc) (cont : Context.context -> Values.object -> (Context.context * (@Context.result value_type))) : (Context.context * (@Context.result value_type)) :=
  assert_get_object_ptr context loc (fun context ptr =>
    assert_get_object_of_ptr context ptr cont
  )
.

(* Calls the continuation if the value is a string.
* Fails otherwise. *)
Definition assert_get_string {value_type : Type} context (loc : Values.value_loc) (cont : Context.context -> string -> (Context.context * (@Context.result value_type))) : (Context.context * (@Context.result value_type)) :=
  match (get_value_of_loc context loc) with
  | Some (Values.String s) => cont context s
  | Some _ => (context, Fail "Expected String but did not get one.")
  | None => (context, Fail "Location of non-existing value.")
  end
.


(********* Evaluators ********)

(* a lonely identifier *)
Definition eval_id context (name : string) : (Context.context * Context.result) :=
  match (get_loc_of_name context name) with
  | Some v => (context, Return v)
  | None => raise_exception context "ReferenceError"
  end
.


(* if e_cond e_true else e_false *)
Definition eval_if context (e_cond e_true e_false : Syntax.expression) : (Context.context * Context.result) :=
  if_eval_return context e_cond (fun context v =>
  match (get_value_of_loc context v) with
  | Some Values.True => eval_cont_terminate context e_true
  | Some Values.False => eval_cont_terminate context e_false
  | Some _ => (context, Fail "if with neither true or false")
  | None => (context, Fail "Location of non-existing value.")
  end
  )
.

(* e1 ; e2 *)
Definition eval_seq context (e1 e2 : Syntax.expression) : (Context.context * Context.result) :=
  if_eval_return context e1 (fun context v => eval_cont_terminate context e2 )
.


(* A tail-recursive helper for eval_object_properties, that constructs
* the list of properties. *)
Fixpoint eval_object_properties_aux context (l : list (string * Syntax.property)) (acc : Values.object_properties) : (Context.context * (@Context.result Values.object_properties)) :=
  match l with
  | nil => (context, Return acc)
  | (name, Syntax.DataProperty (Syntax.Data value_expr writable) enumerable configurable) :: tail =>
    (* The order of the evaluation follows the original implementation. *)
    if_eval_return context value_expr (fun context value_loc =>
      eval_object_properties_aux context tail (Heap.write acc name (
        Values.attributes_data_of {|
            Values.attributes_data_value := value_loc;
            Values.attributes_data_writable := writable;
            Values.attributes_data_enumerable := enumerable;
            Values.attributes_data_configurable := configurable |}
      )))
  | (name, Syntax.AccessorProperty (Syntax.Accessor getter_expr setter_expr) enumerable configurable) :: tail =>
    (* The order of the evaluation follows the original implementation. *)
    if_eval_return context getter_expr (fun context getter_loc =>
      if_eval_return context setter_expr (fun context setter_loc =>
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
Definition eval_object_properties context (l : list (string * Syntax.property)) : (Context.context * (@Context.result Values.object_properties)) :=
  eval_object_properties_aux context l Heap.empty
.

(* { [ attrs ] props } *)
Definition eval_object_decl context (attrs : Syntax.object_attributes) (l : list (string * Syntax.property)) : (Context.context * Context.result) :=

  match attrs with
  | Syntax.ObjectAttributes primval_expr code_expr prototype_expr class extensible =>
    (* Following the order in the original implementation: *)
    if_some_eval_return_else_none context primval_expr (fun context primval_loc =>
      let (context, proto_default) := Context.add_value context Values.Undefined in
      if_some_eval_else_default context prototype_expr proto_default (fun context prototype_loc =>
        if_some_eval_return_else_none context code_expr (fun context code =>
          let (context, props) := (eval_object_properties context l)
          in if_return context props (fun context props =>
            Context.add_object_return context {|
                Values.object_proto := prototype_loc;
                Values.object_class := class;
                Values.object_extensible := extensible;
                Values.object_prim_value := primval_loc;
                Values.object_properties_ := props;
                Values.object_code := code_expr |}
          ))))
  end
.

(* left[right, attrs] *)
Definition eval_get_field context (left_expr right_expr attrs_expr : Syntax.expression) : (Context.context * Context.result) :=
  if_eval_return context left_expr (fun context left =>
    if_eval_return context right_expr (fun context right =>
      if_eval_return context attrs_expr (fun context attrs =>
        assert_get_object context left (fun context object =>
          assert_get_string context right (fun context name =>
            match (Values.get_object_property object name) with
            | Some (attributes_data_of data) => (context, Return (Values.attributes_data_value data))
            | Some (attributes_accessor_of accessor) => (BottomEvaluationContext Values.create_store, Fail "getter not implemented.")
            | None => Context.add_value_return context Values.Undefined
            end)))))
.

(* left[right, attrs] = new_val *)
Definition eval_set_field context (left_expr right_expr new_val_expr attrs_expr : Syntax.expression) : (Context.context * Context.result) :=
  if_eval_return context left_expr (fun context left_loc =>
    if_eval_return context right_expr (fun context right =>
      if_eval_return context new_val_expr (fun context new_val =>
        if_eval_return context attrs_expr (fun context attrs =>
          assert_get_string context right (fun context name =>
            assert_get_object_ptr context left_loc (fun context left_ptr =>
              Context.update_object context left_ptr (fun object =>
                match (Values.get_object_property object name) with
                | Some (attributes_data_of (Values.attributes_data_intro _ w e c)) =>
                  let attrs := Values.attributes_data_of (attributes_data_intro new_val w e c) in
                  let new_obj := Values.set_object_property object name attrs in
                  (new_obj, Context.Return new_val)
                | Some (attributes_accessor_of accessor) => (object, Fail "setter not implemented.") (* TODO *)
                | None => 
                  let attrs := Values.attributes_data_of (attributes_data_intro new_val true true false) in
                  let new_obj := Values.set_object_property object name attrs in
                  (new_obj, Context.Return new_val)
                end)))))))
.


(* let (id = expr) body *)
Definition eval_let context (id : string) (value_expr body_expr : Syntax.expression) : (Context.context * Context.result) :=
  if_eval_return context value_expr (fun context value_loc =>
    assert_deref context value_loc (fun context value =>
      let (new_context, loc) := Context.add_named_value context id value in
        eval_cont_terminate new_context body_expr
  ))
.

(* name := expr *)
Definition eval_setbang context (name : string) (expr : Syntax.expression) : (Context.context * Context.result) :=
  if_eval_return context expr (fun context value_loc =>
    assert_deref context value_loc (fun context value =>
      match (get_loc_of_name context name) with
      | Some loc => (Context.add_value_at_location context loc value, Context.Return value_loc)
      | None => raise_exception context "ReferenceError"
      end
  ))
.

(* func (args) { body } *)
Definition eval_lambda context (args : list id) (body : Syntax.expression) : (Context.context * Context.result) :=
  let env := Context.read_store context Values.loc_heap in
  Context.add_value_return context (Values.Closure env args body)
.


(* Evaluates all arguments, passing the context from one to the next. *)
(* FIXME: Do it in the right order. *)
Definition eval_arg_list_aux (left : (Context.context * @Context.result (list Values.value_loc))) (arg_expr : Syntax.expression) : (Context.context * @Context.result (list Values.value_loc)) :=
  let (context, res) := left in
  if_return context res (fun context left_args =>
    if_eval_return context arg_expr (fun context arg_loc =>
      (context, Return (arg_loc :: left_args))))
.


Definition eval_arg_list context (args_expr : list Syntax.expression) : (Context.context * Context.result) :=
  List.fold_left eval_arg_list_aux args_expr (context, Return nil)
.

Definition make_app_loc_heap (app_context lambda_context : Values.loc_heap_type) (args_name : list Values.id) (args : list Values.value_loc) : option Values.loc_heap_type :=
  match (Utils.zip_left (List.rev args_name) args) with
  | Some args_heap =>
    Some (Utils.concat_list_heap
      args_heap
      (Utils.concat_heaps lambda_context app_context)
    )
  | None => None
  end
.

Definition make_app_context context (closure_env : Values.loc_heap_type) (args_name : list Values.id) (args_expr : list Syntax.expression) : (Context.context * Context.result) :=
  let (context, res) := eval_arg_list context args_expr in
  if_return context res (fun context args =>
    Context.update_store context (fun st =>
      match st with Values.store_intro obj_heap val_heap loc_heap stream =>
        match (make_app_loc_heap loc_heap closure_env args_name args) with
        | Some new_loc_heap =>
          (Values.store_intro obj_heap val_heap new_loc_heap stream, Context.Return 0) (* We have to return something... *)
        | None => (st, Fail "Arity mismatch")
        end
      end
  ))
.


(* f (args) *)
Definition eval_app context (f : Syntax.expression) (args_expr : list Syntax.expression) : (Context.context * Context.result) :=
  if_eval_return context f (fun context f_loc =>
    assert_deref context f_loc (fun context f =>
      match f with
      | Values.Closure env args_names body =>
        let (context, res) := make_app_context context env args_names args_expr in
        if_return context res (fun context _ =>
          eval_cont_terminate context body
        )
      | Values.Object ptr =>
        assert_get_object_of_ptr context ptr (fun context obj =>
          match (Values.object_code obj) with
          | Some code => eval_cont_terminate context (Syntax.App code args_expr)
          | None => Context.raise_exception context "Calling non-callable object."
          end
        )
      | _ => (context, Fail "Expected Closure but did not get one.")
      end
  ))
.
        
      

(******** Closing the loop *******)

(* Main evaluator *)
Definition eval context (e : Syntax.expression) : (Context.context * (@Context.result Values.value_loc)) :=
  let return_value := (fun v => Context.add_value_return context v) in
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
  | Syntax.SetBang id expr => eval_setbang context id expr
  | Syntax.Lambda args body => eval_lambda context args body
  | Syntax.App f args => eval_app context f args
  | _ => (context, Fail "not implemented")
  end
.

(* Evaluates expression and ensure there is a decreasing argument. *)
Fixpoint runs (max_steps : nat) (store : Values.store) (e : Syntax.expression) : (Context.context * Context.result) :=
  match (max_steps) with
  | 0 => (BottomEvaluationContext store, Fail "Coq is not Turing-complete")
  | S max_steps' => eval (EvaluationContext (runs max_steps')  store) e
  end
.

(* Alias for calling runs with only an expression and getting only a Context.result *)
Definition runs_call (e : Syntax.expression) : Context.result :=
  match (runs 1000 Values.create_store e) with
  | (context, res) => res
  end
.


