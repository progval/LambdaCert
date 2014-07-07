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
* * The monadic constructors, which mostly take a store, some
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


Implicit Type runs : Context.runs_type.
Implicit Type store : Values.store.


(******* Utilities *******)


(* Evaluate an expression, and calls the continuation with
* the new store and the Context.result of the evaluation. *)
Definition eval_cont {value_type : Type} runs store (e : Syntax.expression) (cont : Values.store -> (@Context.result Values.value_loc) -> (Values.store * (@Context.result value_type))) : (Values.store * (@Context.result value_type)) :=
  match ((Context.runs_type_eval runs) store e) with (store, res) =>
    cont store res
  end
.
(* Alias for calling eval_cont with an empty continuation *)
Definition eval_cont_terminate runs store (e : Syntax.expression) : (Values.store * Context.result) :=
  eval_cont runs store e (fun store res => (store, res))
.

(********* Monadic constructors ********)

(* Calls the continuation if the variable is a value.
* Returns the variable and the store verbatim otherwise. *)
Definition if_return {value_type : Type} {value_type_2 : Type} store (var : @Context.result value_type) (cont : value_type -> (Values.store * (@Context.result value_type_2))) : (Values.store * (@Context.result value_type_2)) :=
  match var with
  | Return v => cont v
  | Exception exc => (store, Exception exc)
  | Fail f => (store, Fail f)
  end
.

(* Evaluates an expression, and calls the continuation if
* the evaluation returned a value.
* Returns the store and the variable verbatim otherwise. *)
Definition if_eval_return {value_type : Type} runs store (e : Syntax.expression) (cont : Values.store -> Values.value_loc -> (Values.store * (@Context.result value_type))) : (Values.store * (@Context.result value_type)) :=
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
Definition if_some_eval_else_default {value_type : Type} runs store (oe : option Syntax.expression) (default : Values.value_loc) (cont : Values.store -> Values.value_loc -> (Values.store * (@Context.result value_type))) : (Values.store * (@Context.result value_type)) :=
  match oe with
  | Some e => if_eval_return runs store e cont
  | None => cont store default
  end
.

(* Same as if_some_and_eval_value, but returns an option as the Context.result, and
* None is used as the default value passed to the continuation. *)
Definition if_some_eval_return_else_none {value_type : Type} runs store (oe : option Syntax.expression) (cont : Values.store -> option Values.value_loc -> (Values.store * (@Context.result value_type))) : (Values.store * (@Context.result value_type)) :=
  match oe with
  | Some e => if_eval_return runs store e (fun ctx res => cont ctx (Some res))
  | None => cont store None
  end
.

(* Calls the continuation with the referenced value. Fails if the reference
* points to a non-existing object (never actually happens). *)
Definition assert_deref {value_type : Type} store (loc : Values.value_loc) (cont : Values.value -> (Values.store * (@Context.result value_type))) : (Values.store * (@Context.result value_type)) :=
  match (get_value_from_store store loc) with
  | Some val => cont val
  | None => (store, Fail "Location of non-existing value.")
  end
.

(* Calls the continuation if the value is a location to a value (always!), and passes the value to the continuation.
* Fails otherwise. *)
Definition assert_get {value_type : Type} store (loc : Values.value_loc) (cont : Values.value -> (Values.store * (@Context.result value_type))) : (Values.store * (@Context.result value_type)) :=
  match (Values.get_value_from_store store loc) with
  | Some val => cont val
  | None => (store, Fail "Location of non-existing value.")
  end
.

(* Calls the continuation if the value is an object pointer, and passes the pointer to the continuation.
* Fails otherwise. *)
Definition assert_get_object_ptr {value_type : Type} store (loc : Values.value_loc) (cont : Values.object_ptr -> (Values.store * (@Context.result value_type))) : (Values.store * (@Context.result value_type)) :=
  match (Values.get_value_from_store store loc) with
  | Some (Values.Object ptr) => cont ptr
  | Some _ => (store, Fail "Expected an object pointer.")
  | None => (store, Fail "Location of non-existing value.")
  end
.

Definition assert_get_object_from_ptr {value_type : Type} store (ptr : Values.object_ptr) (cont : Values.object -> (Values.store * (@Context.result value_type))) : (Values.store * (@Context.result value_type)) :=
  match (Values.get_object_from_store store ptr) with
  | Some obj => cont obj
  | None => (store, Fail "Pointer to a non-existing object.")
  end
.

(* Calls the continuation if the value is an object pointer, and passes the object to the continuation *)
Definition assert_get_object {value_type : Type} store (loc : Values.value_loc) (cont : Values.object -> (Values.store * (@Context.result value_type))) : (Values.store * (@Context.result value_type)) :=
  assert_get_object_ptr store loc (fun ptr =>
    assert_get_object_from_ptr store ptr cont
  )
.

(* Calls the continuation if the value is a string.
* Fails otherwise. *)
Definition assert_get_string {value_type : Type} store (loc : Values.value_loc) (cont : string -> (Values.store * (@Context.result value_type))) : (Values.store * (@Context.result value_type)) :=
  match (get_value_from_store store loc) with
  | Some (Values.String s) => cont s
  | Some _ => (store, Fail "Expected String but did not get one.")
  | None => (store, Fail "Location of non-existing value.")
  end
.


(********* Evaluators ********)

(* a lonely identifier.
* Fetch the associated value location and return it. *)
Definition eval_id runs store (name : string) : (Values.store * Context.result) :=
  match (get_loc_from_store store name) with
  | Some v => (store, Return v)
  | None => Context.raise_exception store "ReferenceError"
  end
.


(* if e_cond e_true else e_false.
* Evaluate the condition and get the associated value, then evaluate
* e_true or e_false depending on the value. *)
Definition eval_if runs store (e_cond e_true e_false : Syntax.expression) : (Values.store * Context.result) :=
  if_eval_return runs store e_cond (fun store v =>
    match (Values.get_value_from_store store v) with
    | Some Values.True => eval_cont_terminate runs store e_true
    | Some Values.False => eval_cont_terminate runs store e_false
    | Some _ => (store, Fail "if with neither true or false")
    | None => (store, Fail "Location of non-existing value.")
    end
  )
.

(* e1 ; e2.
* Evaluate e1, then e2, and return the value location returned by e2. *)
Definition eval_seq runs store (e1 e2 : Syntax.expression) : (Values.store * Context.result) :=
  if_eval_return runs store e1 (fun store v => eval_cont_terminate runs store e2 )
.


(* A tail-recursive helper for eval_object_properties, that constructs
* the list of properties. *)
Fixpoint eval_object_properties_aux runs store (l : list (string * Syntax.property)) (acc : Values.object_properties) : (Values.store * (@Context.result Values.object_properties)) :=
  match l with
  | nil => (store, Return acc)
  | (name, Syntax.DataProperty (Syntax.Data value_expr writable) enumerable configurable) :: tail =>
    (* The order of the evaluation follows the original implementation. *)
    if_eval_return runs store value_expr (fun store value_loc =>
      eval_object_properties_aux runs store tail (Heap.write acc name (
        Values.attributes_data_of {|
            Values.attributes_data_value := value_loc;
            Values.attributes_data_writable := writable;
            Values.attributes_data_enumerable := enumerable;
            Values.attributes_data_configurable := configurable |}
      )))
  | (name, Syntax.AccessorProperty (Syntax.Accessor getter_expr setter_expr) enumerable configurable) :: tail =>
    (* The order of the evaluation follows the original implementation. *)
    if_eval_return runs store getter_expr (fun store getter_loc =>
      if_eval_return runs store setter_expr (fun store setter_loc =>
        eval_object_properties_aux runs store tail (Heap.write acc name (
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
Definition eval_object_properties runs store (l : list (string * Syntax.property)) : (Values.store * (@Context.result Values.object_properties)) :=
  eval_object_properties_aux runs store l Heap.empty
.

(* { [ attrs ] props }
* Evaluate the primval attribute (if any), then the proto attribute (defaults
* to Undefined), then properties. Finally, allocate a new object with the
* computed values. *)
Definition eval_object_decl runs store (attrs : Syntax.object_attributes) (l : list (string * Syntax.property)) : (Values.store * Context.result) :=

  match attrs with
  | Syntax.ObjectAttributes primval_expr code_expr prototype_expr class extensible =>
    (* Following the order in the original implementation: *)
    if_some_eval_return_else_none runs store primval_expr (fun store primval_loc =>
      let (store, proto_default) := Values.add_value_to_store store Values.Undefined in
      if_some_eval_else_default runs store prototype_expr proto_default (fun store prototype_loc =>
        if_some_eval_return_else_none runs store code_expr (fun store code =>
          let (store, props) := (eval_object_properties runs store l)
          in if_return store props (fun props =>
            let (store, loc) := Values.add_object_to_store store {|
                Values.object_proto := prototype_loc;
                Values.object_class := class;
                Values.object_extensible := extensible;
                Values.object_prim_value := primval_loc;
                Values.object_properties_ := props;
                Values.object_code := code_expr |}
            in (store, Context.Return loc)
          ))))
  end
.

(* left[right, args].
* Evaluate left, then right, then the arguments.
* Fails if left does not evaluate to a location of an object pointer.
* Otherwise, if the `right` attribute of the object pointed to by `left`
* is a value field, return it; and if it is an “accessor field”, call
* the getter with the arguments.
* Note the arguments are evaluated even if they are not passed to any
* function. *)
Definition eval_get_field runs store (left_expr right_expr attrs_expr : Syntax.expression) : (Values.store * Context.result) :=
  if_eval_return runs store left_expr (fun store left =>
    if_eval_return runs store right_expr (fun store right =>
      if_eval_return runs store attrs_expr (fun store attrs =>
        assert_get_object store left (fun object =>
          assert_get_string store right (fun name =>
            match (Values.get_object_property object name) with
            | Some (attributes_data_of data) => (store, Return (Values.attributes_data_value data))
            | Some (attributes_accessor_of accessor) => (store, Fail "getter not implemented.")
            | None =>
                let (store, loc) := Values.add_value_to_store store Values.Undefined
                in (store, Context.Return loc)
            end)))))
.

(* left[right, attrs] = new_val
* Evaluate left, then right, then the arguments, then the new_val.
* Fails if left does not evaluate to a location of an object pointer.
* Otherwise, if the `right` attribute of the object pointed to by `left`
* is a value field, set it to the `new_val` and return the `new_val`;
* and if it is an “accessor field”, call the getter with the arguments,
* with the `new_val` prepended to the list.
* Note the arguments are evaluated even if they are not passed to any
* function. *)
Definition eval_set_field runs store (left_expr right_expr new_val_expr attrs_expr : Syntax.expression) : (Values.store * Context.result) :=
  if_eval_return runs store left_expr (fun store left_loc =>
    if_eval_return runs store right_expr (fun store right =>
      if_eval_return runs store new_val_expr (fun store new_val =>
        if_eval_return runs store attrs_expr (fun store attrs =>
          assert_get_string store right (fun name =>
            assert_get_object_ptr store left_loc (fun left_ptr =>
              Context.update_object store left_ptr (fun object =>
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


(* let (id = expr) body
* Evaluate expr, set it to a fresh location in the store, and bind this
* location to the name `id` in the store.
* Evaluate the body in the new store. *)
Definition eval_let runs store (id : string) (value_expr body_expr : Syntax.expression) : (Values.store * Context.result) :=
  if_eval_return runs store value_expr (fun store value_loc =>
    assert_deref store value_loc (fun value =>
      let (store, loc) := Values.add_named_value_to_store store id value in
        eval_cont_terminate runs store body_expr
  ))
.

(* name := expr
* Evaluate expr, and set it at the location bound to `name`. Fail if `name`
* is not associated with a location in the store. *)
Definition eval_setbang runs store (name : string) (expr : Syntax.expression) : (Values.store * Context.result) :=
  if_eval_return runs store expr (fun store value_loc =>
    assert_deref store value_loc (fun value =>
      match (get_loc_from_store store name) with
      | Some loc => (Values.add_value_at_location store loc value, Context.Return value_loc)
      | None => Context.raise_exception store "ReferenceError"
      end
  ))
.

(* func (args) { body }
* Capture the environment's name-to-location heap and return a closure. *)
Definition eval_lambda runs store (args : list id) (body : Syntax.expression) : (Values.store * Context.result) :=
  let env := Values.loc_heap store in
  let (store, loc) := Values.add_value_to_store store (Values.Closure env args body)
  in (store, Return loc)
.


(* Evaluates all arguments, passing the store from one to the next. *)
Definition eval_arg_list_aux runs (left : (Values.store * @Context.result (list Values.value_loc))) (arg_expr : Syntax.expression) : (Values.store * @Context.result (list Values.value_loc)) :=
  let (store, res) := left in
  if_return store res (fun left_args =>
    if_eval_return runs store arg_expr (fun store arg_loc =>
      (store, Return (arg_loc :: left_args))))
.


Definition eval_arg_list runs store (args_expr : list Syntax.expression) : (Values.store * Context.result) :=
  List.fold_left (eval_arg_list_aux runs) args_expr (store, Return nil)
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

Definition make_app_store runs store (closure_env : Values.loc_heap_type) (args_name : list Values.id) (args_expr : list Syntax.expression) : (Values.store * Context.result) :=
  let (store, res) := eval_arg_list runs store args_expr in
  if_return store res (fun args =>
    match store with Values.store_intro obj_heap val_heap loc_heap stream =>
      match (make_app_loc_heap loc_heap closure_env args_name args) with
      | Some new_loc_heap =>
        (Values.store_intro obj_heap val_heap new_loc_heap stream, Context.Return 0) (* We have to return something... *)
      | None => (store, Fail "Arity mismatch")
      end
    end
  )
.


(* f (args)
* If f is a closure and there are as many arguments as the arity of f,
* call f's body with the current store, with the name-to-location map
* modified this way: for all `var`,
* * if `var` is the name of one of the arguments, then `var` maps to
*   the location of the value computed when evaluating this argument
* * else, if `var` is the name of one of the variable in f's closure,
*   then `var` maps to the location associated with in the closure.
* * else, `var` is left unchanged (ie. if it was mapped to a location,
*   it still maps to this location; and if it did not map to anything,
*   it still does not map to anything). *)
Definition eval_app runs store (f : Syntax.expression) (args_expr : list Syntax.expression) : (Values.store * Context.result) :=
  if_eval_return runs store f (fun store f_loc =>
    let (store, res) := ((Context.runs_type_get_closure runs) store f_loc) in
    if_return store res (fun f_loc =>
      assert_deref store f_loc (fun f =>
        match f with
        | Values.Closure env args_names body =>
          let (store, res) := make_app_store runs store env args_names args_expr in
          if_return store res (fun _ =>
            eval_cont_terminate runs store body
          )
        | _ => (store, Fail "Expected Closure but did not get one.")
        end
  )))
.
        
      

(******** Closing the loop *******)

(* Main evaluator *)
Definition eval runs store (e : Syntax.expression) : (Values.store * (@Context.result Values.value_loc)) :=
  let return_value := (fun v =>
    let (store, loc) := Values.add_value_to_store store v in
    (store, Context.Return loc)
  ) in
  match e with
  | Syntax.Undefined => return_value Values.Undefined
  | Syntax.String s => return_value (Values.String s)
  | Syntax.Number n => return_value (Values.Number n)
  | Syntax.True => return_value Values.True
  | Syntax.False => return_value Values.False
  | Syntax.Id s => eval_id runs store s
  | Syntax.If e_cond e_true e_false => eval_if runs store e_cond e_true e_false
  | Syntax.Seq e1 e2 => eval_seq runs store e1 e2
  | Syntax.ObjectDecl attrs l => eval_object_decl runs store attrs l
  | Syntax.GetField left_ right_ attributes => eval_get_field runs store left_ right_ attributes
  | Syntax.SetField left_ right_ new_val attributes => eval_set_field runs store left_ right_ new_val attributes
  | Syntax.Let id value body => eval_let runs store id value body
  | Syntax.SetBang id expr => eval_setbang runs store id expr
  | Syntax.Lambda args body => eval_lambda runs store args body
  | Syntax.App f args => eval_app runs store f args
  | _ => (store, Fail "not implemented")
  end
.

(* Calls a value (hopefully a function or a callable object) *)
Definition get_closure runs store (loc : Values.value_loc) : (Values.store * (@Context.result Values.value_loc)) :=
  assert_get store loc (fun v =>
    match v with
    | Values.Closure _ _ _ => (store, Context.Return loc)
    | Values.Object ptr =>
      assert_get_object_from_ptr store ptr (fun obj =>
        match (Values.object_code obj) with
        | None => (store, Fail "Applied an object without a code attribute")
        | Some loc => eval_cont_terminate runs store loc
        end
      )
    | _ => (store, Fail "Applied non-function.")
    end
  )
.


Fixpoint runs {X : Type} (runner : Context.runs_type -> Context.runner_type X) (max_steps : nat) (store : Values.store) (e : X) : (Values.store * Context.result) :=
  match (max_steps) with
  | 0 => (store, Fail "Coq is not Turing-complete")
  | S max_steps' =>
    let runners := {|
        Context.runs_type_eval := runs eval max_steps';
        Context.runs_type_get_closure := runs get_closure max_steps'
        |} in
    runner runners store e
  end
.

Definition runs_eval := runs eval.
Definition runs_get_closure := runs get_closure.
