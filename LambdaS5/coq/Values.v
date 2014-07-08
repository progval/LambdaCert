Require Import Utils.
Require Import String.
Open Scope list_scope.
Module Heap := Utils.Heap.




Require Import Syntax.


(* LambdaJS values and objects *)



(* Some vocabulary:
* All of LambdaJS data is passed as value location (think of locations as
* pointers), so there is an heap mapping locations to values, and optionnally
* another one mapping names to locations.
* Moreover, objects are mutable values. To emulate mutability with Coq, we
* represent objects as pointer values, and the pointer is used to fetch
* them from the objects heap. *)


(****** Basic stuff ******)

Definition id := string.
Definition closure_id := nat.
Definition value_loc := nat.
Definition object_ptr := nat.

Definition loc_heap_type := Heap.heap id value_loc.

(****** Objects ******)

(* (The code in this section comes mostly from JSCert.) *)

(* Named data property attributes *)
Record attributes_data := attributes_data_intro {
   attributes_data_value : value_loc;
   attributes_data_writable : bool;
   attributes_data_enumerable : bool;
   attributes_data_configurable : bool }.

(* Named accessor property attributes *)
Record attributes_accessor := attributes_accessor_intro {
   attributes_accessor_get : value_loc;
   attributes_accessor_set : value_loc;
   attributes_accessor_enumerable : bool;
   attributes_accessor_configurable : bool }.

(* Property attributes *)
Inductive attributes :=
  | attributes_data_of : attributes_data -> attributes
  | attributes_accessor_of : attributes_accessor -> attributes.


Definition prop_name := string.
Definition class_name := string.
Definition object_properties := Heap.heap prop_name attributes.

Record object := object_intro {
   object_proto : value_loc;
   object_class : class_name;
   object_extensible : bool;
   object_prim_value : option value_loc;
   object_properties_ : object_properties;
   object_code : option value_loc }.

Definition get_object_property (object : object) (name : prop_name) : option attributes :=
  Heap.read_option (object_properties_ object) name
.
Definition set_object_property (obj : object) (name : prop_name) (attrs : attributes) : object :=
  let key_equal_pred := (fun x => match x with (k, _) => (if (String.string_dec k name) then false else true) end) in
  match obj with (object_intro p c e p' props code) =>
    let props2 := Heap.write (Utils.heap_filter props key_equal_pred) name attrs in
    object_intro p c e p' props2 code
  end
.

(******* Finally, values. *******)

Inductive value : Type :=
| Null
| Undefined
| Number : Syntax.number -> value
| String : string -> value
| True
| False
| Object : object_ptr -> value
| Closure : closure_id -> loc_heap_type -> list id -> Syntax.expression -> value (* closure_id is for making closures comparable with stx= *)
.

