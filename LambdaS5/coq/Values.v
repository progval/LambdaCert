Require Import String.

Open Scope list_scope.


Require Import LibHeap. (* jscert/tlc/ *)
Require Import Shared. (* jscert/coq/ *)
Require Import LibStream.
Module Heap := HeapGen (LibHeap.HeapList).


Require Import Syntax.


(* LambdaJS values, and object/values storage. *)

(* Values are not to be confused with objects.
* Values are all of basic data types (either a constant constructor
* or a string/integer). They can be a location to an object (you can
* think of locations as references).
* An object is a collection of data with lots of metadata.
*)


(****** Basic stuff ******)

Definition id := string.
Definition object_loc := nat.

Inductive value : Type :=
| Null
| Undefined
| Number : Syntax.number -> value
| String : string -> value
| True
| False
| ObjectLoc : object_loc -> value
.

(****** Objects ******)

(* (The code in this section comes mostly from JSCert.) *)

(* Named data property attributes *)
Record attributes_data := attributes_data_intro {
   attributes_data_value : value;
   attributes_data_writable : bool;
   attributes_data_enumerable : bool;
   attributes_data_configurable : bool }.

(* Named accessor property attributes *)
Record attributes_accessor := attributes_accessor_intro {
   attributes_accessor_get : value;
   attributes_accessor_set : value;
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
   object_proto : value;
   object_class : class_name;
   object_extensible : bool;
   object_prim_value : option value;
   object_properties_ : object_properties;
   object_code : option Syntax.expression }.

Definition get_object_property (object : object) (name : prop_name) : option attributes :=
  Heap.read_option (object_properties_ object) name
.

(****** Store ******)

(* (The initial definitions of the sections come from JSCert.) *)

Definition object_heap_type := Heap.heap object_loc object.
Definition value_heap_type := Heap.heap id value.

Record store := store_intro {
   object_heap : object_heap_type;
   value_heap : value_heap_type;
   fresh_locations : stream nat }.

CoFixpoint all_locations (k:nat) : stream nat :=
  LibStream.stream_intro k (all_locations (S k)).
Definition dummy_fresh_locations := all_locations 1%nat.

Definition object_heap_initial : Heap.heap object_loc object:=
  Heap.empty.
Definition value_heap_initial : Heap.heap id value:=
  Heap.empty.

Definition create_store :=
  {| object_heap := object_heap_initial;
     value_heap := value_heap_initial;
     fresh_locations := dummy_fresh_locations |}.

Definition add_object_to_store (st : store) (object : Values.object) : (store * object_loc) :=
  match st with
  | store_intro obj_heap val_heap (loc ::: stream) => (store_intro (Heap.write obj_heap loc object) (val_heap) stream, loc)
  end
.
Definition add_value_to_store (st : store) (name : id) (val : Values.value) : store :=
  match st with
  | store_intro obj_heap val_heap stream => store_intro obj_heap (Heap.write val_heap name val) stream
  end
.

Definition get_object_from_store (st : store) (loc : object_loc) : option object :=
  Heap.read_option (object_heap st) loc
.
Definition get_value_from_store (st : store) (name : id) : option value :=
  Heap.read_option (value_heap st) name
.
