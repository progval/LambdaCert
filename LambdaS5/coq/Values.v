Require Import String.

Open Scope list_scope.


Require Import LibHeap. (* jscert/tlc/ *)
Require Import Shared. (* jscert/coq/ *)
Require Import LibStream.
Module Heap := HeapGen (LibHeap.HeapList).


Require Import Syntax.


(* LambdaJS values, and object/values storage. *)


(****** Basic stuff ******)

Definition id := string.
Definition value_loc := nat.

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
   object_code : option Syntax.expression }.

Definition get_object_property (object : object) (name : prop_name) : option attributes :=
  Heap.read_option (object_properties_ object) name
.
Definition set_object_property (obj : object) (name : prop_name) (attrs : attributes) : object :=
  (* TODO: Remove the old value from the Heap (or fix LibHeap to prevent duplicates) *)
  match obj with (object_intro p c e p' props code) =>
    let props2 := Heap.write props name attrs in
    object_intro p c e p' props2 code
  end
.

Inductive value : Type :=
| Null
| Undefined
| Number : Syntax.number -> value
| String : string -> value
| True
| False
| Object : object -> value
.

(****** Store ******)

(* (The initial definitions of the sections come from JSCert.) *)

Definition value_heap_type := Heap.heap value_loc value.
Definition loc_heap_type := Heap.heap id value_loc.

Record store := store_intro {
   value_heap : value_heap_type; (* maps locations to values *)
   loc_heap : loc_heap_type; (* maps names to locations *)
   fresh_locations : stream nat }.

CoFixpoint all_locations (k:nat) : stream nat :=
  LibStream.stream_intro k (all_locations (S k)).
Definition dummy_fresh_locations := all_locations 1%nat.

Definition value_heap_initial : Heap.heap value_loc value :=
  Heap.empty.
Definition loc_heap_initial : Heap.heap id value_loc :=
  Heap.empty.

Definition create_store :=
  {| value_heap := value_heap_initial;
     loc_heap := loc_heap_initial;
     fresh_locations := dummy_fresh_locations |}.

Definition add_value_to_store (st : store) (val : value) : (store * value_loc) :=
  match st with
  | store_intro val_heap loc_heap (loc ::: stream) => (store_intro (Heap.write val_heap loc val) (loc_heap) stream, loc)
  end
.
Definition add_value_at_location (st : store) (loc : value_loc) (val : value) : store :=
  (* TODO: Remove the old value from the Heap (or fix LibHeap to prevent duplicates) *)
  match st with
  | store_intro val_heap loc_heap stream => (store_intro (Heap.write val_heap loc val) (loc_heap) stream)
  end
.
Definition add_named_value_to_store (st : store) (name : id) (val : value) : (store * value_loc) :=
  match st with
  | store_intro val_heap loc_heap (loc ::: stream) => (store_intro (Heap.write val_heap loc val) (Heap.write loc_heap name loc) stream, loc)
  end
.


Definition get_value_from_store (st : store) (loc : value_loc) : option value :=
  Heap.read_option (value_heap st) loc
.
Definition get_loc_from_store (st : store) (name : id) : option value_loc :=
  Heap.read_option (loc_heap st) name
.
