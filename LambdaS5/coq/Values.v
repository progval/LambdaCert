Require Import String.

Open Scope list_scope.


Require Import LibHeap. (* jscert/tlc/ *)
Require Import Shared. (* jscert/coq/ *)
Require Import LibStream.
Module Heap := HeapGen (LibHeap.HeapList).


Require Import Syntax.


(* LambdaJS values, and object/values storage. *)



(* Some vocabulary:
* All of LambdaJS data is passed as value location (think of locations as
* pointers), so there is an heap mapping locations to values, and optionnally
* another one mapping names to locations.
* Moreover, objects are mutable values. To emulate mutability with Coq, we
* represent objects as pointer values, and the pointer is used to fetch
* them from the objects heap. *)


(****** Basic stuff ******)

Definition id := string.
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
| Object : object_ptr -> value
| Closure : loc_heap_type -> list id -> Syntax.expression -> value
.

(****** Store ******)

(* (The initial definitions of the sections come from JSCert.) *)

Definition value_heap_type := Heap.heap value_loc value.
Definition object_heap_type := Heap.heap object_ptr object.

Record store := store_intro {
  object_heap : object_heap_type; (* simulates mutability of objects *)
  value_heap : value_heap_type; (* maps locations to values *)
  loc_heap : loc_heap_type; (* maps names to locations *)
  fresh_locations : stream nat }.

CoFixpoint all_locations (k:nat) : stream nat :=
  LibStream.stream_intro k (all_locations (S k)).
Definition dummy_fresh_locations := all_locations 1%nat.

Definition object_heap_initial : Heap.heap object_ptr object :=
  Heap.empty.
Definition value_heap_initial : Heap.heap value_loc value :=
  Heap.empty.
Definition loc_heap_initial : Heap.heap id value_loc :=
  Heap.empty.

Definition create_store :=
  {| object_heap := object_heap_initial;
     value_heap := value_heap_initial;
     loc_heap := loc_heap_initial;
     fresh_locations := dummy_fresh_locations |}.

Definition add_value_to_store (st : store) (val : value) : (store * value_loc) :=
  match st with
  | store_intro obj_heap val_heap loc_heap (loc ::: stream) =>
    (store_intro obj_heap (Heap.write val_heap loc val) loc_heap stream, loc)
  end
.
Definition add_object_to_store (st : store) (obj : object) : (store * value_loc) :=
  match st with
  | store_intro obj_heap val_heap loc_heap (loc ::: (ptr ::: stream)) =>
    ((store_intro
      (Heap.write obj_heap ptr obj)
      (Heap.write val_heap loc (Object ptr))
      loc_heap
      stream
    ), loc)
  end
.
Definition add_value_at_location (st : store) (loc : value_loc) (val : value) : store :=
  (* TODO: Remove the old value from the Heap (or fix LibHeap to prevent duplicates) *)
  match st with
  | store_intro obj_heap val_heap loc_heap stream => (store_intro obj_heap (Heap.write val_heap loc val) (loc_heap) stream)
  end
.
Definition add_named_location_to_store (st : store) (name : id) (loc : value_loc) : store :=
  match st with
  | store_intro obj_heap val_heap loc_heap stream =>
    store_intro obj_heap val_heap (Heap.write loc_heap name loc) stream
  end
.
Definition add_named_value_to_store (st : store) (name : id) (val : value) : (store * value_loc) :=
  match st with
  | store_intro obj_heap val_heap loc_heap (loc ::: stream) => (store_intro obj_heap (Heap.write val_heap loc val) (Heap.write loc_heap name loc) stream, loc)
  end
.
Definition update_object (st : store) (ptr : object_ptr) (new_obj : object) : store :=
  (* TODO: Remove the old object from the Heap (or fix LibHeap to prevent duplicates) *)
  match st with
  | store_intro obj_heap val_heap loc_heap stream => (store_intro (Heap.write obj_heap ptr new_obj) val_heap (loc_heap) stream)
  end
.


Definition get_object_from_store (st : store) (ptr : object_ptr) : option object :=
  Heap.read_option (object_heap st) ptr
.
Definition get_value_from_store (st : store) (loc : value_loc) : option value :=
  Heap.read_option (value_heap st) loc
.
Definition get_loc_from_store (st : store) (name : id) : option value_loc :=
  Heap.read_option (loc_heap st) name
.
