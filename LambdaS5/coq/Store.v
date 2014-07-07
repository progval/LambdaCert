Require Import Values.
Require Import LibStream.

Module Heap := Values.Heap.

(* LambdaJS environment storage. *)

(* (The initial definitions of this file come from JSCert.) *)

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

Definition add_value (st : store) (val : value) : (store * value_loc) :=
  match st with
  | store_intro obj_heap val_heap loc_heap (loc ::: stream) =>
    (store_intro obj_heap (Heap.write val_heap loc val) loc_heap stream, loc)
  end
.
Definition add_object (st : store) (obj : object) : (store * value_loc) :=
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
Definition add_named_location (st : store) (name : id) (loc : value_loc) : store :=
  match st with
  | store_intro obj_heap val_heap loc_heap stream =>
    store_intro obj_heap val_heap (Heap.write loc_heap name loc) stream
  end
.
Definition add_named_value (st : store) (name : id) (val : value) : (store * value_loc) :=
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
Definition add_option_value st (oval : option value) : (store * option Values.value_loc) :=
  match oval with
  | Some val => let (st, loc) := add_value st val in (st, Some loc)
  | None => (st, None)
  end
.



Definition get_object (st : store) (ptr : object_ptr) : option object :=
  Heap.read_option (object_heap st) ptr
.
Definition get_value (st : store) (loc : value_loc) : option value :=
  Heap.read_option (value_heap st) loc
.
Definition get_loc  (st : store) (name : id) : option value_loc :=
  Heap.read_option (loc_heap st) name
.

(* Returns the value associated to a variable name (aka. id) in the current
* context. *)
Definition get_value_of_name store (name : Values.id) : option Values.value :=
  match (get_loc store name) with
  | Some loc => get_value store loc
  | None => None
  end
.

