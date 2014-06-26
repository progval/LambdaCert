Require Import String.

Open Scope list_scope.


Require Import LibHeap. (* jscert/tlc/ *)
Require Import Shared. (* jscert/coq/ *)
Require Import LibStream.
Module Heap := HeapGen (LibHeap.HeapList).


Require Import Syntax.

Definition env_loc := nat.
Definition lexical_env := list env_loc.

Record store := store_intro {
   (* object_heap : Heap.heap object_loc object;
   env_record_heap : Heap.heap env_loc env_record; *)
   fresh_locations : stream nat }.

CoFixpoint all_locations (k:nat) : stream nat :=
  LibStream.stream_intro k (all_locations (S k)).
Definition dummy_fresh_locations := all_locations 1%nat.

Definition create_store :=
  {| (*object_heap := object_heap_initial;
     env_record_heap := env_record_heap_initial;*)
     fresh_locations := dummy_fresh_locations |}.

Inductive value : Type :=
| Null
| Undefined
| Number : Syntax.number -> value
| String : string -> value
| True
| False
.

