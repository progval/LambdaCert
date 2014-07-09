Require Import List.
Require Import LibHeap.
Require Import Shared. (* jscert/coq/ *)
Require Import LibHeap. (* jscert/tlc/ *)
Module Heap := HeapGen (LibHeap.HeapList).
Open Scope list_scope.

Fixpoint concat_list_heap {X Y : Type} (front : list (X * Y)) (back : Heap.heap X Y) : Heap.heap X Y :=
  match front with
  | nil => back
  | (key, val) :: tail => concat_list_heap tail (Heap.write back key val)
  end
.
Definition concat_heaps {X Y : Type} (front back : Heap.heap X Y) :=
  concat_list_heap (Heap.to_list front) back
.


Fixpoint zip_aux {X Y : Type} (lx : list X) (ly : list Y) (acc : list (X * Y)) : option (list (X * Y)) :=
  match lx with
  | nil =>
      match ly with
      | nil => Some acc
      | _ => None
      end
  | x_head :: x_tail =>
      match ly with
      | nil => None
      | y_head :: y_tail => zip_aux x_tail y_tail ((x_head, y_head) :: acc)
      end
  end
.
Definition zip_left {X Y : Type} (lx : list X) (ly : list Y) : option (list (X * Y)) :=
  zip_aux lx ly nil
.
