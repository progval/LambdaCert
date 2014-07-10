Require Import List.
Require Import Ascii.
Require Import String.
Require Import LibHeap.
Require Import Shared. (* jscert/coq/ *)
Require Import LibHeap. (* jscert/tlc/ *)
Require Import JsNumber.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Module Heap := HeapGen (LibHeap.HeapList).
Open Scope list_scope.
Open Scope string_scope.
Open Scope char_scope.

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

Definition ascii_of_nat (a : nat) : ascii :=
  match (a mod 10) with
  | 0=>"0" | 1=>"1" | 2=>"2" | 3=>"3" | 4=>"4"
  | 5=>"5" | 6=>"6" | 7=>"7" | 8=>"8" | 9=>"9"
  | _=>"A"
  end
.
Fixpoint string_of_nat_aux (fuel n : nat) (acc : string) : option string :=
  match (fuel, n) with
  | (_, 0) => Some acc
  | (0, _) => None
  | (S fuel', _) => string_of_nat_aux fuel' (n / 10) (String.String (ascii_of_nat n) acc)
  end
.
Definition string_of_nat (fuel n : nat) : option string :=
  match n with
  | 0 => string_of_nat_aux fuel 0 "0"
  | _ => string_of_nat_aux fuel n ""
  end
.

Definition make_number (n : nat) : JsNumber.number :=
  Fappli_IEEE.binary_normalize 53 1024 eq_refl eq_refl Fappli_IEEE.mode_NE n 0 false.
