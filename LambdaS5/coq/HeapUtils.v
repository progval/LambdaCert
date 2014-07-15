Require Import Shared.
Require Import LibHeap.
Require Import LibTactics.
Require Import LibReflect.
Require Import Coq.Arith.EqNat.

Module Heap := HeapGen (LibHeap.HeapList).

Lemma write_preserves_indom : forall (X Y : Type) (h : Heap.heap X Y) k k0 v0,
  LibReflect.Comparable X -> Heap.indom h k -> Heap.indom (Heap.write h k0 v0) k
.
Proof.
  intros X Y h k k0 v0 H0 H.
  rewrite Heap.indom_equiv_binds.
  rewrite Heap.indom_equiv_binds in H.
  destruct H as (v&Hv).
  cases (LibReflect.decide (k=k0)). (* LibTactics.cases *)
    fold_bool. (* LibReflect.fold_bool *)
    rew_refl in Eq. (* LibReflect.rew_refl *)
    rewrite Eq.
    exists v0.
    apply Heap.binds_write_eq.

    fold_bool.
    rew_refl in Eq.
    exists v.
    generalize Eq.
    apply Heap.binds_write_neq.
    apply Hv.
Qed.



Lemma nat_comparable : Comparable nat.
Proof.
  apply (comparable_beq beq_nat).
  auto.
  intros x y.
  split.
    intro H.
    apply beq_nat_true.
    apply H.

    intro H.
    assert (beq_nat x y = true).
      apply beq_nat_true_iff.
      apply H.

      apply H0.
Qed.
