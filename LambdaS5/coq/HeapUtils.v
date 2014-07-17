Require Import Shared.
Require Import LibHeap.
Require Import LibTactics.
Require Import LibReflect.

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

Lemma binds_write_inv_val_neq : forall X Y (h : Heap.heap X Y) k v k' v',
  Heap.binds (Heap.write h k' v') k v -> v <> v' ->
  Heap.binds h k v
.
Proof.
  intros X Y h k v k' v' IH v_neq_v'.
  apply Heap.binds_write_inv in IH.
  destruct IH as [H|H].
    destruct H as (H_keys,H_values).
    apply v_neq_v' in H_values.
    contradiction.

    destruct H as (H_keys,H_binds).
    apply H_binds.
Qed.

