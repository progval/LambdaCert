Add LoadPath "../../jscert/coq/".
Add LoadPath "../../jscert/tlc/".
Add Rec LoadPath "../../jscert/flocq/src/" as Flocq.
Require Import String.
Require Import Store.
Require Import Values.
Require Import Context.
Require Import HeapUtils.
Require Import Interpreter.
Require Import LibNat.
Module Heap := Values.Heap.


(******** Definitions ********)

Definition ok_loc st loc :=
  Heap.indom (Store.value_heap st) loc
.
Definition ok_loc_option st loc_option :=
  match loc_option with
  | Some loc => ok_loc st loc
  | None => Logic.True
  end
.

Definition all_locs_exist (st : Store.store) : Prop :=
  forall (i : Values.id) l,
  Heap.binds (Store.loc_heap st) i l ->
  ok_loc st l
.

Inductive result_value_loc_exists {value_type : Type} (ok : Store.store -> value_type -> Prop) (st : store) : (@Context.result value_type) -> Prop :=
  | result_value_loc_exists_return : forall (v : value_type),
      ok st v ->
      result_value_loc_exists ok st (Return v)
  | result_value_loc_exists_exception : forall (l : Values.value_loc),
      ok_loc st l ->
      result_value_loc_exists ok st (Exception l)
  | result_value_loc_exists_break : forall (b : string) (l : Values.value_loc),
      ok_loc st l ->
      result_value_loc_exists ok st (Break b l)
  | result_value_loc_exists_fail : forall (s : string),
      result_value_loc_exists ok st (Fail s)
.

(******** Consistency of Store operations ********)

Lemma get_loc_returns_valid_loc :
  forall st name,
  all_locs_exist st ->
  ok_loc_option st (get_loc st name)
.
Proof.
  intros st name IH.
  unfold get_loc.
    rewrite Heap.read_option_def.
    destruct LibLogic.classicT as [in_dom|not_in_dom].
      (* If the name has been found. *)
      simpl.
      assert (binds_equiv_read_name: forall v, (Heap.binds (loc_heap st) name v) -> (Heap.read (loc_heap st) name = v)).
        intros v name_bound_to_v.
        rewrite <- Heap.binds_equiv_read.
          apply name_bound_to_v.

          apply in_dom.

        unfold all_locs_exist in IH.
        rewrite Heap.indom_equiv_binds in in_dom.
        destruct in_dom as (x, x_in_dom).
        assert (x_in_dom_dup: Heap.binds (loc_heap st) name x).
          apply x_in_dom.

          apply IH in x_in_dom_dup.
          specialize (binds_equiv_read_name x).
          assert (read_equals_x: Heap.read (loc_heap st) name = x).
            apply binds_equiv_read_name.
            apply x_in_dom.

            rewrite <-read_equals_x in x_in_dom_dup.
            apply x_in_dom_dup.

      (* If the name has not been found *)
      unfold ok_loc_option.
      apply I.
Qed.


Lemma add_value_preserves_store_consistency :
  forall (st : Store.store) (v : Values.value),
  all_locs_exist st ->
  let (st2, loc) := Store.add_value st v in
  all_locs_exist st2
.
Proof.
  intros st v IH.
  unfold add_value.
  destruct st.
  destruct fresh_locations.
  unfold all_locs_exist.
  simpl.
  intros i l H.
  apply IH in H.
  unfold ok_loc.
  simpl.
  unfold ok_loc in H.
  simpl in H.
  apply HeapUtils.write_preserves_indom.
    apply LibNat.nat_comparable.

    apply H.
Qed.

Lemma add_value_returns_existing_value_loc :
  forall (st : Store.store) (v : Values.value),
  all_locs_exist st ->
  let (st2, loc) := Store.add_value st v in
  ok_loc st2 loc
.
Proof.
  intros st v IH.
  unfold add_value.
  unfold ok_loc.
  destruct st.
  destruct fresh_locations.
  simpl.
  rewrite Heap.indom_equiv_binds.
  exists v.
  apply Heap.binds_write_eq.
Qed.

Lemma add_value_return_preserves_all_locs_exist :
  forall (st : Store.store) (v : Values.value),
  all_locs_exist st ->
  let (st2, res) := Context.add_value_return st v in
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res
.
Proof.
  intros st v IH.
  unfold add_value_return.
  destruct (let (store, loc) := add_value st v in (store, Return loc)) as (store, res) eqn: store_loc_def.
  split.
    (* Store is consistent *)
    destruct (add_value st v) eqn:H.
    inversion store_loc_def.
    rewrite <-H1.
    assert (let (s, v0) := Store.add_value st v in all_locs_exist s).
      apply add_value_preserves_store_consistency.
      apply IH.

      rewrite H in H0.
      apply H0.

    (* Returned location exists. *)
    destruct res eqn:v0_def.
      (* Result *)
      apply result_value_loc_exists_return.
      assert (H: (store, v0) = add_value st v).
        destruct (add_value st v).
        inversion store_loc_def.
        auto.
        
        assert (H0: let (s, v0) := Store.add_value st v in ok_loc s v0).
          apply add_value_returns_existing_value_loc.
          apply IH.

          rewrite <-H in H0.
          apply H0.

      (* Exception *)
      destruct (add_value st v).
      inversion store_loc_def.

      (* Break *)
      destruct (add_value st v).
      inversion store_loc_def.

      (* Fail *)
      destruct (add_value st v).
      inversion store_loc_def.
Qed.

(******** Consistency of evaluators ********)

Lemma eval_id_preserves_all_locs_exist :
  forall runs st name,
  all_locs_exist st ->
  let (st2, res) := Interpreter.eval_id runs st name in
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res
.
Proof.
  intros runs st name IH.
  unfold eval_id.
  destruct (get_loc st name) as [l|l] eqn: l_def.
    (* If the name exists *)
    split.
      (* Store is unchanged, so it is still consistent. *)
      apply IH.

      (* Proof that we return an existing location. *)
      apply result_value_loc_exists_return.
      unfold all_locs_exist in IH.
      apply (IH name).
      rewrite Heap.binds_equiv_read_option.
      unfold get_loc in l_def.
      apply l_def.

    (* If the name does not exist. *)
    split.
      (* Store is unchanged. *)
      apply IH.

      (* We are not returning a location, it this is consistent. *)
      apply result_value_loc_exists_fail.
Qed.



(******** Conclusions *********)

Theorem eval_preserves_all_locs_exist :
  forall max_steps (st : Store.store),
  forall st (e : Syntax.expression),
  all_locs_exist st ->
  let (st2, res) := Interpreter.eval max_steps st e in
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res
.
Proof.
  intros max_steps st0 st1 e IH.
  destruct e; unfold eval;
    (* Null, Undefined, String, Number, True, False. *)
    try apply add_value_return_preserves_all_locs_exist; try apply IH.

    (* Id *)
    apply eval_id_preserves_all_locs_exist; apply IH.

Admitted.

Theorem runs_preserves_all_locs_exist :
  forall max_steps (st : Store.store),
  forall runner st (e : Syntax.expression),
  all_locs_exist st ->
  let (st2, res) := Interpreter.runs runner max_steps st e in
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res
.
Admitted.
