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
Require Import LibLogic.
Require Import LibTactics.
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
  forall (st st2 : Store.store) (v : Values.value) loc,
  all_locs_exist st ->
  Store.add_value st v = (st2, loc) ->
  all_locs_exist st2
.
Proof.
  intros st st2 v loc IH st2_def.
  unfold add_value.
  destruct st.
  destruct fresh_locations.
  unfold all_locs_exist.
  simpl.
  intros i l H.
  unfold ok_loc.
  unfold add_value in st2_def.
  inversion st2_def.
  simpl.
  tests: (l=n).
    rewrite Heap.indom_equiv_binds.
    exists v.
    rewrite H2.
    apply Heap.binds_write_eq.

    unfold all_locs_exist in IH.
    simpl in IH.
    unfold ok_loc in IH.
    simpl in IH.
    apply HeapUtils.write_preserves_indom.
      apply LibNat.nat_comparable.

      rewrite <-H1 in H.
      simpl in H.
      eapply IH.
      apply H.
Qed.

Lemma add_value_returns_existing_value_loc :
  forall (st st2 : Store.store) (v : Values.value) loc,
  all_locs_exist st ->
  Store.add_value st v = (st2, loc) ->
  ok_loc st2 loc
.
Proof.
  intros st st2 v IH loc.
  unfold add_value.
  unfold ok_loc.
  destruct st.
  destruct fresh_locations.
  simpl.
  rewrite Heap.indom_equiv_binds.
  exists v.
  inversion H.
  apply Heap.binds_write_eq.
Qed.

Lemma add_value_return_preserves_all_locs_exist :
  forall (st st2: Store.store) res (v : Values.value),
  all_locs_exist st ->
  Context.add_value_return st v = (st2, res) ->
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res
.
Proof.
  intros st st2 res v IH H.
  unfold add_value_return.
  split.
    (* Store is consistent *)
    unfold add_value_return in H.
    destruct res in H.
      (* Return *)
      assert (add_value st v = (st2, v0)).
        destruct (add_value st v) eqn:H'.
        inversion H.
        reflexivity.
        
        eapply add_value_preserves_store_consistency.
          apply IH.

          apply H0.

      (* Exception *)
      destruct (add_value st v) in H.
      inversion H.

      (* Break *)
      destruct (add_value st v) in H.
      inversion H.

      (* Fail *)
      destruct (add_value st v) in H.
      inversion H.


    (* Returned location exists. *)
    destruct res eqn:v0_def.
      (* Return *)
      apply result_value_loc_exists_return.
      unfold add_value_return in H.
      assert (add_value st v = (st2, v0)).
        destruct (add_value st v) eqn:H'.
        inversion H.
        reflexivity.

        eapply add_value_returns_existing_value_loc.
          apply IH.

          apply H0.

      (* Exception *)
      unfold add_value_return in H.
      destruct (add_value st v) in H.
      inversion H.

      (* Break *)
      unfold add_value_return in H.
      destruct (add_value st v) in H.
      inversion H.

      (* Fail *)
      unfold add_value_return in H.
      destruct (add_value st v) in H.
      inversion H.
Qed.

Lemma add_object_preserves_store_consistant :
  forall st st2 obj loc,
  (st2, loc) = Store.add_object st obj ->
  all_locs_exist st2
.
Admitted.

Lemma add_object_preserves_all_locs_exist :
  forall st st2 obj loc,
  Store.add_object st obj = (st2, loc) ->
  all_locs_exist st2 /\ ok_loc st2 loc
.
Admitted.

(******** Consistency of monads ********)

Lemma monad_ec_preserves_all_locs_exist :
  forall runs st st2 e (cont : Store.store -> Context.result -> (Store.store * Context.result)) res2,
  all_locs_exist st ->
  (forall st0 res0, let (st1, res) := cont st0 res0 in
    all_locs_exist st1 /\ result_value_loc_exists ok_loc st1 res) ->
  Monads.eval_cont runs st e cont = (st2, res2) ->
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res2
.
Admitted.

Lemma monad_ect_preserves_all_locs_exist :
  forall runs st st2 e res2,
  all_locs_exist st ->
  Monads.eval_cont_terminate runs st e = (st2, res2) ->
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res2
.
Admitted.

Lemma monad_ir_preserves_all_locs_exist (X : Type) :
  forall st st2 (var : X) res (cont : X -> (Store.store * (@Context.result Values.value_loc))) res2,
  all_locs_exist st ->
  (forall res0 st1 res,
    cont res0 = (st1, res) ->
    all_locs_exist st1 /\ result_value_loc_exists ok_loc st1 res) ->
  Monads.if_return st res cont = (st2, res2) ->
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res2
.
Admitted.

Lemma monad_iseren_preserves_all_locs_exist :
  forall runs st st2 opt (cont : Store.store -> option Values.value_loc -> (Store.store * Context.result)) res2,
  all_locs_exist st ->
  (forall st0 oloc0 st1 res, all_locs_exist st0 ->
    cont st0 oloc0 = (st1, res) ->
    all_locs_exist st1 /\ result_value_loc_exists ok_loc st1 res) ->
  Monads.if_some_eval_return_else_none runs st opt cont = (st2, res2) ->
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res2
.
Admitted.

Lemma monad_iseed_preserves_all_locs_exist :
  forall runs st st2 opt default (cont : Store.store -> Values.value_loc -> (Store.store * Context.result)) res2,
  all_locs_exist st ->
  (forall st0 loc0 st1 res, all_locs_exist st0 ->
    cont st0 loc0 = (st1, res) ->
    all_locs_exist st1 /\ result_value_loc_exists ok_loc st1 res) ->
  Monads.if_some_eval_else_default runs st opt default cont = (st2, res2) ->
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res2
.
Admitted.

(******** Consistency of evaluators ********)

Lemma eval_id_preserves_all_locs_exist :
  forall runs st name st2 res,
  all_locs_exist st ->
  Interpreter.eval_id runs st name = (st2, res) ->
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res
.
Proof.
  intros runs st name st2 res IH.
  unfold eval_id.
  destruct (get_loc st name) as [l|l] eqn: l_def.
    (* If the name exists *)
    split.
      (* Store is unchanged, so it is still consistent. *)
      inversion H.
      rewrite <-H1.
      apply IH.

      (* Proof that we return an existing location. *)
      inversion H.
      apply result_value_loc_exists_return.
      unfold all_locs_exist in IH.
      rewrite <-H1.
      apply (IH name).
      rewrite Heap.binds_equiv_read_option.
      unfold get_loc in l_def.
      apply l_def.

    (* If the name does not exist. *)
    split.
      (* Store is unchanged. *)
      inversion H.
      rewrite <-H1.
      apply IH.

      (* We are not returning a location, it this is consistent. *)
      inversion H.
      apply result_value_loc_exists_fail.
Qed.

Lemma eval_object_properties_preserves_all_locs_exist :
  forall runs st st2 props props2,
  all_locs_exist st ->
  eval_object_properties runs st props = (st2, props2) ->
  all_locs_exist st2
.
Admitted.

(* TODO: We will have to prove the added locations exist too… *)
Lemma eval_objectdecl_preserves_all_locs_exist :
  forall runs st st2 attrs props res,
  all_locs_exist st ->
  Interpreter.eval_object_decl runs st attrs props = (st2, res) ->
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res
.
Proof.
  intros runs st st2 attrs props res IH.
  unfold eval_object_decl.
  destruct attrs.
  apply monad_iseren_preserves_all_locs_exist.
    apply IH.

    intros st0 oloc0 st1 res0.
    destruct (add_value st0 Undefined) eqn:store_def.
    intro st0_consistant.
    apply monad_iseed_preserves_all_locs_exist.
      apply add_value_preserves_store_consistency in store_def.
      apply store_def.
      apply st0_consistant.

     intros st3 loc0 st4 res1 st3_consistant. 
     apply monad_iseren_preserves_all_locs_exist.
      apply st3_consistant.

      intros st5 oloc1 st6 res2 st5_consistant.
      destruct (eval_object_properties runs st5 props) eqn:store_def2.
      apply (monad_ir_preserves_all_locs_exist object_properties).
        apply Heap.empty.

        eapply eval_object_properties_preserves_all_locs_exist.
          apply st5_consistant.

          apply store_def2.

        intros res3 st7 res4.
        destruct (add_object s1
          {|
          object_proto := loc0;
          object_class := s;
          object_extensible := b;
          object_prim_value := oloc0;
          object_properties_ := res3;
          object_deleted_properties := nil;
          object_code := oloc1 |}) eqn:st3_def.
        split.
          eapply add_object_preserves_store_consistant.
          symmetry.
          inversion H.
          rewrite <-H1.
          apply st3_def.

          inversion H.
          rewrite <-H1.
          apply result_value_loc_exists_return.
          eapply add_object_preserves_all_locs_exist.
          apply st3_def.
Qed.


(******** Conclusions *********)

Theorem eval_preserves_all_locs_exist :
  forall runs (st st2 : Store.store) res,
  forall st (e : Syntax.expression),
  all_locs_exist st ->
  Interpreter.eval runs st e = (st2, res) ->
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res
.
Proof.
  intros runs st st2 res st0 e IH H.
  destruct e; unfold eval; simpl;
    (* Null, Undefined, String, Number, True, False. *)
    try solve [applys* add_value_return_preserves_all_locs_exist].

    (* Id *)
    applys* eval_id_preserves_all_locs_exist.

    (* ObjectDecl *)
    applys* eval_objectdecl_preserves_all_locs_exist.

Admitted.

Theorem runs_preserves_all_locs_exist :
  forall max_steps (st : Store.store),
  forall runner st (e : Syntax.expression),
  all_locs_exist st ->
  let (st2, res) := Interpreter.runs runner max_steps st e in
  all_locs_exist st2 /\ result_value_loc_exists ok_loc st2 res
.
Admitted.
