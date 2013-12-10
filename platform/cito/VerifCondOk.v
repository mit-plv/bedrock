Require Import CompileStmtSpec CompileStmtImpl.

Set Implicit Arguments.

Section TopSection.

  Require Import Inv.

  Variable layout : Layout.

  Variable vars : list string.

  Variable temp_size : nat.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Require Import Syntax.
  Require Import Wrap.

  Definition compile := compile layout vars temp_size imports_global modName.

  Lemma verifCond_ok : 
    forall (s k : Stmt) (pre : assert),
      vcs (verifCond layout vars temp_size s k pre) ->
      vcs
        (VerifCond (compile s k pre)).
  Proof.

    Require Import Semantics.
    Require Import Safe.
    Require Import Notations.
    Require Import SemanticsFacts.
    Require Import ScopeFacts.
    Require Import ListFacts.
    Require Import StringSet.
    Require Import SetFacts.
    Require Import CompileStmtTactics.

    Open Scope stmt.

    Opaque funcs_ok.
    Opaque mult.
    Opaque star. (* necessary to use eapply_cancel *)

    Hint Resolve Subset_in_scope_In.
    Hint Extern 0 (Subset _ _) => progress (simpl; subset_solver).

    unfold verifCond, imply; induction s.

    Focus 5.

    Set Printing Coercions.

    Require Import SemanticsExpr.
    Require Import SepHints.
    Require Import GeneralTactics.
    Require Import WordFacts.
    Require Import Arith.
    Require Import InvFacts.

    Open Scope nat.

    Ltac hide_upd_sublist :=
      repeat match goal with
               | H : context [ upd_sublist ?L _ _ ] |- _ => set (upd_sublist L _ _) in *
             end.

    Hint Resolve map_length.

    Lemma replace1 : forall a b c d e : W, a ^+ b ^+ c ^+ d ^+ e = a ^+ (b ^+ c ^+ d ^+ e).
      intros; repeat rewrite wplus_assoc in *; eauto.
    Qed.

    Lemma replace_it3 : forall a b, 2 <= a -> b <= a - 2 -> $(a) ^- $(S (S b)) = natToW (a - 2 - b).
      intros; replace (a - 2 - b) with (a - (2 + b)) by omega; rewrite natToW_minus; eauto.
    Qed.

    Ltac inversion_Safe :=
      repeat match goal with
               | H : Safe _ _ _ |- _ => inversion H; clear H; subst
             end.
    
    Transparent funcs_ok.
    Ltac unfold_funcs_ok :=
      match goal with 
        | H : interp _ (funcs_ok _ _ _) |- _ => generalize H; intro is_funcs_ok; unfold funcs_ok in H
      end.
    Opaque funcs_ok.

    Ltac specialize_funcs_ok :=
      match goal with
        | H : context [ (_ ---> _)%PropX ], H2 : _ = Some _ |- _ => 
          specialize (Imply_sound (H _ _) (Inj_I _ _ H2)); propxFo
      end.

    Lemma map_eq_length_eq : forall A B C (f1 : A -> B) ls1 (f2 : C -> B) ls2, map f1 ls1 = map f2 ls2 -> length ls1 = length ls2.
      intros; assert (length (map f1 ls1) = length (map f2 ls2)) by congruence; repeat rewrite map_length in *; eauto.
    Qed.

    Ltac hide_map :=
      repeat match goal with
               | H : context [ map ?A _ ] |- _ => set (map A _) in *
             end.

    Ltac auto_apply :=
      match goal with
          H : _ |- _ => eapply H
      end.

    (* call *)
    wrap0.

    Focus 8.

    (* vc 8 *)
    eapply H2 in H3.
    unfold precond, inv, inv_template, is_state in *.
    unfold has_extra_stack in *.
    post.
    unfold stack_slot in *.
    rewrite fold_4_mult_1 in *.
    hide_Safe.
    hiding ltac:(evaluate auto_ext).
    destruct_state.
    unfold CompileExprs.runs_to in *.
    unfold CompileExprs.is_state in *.
    simpl in *.
    hide_evalInstrs.
    assert (2 <= x8) by admit.
    hide_Safe.
    hiding ltac:(evaluate hints_buf_2_fwd).
    hiding ltac:(evaluate hints_array).
    unfold callee_stack_start in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    rewrite H in *.
    rewrite <- H9 in *.
    rewrite fold_4_mult_2 in *.
    rewrite Mult.mult_plus_distr_l in *.
    rewrite_natToW_plus.
    repeat rewrite natToW_plus in H6.
    repeat rewrite wplus_assoc in *.
    transit.
    post.
    unfold CompileExpr.runs_to in *.
    unfold CompileExpr.is_state in *.
    simpl in *.
    set (upd_sublist x6 _ _) in *.
    set (upd_sublist x11 _ _) in *.
    transit.
    post.
    unfold callee_stack_slot in *.
    unfold callee_stack_start in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    rewrite fold_4_mult_1 in *.
    rewrite fold_4_mult_2 in *.
    rewrite_natToW_plus.
    repeat rewrite wplus_assoc in *.
    rewrite <- H18 in *.
    rewrite <- H20 in *.
    repeat rewrite replace1 in H22.
    hide_all_eq_except H6.
    hiding ltac:(evaluate auto_ext).
    intros.
    inversion_Safe.

    (* internal *)
    unfold_all.
    simpl in *.
    Transparent funcs_ok.
    unfold_funcs_ok.
    Opaque funcs_ok.
    simpl in *.
    repeat rewrite wplus_assoc in *.
    post.
    specialize_funcs_ok.
    descend.
    rewriter.
    eauto.
    hiding ltac:(step auto_ext).
    hide_upd_sublist.
    Require Import SepHints2.
    rewrite (@replace_array_to_split l2 _ (length l)) in H7.
    assert (splittable l2 (length l)) by admit.
    hiding ltac:(evaluate hints_array_split).
    fold (@firstn W) in *.
    fold (@skipn W) in *.
    rewrite fold_4_mult in *.
    unfold_all.
    erewrite firstn_upd_sublist in * by eauto.
    erewrite skipn_upd_sublist in * by eauto.

    set (map _ _) in *.
    set (ArgVars _) in *.
    Require Import SepHints3.
    rewrite (@replace_array_to_locals l0 _ l1) in H35.
    assert (array_to_locals_ok l0 l1) by admit.
    hiding ltac:(evaluate hints_array_to_locals).
    fold (@skipn W) in *.
    unfold_all.

    set (skipn _ _) in *.
    set (map _ _) in *.
    assert (to_elim l0) by (unfold to_elim; eauto); hiding ltac:(evaluate hints_array_elim).
    unfold_all.
    erewrite CancelIL.skipn_length in *.

    descend.
    clear_Imply.
    clear_evalInstrs.
    unfold is_state in *.
    unfold has_extra_stack in *.
    unfold frame_len_w in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    simpl in *.
    rewrite H.
    rewrite fold_4_mult_2 in *.
    rewrite_natToW_plus.
    repeat rewrite wplus_assoc in *.
    clear_Forall_PreCond.

    set (array nil _) in *.
    unfold array in h0.
    simpl in h0.
    subst h0.

    instantiate (5 := (_, _)); simpl.

    match goal with
      | H : length _ = _ - 2 |- _ => rewrite H in *
    end.
    unfold toArray in *.
    erewrite (map_eq_length_eq _ (ArgVars _)) in * by eauto.

    rewrite replace_it3 in * by eauto.
    rewrite plus_0_r in *.
    rewrite_natToW_plus.
    repeat rewrite wplus_assoc in *.

    hide_upd_sublist.
    hide_map.
    set (ArgVars _) in *.
    set (x8 - _ - _) in *.
    generalize dependent H36; clear_all; intros.

    repeat hiding ltac:(step auto_ext).

    auto_apply.
    eauto.
    eauto.

    (* post call *)
    eapply existsR.
    apply andR.
    apply Imply_I.
    apply interp_weaken.
    eauto.

    descend.
    generalize H13.
    clear_Imply.

    hide_upd_sublist.
    intros.

    hiding ltac:(step auto_ext).
    hiding ltac:(step auto_ext).

    instantiate (2 := None).
    instantiate (2 := $0).
    simpl.

    unfold is_state in *.
    unfold has_extra_stack in *.
    unfold frame_len_w in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    simpl in *.
    openhyp.
    match goal with
      | H : Regs x15 Sp = _ |- _ => rewrite H in *
    end.
    rewrite H in *.
    rewrite wplus_wminus in *.

    set (array nil _) in *.
    unfold array in h0.
    simpl in h0.
    subst h0.

    instantiate (8 := (_, _)); simpl in *.
    instantiate (7 := l0).
    unfold_all.
    repeat rewrite length_upd_sublist in *.

    rewrite plus_0_r in *.
    rewrite fold_4_mult_2 in *.
    repeat rewrite Mult.mult_plus_distr_l in *.
    rewrite_natToW_plus.
    set (len1 := 4 * length vars) in *.
    set (len2 := 4 * length x6) in *.
    set (w := Regs x Sp ^+ $8) in *.
    replace (_ ^+ natToW (len1 + len2)) with (w ^+ $(len1) ^+ $(len2)) by (rewrite natToW_plus; rewrite wplus_assoc; eauto).
    unfold_all.
    repeat rewrite wplus_assoc in *.

    hide_upd_sublist.
    hide_le.
    unfold toArray in *.
    match goal with
      | H : map _ _ = map _ _ |- _ => eapply map_eq_length_eq in H
    end.

    match goal with
      | H : length (ArgVars _) = _ |- _ => rewrite H in *
    end.

    match goal with
      | H : length (ArgVars _) = _ |- _ => generalize dependent H
    end.

    clear_all.
    intros.

    hiding ltac:(step auto_ext). (* causing universe inconsistency *)

    rewrite fold_first in *.
    set (Regs _ _ ^+ _ ^+ _ ^+ _) in *.
    set (length l) in *.
    set (x8 - _ - _) in *.

    replace (w =?> x8)%Sep with (buf_to_split w x8 2) by (unfold buf_to_split; eauto).
    assert (buf_splittable x8 2) by admit.
    hiding ltac:(step hints_buf_split_bwd).
    post.
    hiding ltac:(step auto_ext).

    rewrite fold_first in *.
    unfold_all.
    set (w := Regs _ _ ^+ _ ^+ _ ^+ _ ^+ _) in *.
    set (big := x8 - _) in *.
    set (small := length l) in *.
    replace (w =?> big)%Sep with (buf_to_split w big small) by (unfold buf_to_split; eauto).
    assert (buf_splittable big small) by admit.
    hiding ltac:(step hints_buf_split_bwd).

    rewrite fold_first in *.
    rewrite fold_4_mult in *.
    hiding ltac:(step auto_ext).

    rewrite fold_first in *.
    set (ArgVars _) in *.
    Require Import SepHints4.
    assert (locals_to_elim l0) by (unfold locals_to_elim; eauto).
    hiding ltac:(step hints_elim_locals).
    unfold_all.
    match goal with
      | H : length (ArgVars _) = _ |- _ => rewrite H in *
    end.
    hiding ltac:(step auto_ext).

    rewrite fold_second in *.
    simpl in *.
    openhyp.
    descend.
    match goal with
      | H : Regs _ Rv = _ |- _ => rewrite H
    end.
    auto_apply.
    econstructor; simpl in *.
    eauto.
    unfold toArray in *.
    match goal with
      | H : map _ _ = map _ _ |- _ => rewrite <- H
    end.
    reflexivity.
    eauto.
    unfold_all.
    repeat rewrite length_upd_sublist in *; eauto.

    eauto.

    destruct_state.

    unfold is_state in *.
    unfold has_extra_stack in *.
    simpl in *.
    hiding ltac:(step auto_ext).
    hiding ltac:(step auto_ext).
    hiding ltac:(step auto_ext).
    hiding ltac:(step auto_ext).
    instantiate (2 := (_, _)); simpl in *.
    clear_all.

    hiding ltac:(step auto_ext).

    descend.
    2 : words.

    econstructor.
    2 : eauto.
    match goal with
      | H : Regs _ Rv = _ |- _ => rewrite H
    end.
    econstructor; simpl in *.
    eauto.
    unfold toArray in *.
    match goal with
      | H : map _ _ = map _ _ |- _ => rewrite <- H
    end.
    reflexivity.
    eauto.

    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
  Qed.
(*here*)

    (* foreign *)
    unfold_all.
    simpl in *.
    Transparent funcs_ok.
    generalize H7; intro is_funcs_ok.
    unfold funcs_ok in H7.
    Opaque funcs_ok.
    simpl in *.
    repeat rewrite wplus_assoc in *.
    post.
    specialize (Imply_sound (H10 _ _) (Inj_I _ _ H28)); propxFo.
    descend.
    rewrite H2.
    rewrite H26.
    eauto.
    step auto_ext.
    descend.
    clear_Imply.
    clear_evalInstrs.
    instantiate (2 := pairs).
    unfold is_state in *.
    unfold has_extra_stack in *.
    unfold frame_len_w in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    simpl in *.
    rewrite H.
    rewrite <- H30.
    rewrite map_length in *.
    hide_upd_sublist.
    Require Import SepHints2.
    clear_Forall_PreCond.
    hide_all_eq.
    rewrite (@replace_array_to_split l2 _ (length l)) in H3.
    assert (splittable l2 (length l)) by admit.
    hiding ltac:(evaluate hints_array_split).
    fold (@firstn W) in *.
    fold (@skipn W) in *.
    rewrite fold_4_mult in *.
    intros.
    unfold_all.
    erewrite firstn_upd_sublist in * by eauto.
    erewrite skipn_upd_sublist in * by eauto.

    set (skipn _ _) in *.
    hide_all_eq.
    hide_upd_sublist.
    set (map _ _) in H5.
    assert (to_elim l0) by (unfold to_elim; eauto); hiding ltac:(evaluate hints_array_elim).
    intros.
    unfold_all.
    erewrite CancelIL.skipn_length in *.
    rewrite H27 in *.
    rewrite replace_it3 in * by eauto.
    rewrite Mult.mult_0_r in *.
    rewrite wplus_0 in *.
    rewrite fold_4_mult_2 in *.
    rewrite_natToW_plus.
    repeat rewrite wplus_assoc in *.

    generalize dependent H6; clear_all; intros.
    hide_upd_sublist.
    set (map _ _) in *.
    set (x8 - _ - _) in *.

    set (locals nil _ _ _) in *.
    unfold locals in h0.
    unfold array in h0.
    simpl in h0.
    subst h0.

    repeat hiding ltac:(step auto_ext).

    eauto.
    eauto.
    eauto.

    (* post call *)
    eapply existsR.
    apply andR.
    apply Imply_I.
    apply interp_weaken.
    eauto.

    descend.
    generalize H13.
    clear_Imply.

    hide_upd_sublist.
    intros.

    hiding ltac:(step auto_ext).

    unfold is_state in *.
    unfold has_extra_stack in *.
    unfold frame_len_w in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    simpl in *.
    rewrite H32 in *.
    rewrite H in *.
    rewrite wplus_wminus in *.

    set (locals nil _ _ _) in *.
    unfold locals in h0.
    unfold array in h0.
    simpl in h0.
    subst h0.

    instantiate (8 := (_, _)); simpl in *.
    instantiate (9 := upd_sublist (upd_sublist x6 0 x12) 0 x13).
    repeat rewrite length_upd_sublist in *.

    rewrite Mult.mult_0_r in *.
    rewrite wplus_0 in *.
    rewrite fold_4_mult_2 in *.
    rewrite Mult.mult_plus_distr_l in *.
    rewrite_natToW_plus.
    set (4 * length vars) in *.
    set (4 * length x6) in *.
    set (Regs x Sp ^+ $8) in *.
    replace (_ ^+ natToW (n + n0)) with (w ^+ $(n) ^+ $(n0)) by (rewrite natToW_plus; rewrite wplus_assoc; eauto).
    unfold_all.
    repeat rewrite wplus_assoc in *.

    hide_upd_sublist.
    assert (length x15 = length l) by admit.
    generalize H35.
    hide_le.
    clear_all.
    intros.

    hiding ltac:(step auto_ext).
    assert (to_elim x15) by (unfold to_elim; eauto).
    hiding ltac:(step hints_array_elim).
    rewrite H35 in *.
    set (Regs _ _ ^+ _ ^+ _ ^+ _) in *.
    set (length l) in *.
    set (x8 - _ - _) in *.

    replace (w =?> x8)%Sep with (buf_to_split w x8 2) by (unfold buf_to_split; eauto).
    assert (buf_splittable x8 2) by admit.
    hiding ltac:(step hints_buf_split_bwd).
    post.
    hiding ltac:(step auto_ext).

    set (w ^+ _) in *.
    set (x8 - _) in *.
    subst n0.
    set (length l) in *.
    replace (w0 =?> n)%Sep with (buf_to_split w0 n n0) by (unfold buf_to_split; eauto).
    assert (buf_splittable n n0) by admit.
    hiding ltac:(step hints_buf_split_bwd).

    rewrite fold_first in *.
    rewrite fold_second in *.
    simpl in *.
    descend.
    rewrite H29.
    rewrite H10 in *.
    eapply H31.
    econstructor; simpl in *.
    eauto.
    rewrite H30.
    rewrite make_triples_Word; eauto.
    eapply make_triples_Forall_pair; eauto.
    rewrite make_triples_ADTIn; eauto.
    eauto.
    eauto.

    unfold_all.
    repeat rewrite length_upd_sublist in *; eauto.

    eauto.

    destruct_state.

    unfold is_state in *.
    unfold has_extra_stack in *.
    simpl in *.
    hiding ltac:(step auto_ext).
    hiding ltac:(step auto_ext).
    hiding ltac:(step auto_ext).
    instantiate (2 := (_, _)); simpl in *.
    clear_all.

    hiding ltac:(step auto_ext).

    rewrite fold_first in *.
    rewrite fold_second in *.
    simpl in *.
    descend.
    2 : words.

    econstructor.
    2 : eauto.
    rewrite H29.
    econstructor; simpl in *.
    eauto.
    rewrite H30.
    rewrite make_triples_Word; eauto.
    eapply make_triples_Forall_pair; eauto.
    rewrite make_triples_ADTIn; eauto.
    eauto.
    eauto.

    (* vc 1 *)
    unfold stack_slot in *.
    replace (4 * 1) with 4 in * by eauto.
    eapply H2 in H.
    unfold precond, inv, inv_template, is_state in *.
    unfold has_extra_stack in *.
    post.
    evaluate' auto_ext.

    (* vc 2 *)
    unfold stack_slot in *.
    replace (4 * 1) with 4 in * by eauto.
    eapply H2 in H3.
    unfold precond, inv, inv_template, is_state in *.
    unfold has_extra_stack in *.
    post.
    evaluate' auto_ext.

    (* vc 3 *)
    unfold CompileExprs.imply in *.
    unfold CompileExprs.new_pre in *.
    unfold CompileExprs.is_state in *.
    post.
    eapply H2 in H0.
    unfold precond, inv, inv_template, is_state in *.
    unfold has_extra_stack in *.
    post.
    unfold stack_slot in *.
    replace (4 * 1) with 4 in * by eauto.
    evaluate' auto_ext.
    destruct x3; simpl in *.
    destruct x; simpl in *.
    generalize dependent H4.
    assert (2 <= wordToNat x7) by admit.
    evaluate' hints_buf_2_fwd.
    evaluate' hints_array.
    intros.
    descend.
    unfold callee_stack_start in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    post.
    rewrite H in *.
    rewrite H8 in *.
    rewrite replace_it.
    repeat hiding ltac:(step auto_ext).
    eauto.
    rewrite H23.
    admit. (* length l <= wordToNat x7 - 2 *)

    (* vc 4*)
    eapply in_scope_Call_args; eauto.

    (* vc 5*)
    unfold CompileExpr.imply in *.
    unfold CompileExpr.new_pre in *.
    unfold CompileExpr.is_state in *.
    post.
    eapply H2 in H0.
    unfold precond, inv, inv_template, is_state in *.
    unfold has_extra_stack in *.
    post.
    unfold stack_slot in *.
    replace (4 * 1) with 4 in * by eauto.
    evaluate' auto_ext.
    destruct x4; simpl in *.
    destruct x; simpl in *.
    unfold CompileExprs.post in *.
    unfold CompileExprs.runs_to in *.
    unfold CompileExprs.is_state in *.
    generalize dependent H5.
    assert (2 <= wordToNat x8) by admit.
    evaluate' hints_buf_2_fwd.
    evaluate' hints_array.
    unfold callee_stack_start in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    rewrite <- H in *.
    rewrite H9 in *.
    rewrite replace_it in *.
    transit.
    post.
    descend.
    instantiate (2 := upd_sublist x5 0 x10).
    instantiate (2 := v).
    set (upd_sublist x5 _ _) in *.
    set (upd_sublist x9 _ _) in *.
    repeat hiding ltac:(step auto_ext).
    rewrite length_upd_sublist; eauto.
    
    (* vc 6 *)
    eapply in_scope_Call_f; eauto.

    (* vc 7 *)
    eapply H2 in H3.
    unfold precond, inv, inv_template, is_state in *.
    unfold has_extra_stack in *.
    post.
    unfold stack_slot in *.
    replace (4 * 1) with 4 in * by eauto.
    evaluate' auto_ext.
    destruct x4; simpl in *.
    unfold CompileExprs.runs_to in *.
    unfold CompileExprs.is_state in *.
    simpl in *.
    hide_evalInstrs.
    assert (2 <= wordToNat x8) by admit.
    evaluate' hints_buf_2_fwd.
    evaluate' hints_array.
    unfold callee_stack_start in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    rewrite <- H in *.
    rewrite H11 in *.
    rewrite replace_it in *.
    transit.
    post.
    unfold CompileExpr.runs_to in *.
    unfold CompileExpr.is_state in *.
    simpl in *.
    set (upd_sublist x5 _ _) in *.
    set (upd_sublist x10 _ _) in *.
    transit.
    post.
    unfold callee_stack_slot in *.
    unfold callee_stack_start in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    rewrite replace_it2 in *.
    rewrite <- H17 in *.
    rewrite <- H19 in *.
    generalize dependent H21.
    generalize dependent H5.
    clear_all.
    intros.
    eval_instrs auto_ext.










    (* skip *)
    wrap0.

    (* seq *)
    Require Import PostOk.

    wrap0.
    eapply IHs1.
    wrap0.
    eapply H2 in H.
    unfold precond in *.
    unfold inv in *.
    unfold inv_template in *.
    post.
    descend.
    eauto.
    eauto.
    eapply Safe_Seq_assoc; eauto.
    eauto.
    eauto.
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    descend.
    eapply RunsTo_Seq_assoc; eauto.
    eapply in_scope_Seq_Seq; eauto.

    eapply IHs2.
    wrap0.
    unfold TopSection.compile in H.
    eapply post_ok in H.
    unfold postcond in *.
    unfold inv in *.
    unfold inv_template in *.
    post.

    unfold verifCond in *.
    unfold imply in *.
    wrap0.
    eapply H2 in H0.
    unfold precond in *.
    unfold inv in *.
    unfold inv_template in *.
    post.
    descend.
    eauto.
    eauto.
    eapply Safe_Seq_assoc; eauto.
    eauto.
    eauto.
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    descend.
    eapply RunsTo_Seq_assoc; eauto.
    eapply in_scope_Seq_Seq; eauto.
    eapply in_scope_Seq; eauto.

    (* if *)
    wrap0.
    unfold CompileExpr.imply in *.
    unfold CompileExpr.new_pre in *.
    unfold CompileExpr.is_state in *.
    intros.
    eapply H2 in H.
    unfold precond in *.
    unfold inv in *.
    unfold inv_template in *.
    unfold is_state in *.
    post.
    descend.
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    eauto.
    eapply in_scope_If_e; eauto.

    clear_imports.
    evaluate auto_ext.

    (* true *)
    eapply IHs1.
    wrap0.
    eapply H2 in H0.
    unfold precond in *.
    unfold inv in *.
    unfold inv_template in *.
    unfold is_state in *.
    unfold CompileExpr.runs_to in *.
    unfold CompileExpr.is_state in *.
    post.
    transit.
    destruct x3; simpl in *.
    destruct x; simpl in *.
    post.
    descend.
    eauto.
    instantiate (4 := (_, _)); simpl.
    instantiate (5 := upd_sublist x4 0 x).
    repeat rewrite length_upd_sublist.
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    find_cond.
    eapply Safe_Seq_If_true; eauto.
    rewrite length_upd_sublist; eauto.
    eauto.

    clear_imports.
    repeat hiding ltac:(step auto_ext).

    descend.
    find_cond.
    eapply RunsTo_Seq_If_true; eauto.
    eapply in_scope_If_true; eauto.

    (* false *)
    eapply IHs2.
    wrap0.
    eapply H2 in H0.
    unfold precond in *.
    unfold inv in *.
    unfold inv_template in *.
    unfold is_state in *.
    unfold CompileExpr.runs_to in *.
    unfold CompileExpr.is_state in *.
    post.
    transit.
    destruct x3; simpl in *.
    destruct x; simpl in *.
    post.
    descend.
    eauto.
    instantiate (4 := (_, _)); simpl.
    instantiate (5 := upd_sublist x4 0 x).
    repeat rewrite length_upd_sublist.
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    find_cond.
    eapply Safe_Seq_If_false; eauto.
    rewrite length_upd_sublist; eauto.
    eauto.

    clear_imports.
    repeat hiding ltac:(step auto_ext).

    descend.
    find_cond.
    eapply RunsTo_Seq_If_false; eauto.
    eapply in_scope_If_false; eauto.

    (* while *)
    wrap0.
    unfold CompileExpr.imply in *.
    unfold CompileExpr.new_pre in *.
    unfold CompileExpr.is_state in *.
    intros.
    eapply H2 in H.
    unfold precond in *.
    unfold inv in *.
    unfold inv_template in *.
    unfold is_state in *.
    post.
    descend.
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    eauto.
    eapply in_scope_While_e; eauto.

    eapply H2 in H0.
    unfold precond in *.
    unfold inv in *.
    unfold inv_template in *.
    unfold is_state in *.
    unfold CompileExpr.runs_to in *.
    unfold CompileExpr.is_state in *.
    post.
    transit.
    destruct x2; simpl in *.
    post.
    descend.
    eauto.
    instantiate (4 := (_, _)); simpl.
    instantiate (5 := upd_sublist x3 0 x2).
    repeat rewrite length_upd_sublist.
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    eauto.
    eauto.
    rewrite length_upd_sublist; eauto.
    eauto.

    clear_imports.
    repeat hiding ltac:(step auto_ext).

    descend.

    unfold evalCond in *.
    simpl in *.
    discriminate H0.

    unfold TopSection.compile in H0.
    eapply post_ok in H0.
    unfold postcond in *.
    unfold inv in *.
    unfold inv_template in *.
    unfold is_state in *.
    unfold CompileExpr.runs_to in *.
    unfold CompileExpr.is_state in *.
    post.
    transit.
    destruct x2; simpl in *.
    post.
    descend.
    eauto.
    instantiate (4 := (_, _)); simpl.
    instantiate (5 := upd_sublist x3 0 x2).
    repeat rewrite length_upd_sublist.
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    eauto.
    eauto.
    rewrite length_upd_sublist; eauto.
    eauto.

    clear_imports.
    repeat hiding ltac:(step auto_ext).

    descend.

    unfold verifCond in *.
    unfold imply in *.
    wrap0.
    post.
    descend.
    eauto.
    eauto.
    find_cond.
    eapply Safe_Seq_While_true; eauto.
    eauto.
    eauto.

    clear_imports.
    repeat hiding ltac:(step auto_ext).

    descend.
    find_cond.
    eapply RunsTo_Seq_While_true; eauto.
    eapply in_scope_While; eauto.

    eapply IHs.
    wrap0.
    post.
    descend.
    eauto.
    eauto.
    find_cond.
    eapply Safe_Seq_While_true; eauto.
    eauto.
    eauto.

    clear_imports.
    repeat hiding ltac:(step auto_ext).

    descend.
    find_cond.
    eapply RunsTo_Seq_While_true; eauto.
    eapply in_scope_While; eauto.

    unfold CompileExpr.verifCond in *.
    unfold CompileExpr.imply in *.
    wrap0.
    unfold TopSection.compile in H.
    eapply post_ok in H.
    unfold postcond in *.
    unfold inv in *.
    unfold inv_template in *.
    unfold is_state in *.
    unfold CompileExpr.is_state in *.
    post.
    descend.
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    eauto.

    unfold verifCond in *.
    unfold imply in *.
    wrap0.
    post.
    descend.
    eauto.
    eauto.
    find_cond.
    eapply Safe_Seq_While_true; eauto.
    eauto.
    eauto.

    clear_imports.
    repeat hiding ltac:(step auto_ext).

    descend.
    find_cond.
    eapply RunsTo_Seq_While_true; eauto.
    eapply in_scope_While; eauto.

    eapply in_scope_While_e; eauto.

  Qed.

End TopSection.