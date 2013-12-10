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
  Hint Resolve map_length.

  Set Printing Coercions.

  Require Import SemanticsExpr.
  Require Import SepHints.
  Require Import GeneralTactics.
  Require Import WordFacts.
  Require Import Arith.
  Require Import InvFacts.
  Require Import VerifCondOkTactics.

  Open Scope nat.

  Lemma verifCond_ok : 
    forall o e l k (pre : assert),
      let s := Syntax.Call o e l in
      vcs (verifCond layout vars temp_size s k pre) ->
      vcs
        (VerifCond (compile s k pre)).
  Proof.

    unfold verifCond, imply.

    (* call *)
    wrap0.

    (* vc 1 *)
    unfold stack_slot in *.
    rewrite fold_4_mult_1 in *.
    eapply H2 in H.
    unfold precond, inv, inv_template, is_state in *.
    unfold has_extra_stack in *.
    post.
    hiding ltac:(evaluate auto_ext).

    (* vc 2 *)
    unfold stack_slot in *.
    rewrite fold_4_mult_1 in *.
    eapply H2 in H3.
    unfold precond, inv, inv_template, is_state in *.
    unfold has_extra_stack in *.
    post.
    hiding ltac:(evaluate auto_ext).

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
    rewrite fold_4_mult_1 in *.
    hiding ltac:(evaluate auto_ext).
    destruct_state.
    hide_evalInstrs.
    match goal with
      | H : context [ (_ =?> ?n)%Sep ] |- _ => assert (2 <= n) by admit
    end.
    hiding ltac:(evaluate hints_buf_2_fwd).
    hiding ltac:(evaluate hints_array).
    intros.
    descend.
    unfold callee_stack_start in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    post.
    match goal with
      | H : _ = temp_size |- _ => rewrite H in *
    end.
    match goal with
      | H : Regs s0 Sp = _ |- _ => rewrite H in *
    end.
    rewrite fold_4_mult_2 in *.
    rewrite Mult.mult_plus_distr_l in *.
    rewrite_natToW_plus.
    repeat rewrite natToW_plus.
    repeat rewrite wplus_assoc in *.
    repeat hiding ltac:(step auto_ext).
    eauto.
    match goal with
      | H : length _ = _ - 2 |- _ => rewrite H in *
    end.
    admit. (* length l <= _ - 2 *)

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
    rewrite fold_4_mult_1 in *.
    hiding ltac:(evaluate auto_ext).
    destruct_state.
    unfold CompileExprs.post in *.
    unfold CompileExprs.runs_to in *.
    unfold CompileExprs.is_state in *.
    hide_evalInstrs.
    match goal with
      | H : context [ (_ =?> ?n)%Sep ] |- _ => assert (2 <= n) by admit
    end.
    hiding ltac:(evaluate hints_buf_2_fwd).
    hiding ltac:(evaluate hints_array).
    unfold callee_stack_start in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    simpl in *.
    match goal with
      | H : _ = temp_size |- _ => rewrite H in *
    end.
    match goal with
      | H : Regs x0 Sp = _ |- _ => rewrite H in *
    end.
    rewrite fold_4_mult_2 in *.
    rewrite Mult.mult_plus_distr_l in *.
    rewrite_natToW_plus.
    repeat rewrite natToW_plus in H3.
    repeat rewrite wplus_assoc in *.
    transit.
    post.
    descend.
    hide_upd_sublist.
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
    rewrite fold_4_mult_1 in *.
    hiding ltac:(evaluate auto_ext).
    destruct_state.
    unfold CompileExprs.runs_to in *.
    unfold CompileExprs.is_state in *.
    simpl in *.
    hide_evalInstrs.
    match goal with
      | H : context [ (_ =?> ?n)%Sep ] |- _ => assert (2 <= n) by admit
    end.
    hiding ltac:(evaluate hints_buf_2_fwd).
    hiding ltac:(evaluate hints_array).
    unfold callee_stack_start in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    match goal with
      | H : _ = temp_size |- _ => rewrite H in *
    end.
    match goal with
      | H : Regs x0 Sp = _ |- _ => rewrite H in *
    end.
    rewrite fold_4_mult_2 in *.
    rewrite Mult.mult_plus_distr_l in *.
    rewrite_natToW_plus.
    repeat rewrite natToW_plus in H5.
    repeat rewrite wplus_assoc in *.
    transit.
    post.
    unfold CompileExpr.runs_to in *.
    unfold CompileExpr.is_state in *.
    simpl in *.
    hide_upd_sublist.
    transit.
    post.
    unfold callee_stack_slot in *.
    unfold callee_stack_start in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    match goal with
      | H : _ = Regs x1 Sp |- _ => rewrite <- H in *
    end.
    match goal with
      | H : _ = Regs x Sp |- _ => rewrite <- H in *
    end.
    rewrite fold_4_mult_1 in *.
    rewrite fold_4_mult_2 in *.
    rewrite_natToW_plus.
    repeat rewrite wplus_assoc in *.
    repeat rewrite replace1 in *.
    generalize dependent H21.
    hide_evalInstrs.
    clear_all.
    intros.
    hiding ltac:(evaluate auto_ext).

    (* vc 8 *)
    eapply H2 in H3.
    unfold precond, inv, inv_template, is_state in *.
    unfold has_extra_stack in *.
    post.
    unfold stack_slot in *.
    rewrite fold_4_mult_1 in *.
    hiding ltac:(evaluate auto_ext).
    destruct_state.
    unfold CompileExprs.runs_to in *.
    unfold CompileExprs.is_state in *.
    simpl in *.
    hide_evalInstrs.
    match goal with
      | H : context [ (_ =?> ?n)%Sep ] |- _ => assert (2 <= n) by admit
    end.
    hiding ltac:(evaluate hints_buf_2_fwd).
    hiding ltac:(evaluate hints_array).
    unfold callee_stack_start in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    match goal with
      | H : _ = temp_size |- _ => rewrite H in *
    end.
    match goal with
      | H : Regs x1 Sp = _ |- _ => rewrite H in *
    end.
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
    hide_upd_sublist.
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
    match goal with
      | H : _ = Regs x2 Sp |- _ => rewrite <- H in *
    end.
    match goal with
      | H : _ = Regs x0 Sp |- _ => rewrite <- H in *
    end.
    repeat rewrite replace1 in *.
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

    hiding ltac:(step auto_ext).

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

    (* foreign *)
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
    match goal with
      | H : map _ _ = map _ _ |- _ => rewrite <- H
    end.
    rewrite map_length in *.
    hide_upd_sublist.
    Require Import SepHints2.
    clear_Forall_PreCond.
    hide_all_eq.
    rewrite (@replace_array_to_split l2 _ (length l)) in H7.
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
    hide_map.
    assert (to_elim l0) by (unfold to_elim; eauto); hiding ltac:(evaluate hints_array_elim).
    intros.
    unfold_all.
    erewrite CancelIL.skipn_length in *.
    match goal with
      | H : length _ = _ - 2 |- _ => rewrite H in *
    end.
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
    match goal with
      | H : Regs x14 Sp = _ |- _ => rewrite H in *
    end.
    rewrite H in *.
    rewrite wplus_wminus in *.

    set (locals nil _ _ _) in *.
    unfold locals in h0.
    unfold array in h0.
    simpl in h0.
    subst h0.

    instantiate (8 := (_, _)); simpl in *.
    hide_upd_sublist.
    instantiate (9 := l1).
    unfold_all.
    repeat rewrite length_upd_sublist in *.

    rewrite Mult.mult_0_r in *.
    rewrite wplus_0 in *.
    rewrite fold_4_mult_2 in *.
    rewrite Mult.mult_plus_distr_l in *.
    rewrite_natToW_plus.
    set (len1 := 4 * length vars) in *.
    set (len2 := 4 * length x6) in *.
    set (w := Regs x Sp ^+ $8) in *.
    replace (_ ^+ natToW (len1 + len2)) with (w ^+ $(len1) ^+ $(len2)) by (rewrite natToW_plus; rewrite wplus_assoc; eauto).
    unfold_all.
    repeat rewrite wplus_assoc in *.

    hide_upd_sublist.
    match goal with
      | H : map _ _ = map _ _ |- _ => generalize H; eapply map_eq_length_eq in H; intro
    end.
    rewrite make_triples_length in * by eauto.
    assert (length x15 = length l) by (rewriter; eauto).
    repeat match goal with
             | H : length _ = length l |- _ => generalize dependent H
           end.
    hide_le.
    clear_all.
    intros.

    hiding ltac:(step auto_ext).
    assert (to_elim x15) by (unfold to_elim; eauto).
    hiding ltac:(step hints_array_elim).
    match goal with
      | H : length _ = length l |- _ => rewrite H in *
    end.
    set (Regs _ _ ^+ _ ^+ _ ^+ _) in *.
    set (length l) in *.
    set (x8 - _ - _) in *.

    replace (w =?> x8)%Sep with (buf_to_split w x8 2) by (unfold buf_to_split; eauto).
    assert (buf_splittable x8 2) by admit.
    hiding ltac:(step hints_buf_split_bwd).
    post.
    hiding ltac:(step auto_ext).

    unfold_all.
    set (w := Regs _ _ ^+ _ ^+ _ ^+ _ ^+ _) in *.
    set (big := x8 - _) in *.
    set (small := length l) in *.
    replace (w =?> big)%Sep with (buf_to_split w big small) by (unfold buf_to_split; eauto).
    assert (buf_splittable big small) by admit.
    hiding ltac:(step hints_buf_split_bwd).

    rewrite fold_first in *.
    rewrite fold_second in *.
    simpl in *.
    descend.
    match goal with
      | H : Regs _ Rv = _ |- _ => rewrite H
    end.
    match goal with
      | H : _ = fold_left store_out _ _ |- _ => rewrite H in *
    end.
    auto_apply.
    econstructor; simpl in *.
    eauto.
    match goal with
      | H : map _ _ = map _ _ |- _ => rewrite H
    end.
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
    match goal with
      | H : Regs _ Rv = _ |- _ => rewrite H
    end.
    econstructor; simpl in *.
    eauto.
    match goal with
      | H : map _ _ = map _ _ |- _ => rewrite H
    end.
    rewrite make_triples_Word; eauto.
    eapply make_triples_Forall_pair; eauto.
    rewrite make_triples_ADTIn; eauto.
    eauto.
    eauto.

    (* vc 9 *)
    post.
    hiding ltac:(evaluate auto_ext).

    (* vc 10 *)
    unfold SaveRet.imply in *.
    wrap0.
    post.
    destruct_state.
    hiding ltac:(evaluate auto_ext).
    unfold is_state in *.
    unfold SaveRet.is_state in *.
    match goal with
      | H : _ = Regs _ _ ^- _ |- _ => rewrite <- H in *
    end.
    simpl in *.
    descend.
    repeat hiding ltac:(step auto_ext).

    (* vc 11 *)
    eapply in_scope_Call_ret; eauto.

  Qed.

End TopSection.