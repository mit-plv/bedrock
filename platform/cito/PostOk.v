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

  Lemma post_ok : 
    forall (s k : Stmt) (pre : assert) (specs : codeSpec W (settings * state))
           (x : settings * state),
      vcs (verifCond layout vars temp_size s k pre) ->
      interp specs
             (Postcondition
                (compile s k pre) x) ->
      interp specs (postcond layout vars temp_size k x).
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

    (* call *)
    Lemma replace_it : forall w n, w ^+ $(8) ^+ $(n) = w ^+ natToW (4 * 2 + n).
      intros.
      rewrite natToW_plus.
      rewrite wplus_assoc.
      eauto.
    Qed.

    destruct o.

    wrap0.
    post.
    clear_imports.
    set (P := is_state _) in *.
    eval_instrs auto_ext.
    subst P.
    unfold is_state in *.
    unfold frame_len_w in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold var_slot in *.
    unfold vars_start in *.
    repeat rewrite <- H in H5.
    assert (List.In s vars) by eauto.
    assert (
        evalInstrs (fst x) x0
                   (Assign (LvMem (Imm ((Regs x0 Sp ^+ $8) ^+ $(variablePosition vars s)))) Rv
                           :: nil) = Some (snd x)
) ; [ | clear H11 ].
    rewrite <- H11.
    Transparent evalInstrs.
    simpl.
    rewrite replace_it.
    eauto.
    Opaque evalInstrs.
    clear_imports.
    set (P := is_heap _) in *.
    eval_instrs auto_ext.
    subst P.
    destruct x; simpl in *.
    destruct x4; simpl in *.
    rewrite <- H in H1.
    repeat rewrite H1.
    descend.
    eauto.
    instantiate (4 := (_, _)); simpl.
    instantiate (6 := upd v s (Regs x0 Rv)).
    instantiate (4 := h).
    instantiate (4 := x5).
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    rewrite H14.
    eauto.
    eauto.
    eauto.
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    descend.
    descend.

    wrap0.
    post.
    clear_imports.
    set (P := is_state _) in *.
    eval_instrs auto_ext.
    subst P.
    unfold is_state in *.
    unfold frame_len_w in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold var_slot in *.
    unfold vars_start in *.
    repeat rewrite <- H in H9.
    destruct x; simpl in *.
    destruct x3; simpl in *.
    descend.
    eauto.
    instantiate (4 := (_, _)); simpl.
    instantiate (6 := v).
    instantiate (4 := h).
    instantiate (4 := x4).
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    eauto.
    eauto.
    eauto.
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    descend.

    (* skip *)

    intros.
    wrap0.
    eapply H3 in H0.
    unfold precond in *.
    unfold inv in *.
    unfold inv_template in *.
    post.
    descend.
    eauto.
    eauto.

    eapply Safe_Seq_Skip; eauto.
    eauto.
    eauto.


    clear_imports.
    repeat hiding ltac:(step auto_ext).
    descend.
    eapply RunsTo_Seq_Skip; eauto.

    (* seq *)
    wrap0.
    eapply IHs2 in H0.
    unfold postcond in *.
    unfold inv in *.
    unfold inv_template in *.
    post.

    wrap0.
    eapply IHs1 in H.
    unfold postcond in *.
    unfold inv in *.
    unfold inv_template in *.
    post.

    wrap0.
    eapply H3 in H1.
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

    (* if - true *)
    wrap0.
    eapply IHs1 in H.
    unfold postcond in *.
    unfold inv in *.
    unfold inv_template in *.
    post.

    wrap0.
    eapply H3 in H1.
    unfold precond in *.
    unfold inv in *.
    unfold inv_template in *.
    unfold CompileExpr.runs_to in *.
    unfold is_state in *.
    unfold CompileExpr.is_state in *.
    post.

    transit.

    destruct x4; simpl in *.
    post.
    descend.
    eauto.
    instantiate (4 := (_, _)).
    simpl.
    destruct x0; simpl in *.
    instantiate (5 := upd_sublist x5 0 x4).
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

    (* if - false *)
    wrap0.
    eapply IHs2 in H.
    unfold postcond in *.
    unfold inv in *.
    unfold inv_template in *.
    post.

    wrap0.
    eapply H3 in H1.
    unfold precond in *.
    unfold inv in *.
    unfold inv_template in *.
    unfold CompileExpr.runs_to in *.
    unfold is_state in *.
    unfold CompileExpr.is_state in *.
    post.

    transit.

    destruct x4; simpl in *.
    post.
    descend.
    eauto.
    instantiate (4 := (_, _)).
    simpl.
    destruct x0; simpl in *.
    instantiate (5 := upd_sublist x5 0 x4).
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
    post.
    descend.
    eauto.
    eauto.
    find_cond.
    eapply Safe_Seq_While_false; eauto.
    eauto.
    eauto.
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    descend.
    find_cond.
    eapply RunsTo_Seq_While_false; eauto.

  Qed.

End TopSection.


(*
    Ltac pre_eval_statement := intros; openhyp; try_post.

    Ltac assert_new_as t name := not_exist t; assert t as name.

    Ltac eval_statement := pre_eval_statement; transit; openhyp; try_post.

    Ltac eval_step hints := first[eval_statement | try clear_imports; eval_instrs hints].

*)