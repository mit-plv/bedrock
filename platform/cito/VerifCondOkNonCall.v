Require Import CompileStmtSpec CompileStmtImpl.

Set Implicit Arguments.

Module Make (Import M : RepInv.RepInv).

  Require Import PostOk.
  Module Import PostOkMake := PostOk.Make M.
  Require Import CompileStmtTactics.
  Module Import CompileStmtTacticsMake := CompileStmtTactics.Make M.

  Import CompileStmtSpecMake.
  Import CompileStmtSpecMake.InvMake.

  Section TopSection.

    Variable vars : list string.

    Variable temp_size : nat.

    Variable imports : LabelMap.t assert.

    Variable imports_global : importsGlobal imports.

    Variable modName : string.

    Require Import Syntax.
    Require Import Wrap.

    Variable rv_postcond : W -> Semantics.State -> Prop.

    Notation do_compile := (CompileStmtImplMake.compile vars temp_size rv_postcond imports_global modName).

    Require Import Semantics.
    Require Import Safe.
    Require Import Notations.
    Require Import SemanticsFacts.
    Require Import SynReqFacts.
    Require Import ListFacts.
    Require Import StringSet.
    Require Import SetFacts.

    Open Scope stmt.

    Opaque funcs_ok.
    Opaque mult.
    Opaque star. (* necessary to use eapply_cancel *)
    Opaque CompileStmtImplMake.InvMake.funcs_ok.

    Hint Resolve Subset_syn_req_In.
    Hint Extern 0 (Subset _ _) => progress (simpl; subset_solver).
    Hint Resolve map_length.

    Set Printing Coercions.

    Require Import SemanticsExpr.
    Require Import GeneralTactics.
    Require Import VerifCondOkTactics.

    Open Scope nat.

    Lemma verifCond_ok_skip : 
      forall k (pre : assert),
        let s := skip in
        vcs (verifCond vars temp_size s k rv_postcond pre) ->
        vcs
          (VerifCond (do_compile s k pre)).
    Proof.

      unfold verifCond, imply.

      (* skip *)
      wrap0.

    Qed.

    Lemma verifCond_ok_seq : 
      forall s1 s2
             (IHs1 : forall (k : Stmt) (pre : assert),
                       vcs
                         ((forall (specs : codeSpec W (settings * state))
                                  (x : settings * state),
                             interp specs (pre x) ->
                             interp specs (precond vars temp_size s1 k rv_postcond x))
                            :: syn_req vars temp_size (s1;; k) :: nil) ->
                       vcs (VerifCond (do_compile s1 k pre)))
             (IHs2 : forall (k : Stmt) (pre : assert),
                       vcs
                         ((forall (specs : codeSpec W (settings * state))
                                  (x : settings * state),
                             interp specs (pre x) ->
                             interp specs (precond vars temp_size s2 k rv_postcond x))
                            :: syn_req vars temp_size (s2;; k) :: nil) ->
                       vcs (VerifCond (do_compile s2 k pre)))
             k (pre : assert),
        let s := s1 ;; s2 in
        vcs (verifCond vars temp_size s k rv_postcond pre) ->
        vcs
          (VerifCond (do_compile s k pre)).
    Proof.

      unfold verifCond, imply.
      intros.

      (* seq *)
      wrap0.
      eapply IHs1.
      wrap0.
      eapply H2 in H.
      unfold precond in *.
      unfold inv in *.
      unfold inv_template in *.
      post.
      descend; eauto.
      eapply Safe_Seq_assoc; eauto.
      repeat hiding ltac:(step auto_ext).
      descend.
      eapply RunsTo_Seq_assoc; eauto.
      eapply syn_req_Seq_Seq; eauto.

      eapply IHs2.
      wrap0.
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
      descend; eauto.
      eapply Safe_Seq_assoc; eauto.
      repeat hiding ltac:(step auto_ext).
      descend.
      eapply RunsTo_Seq_assoc; eauto.
      eapply syn_req_Seq_Seq; eauto.
      eapply syn_req_Seq; eauto.

    Qed.

    Lemma verifCond_ok_if : 
      forall e s1 s2
             (IHs1 : forall (k : Stmt) (pre : assert),
                       vcs
                         ((forall (specs : codeSpec W (settings * state))
                                  (x : settings * state),
                             interp specs (pre x) ->
                             interp specs (precond vars temp_size s1 k rv_postcond x))
                            :: syn_req vars temp_size (s1;; k) :: nil) ->
                       vcs (VerifCond (do_compile s1 k pre)))
             (IHs2 : forall (k : Stmt) (pre : assert),
                       vcs
                         ((forall (specs : codeSpec W (settings * state))
                                  (x : settings * state),
                             interp specs (pre x) ->
                             interp specs (precond vars temp_size s2 k rv_postcond x))
                            :: syn_req vars temp_size (s2;; k) :: nil) ->
                       vcs (VerifCond (do_compile s2 k pre)))
             k (pre : assert),
        let s := Syntax.If e s1 s2 in
        vcs (verifCond vars temp_size s k rv_postcond pre) ->
        vcs
          (VerifCond (do_compile s k pre)).
    Proof.

      unfold verifCond, imply.
      intros.

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
      repeat hiding ltac:(step auto_ext).
      eauto.
      eapply syn_req_If_e; eauto.

      hiding ltac:(evaluate auto_ext).

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
      destruct_state.
      post.
      hide_upd_sublist.
      descend.
      eauto.
      instantiate (6 := (_, _)); simpl.
      instantiate (7 := l).
      unfold_all; repeat rewrite length_upd_sublist.
      repeat hiding ltac:(step auto_ext).
      find_cond.
      eapply Safe_Seq_If_true; eauto.
      unfold_all; rewrite length_upd_sublist; eauto.
      eauto.
      eauto.

      repeat hiding ltac:(step auto_ext).

      descend.
      find_cond.
      eapply RunsTo_Seq_If_true; eauto.
      eapply syn_req_If_true; eauto.

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
      destruct_state.
      post.
      hide_upd_sublist.
      descend.
      eauto.
      instantiate (6 := (_, _)); simpl.
      instantiate (7 := l).
      unfold_all; repeat rewrite length_upd_sublist.
      repeat hiding ltac:(step auto_ext).
      find_cond.
      eapply Safe_Seq_If_false; eauto.
      unfold_all; rewrite length_upd_sublist; eauto.
      eauto.
      eauto.

      repeat hiding ltac:(step auto_ext).

      descend.
      find_cond.
      eapply RunsTo_Seq_If_false; eauto.
      eapply syn_req_If_false; eauto.

    Qed.

    Lemma verifCond_ok_while : 
      forall e s
             (IHs : forall (k : Stmt) (pre : assert),
                      vcs
                        ((forall (specs : codeSpec W (settings * state))
                                 (x : settings * state),
                            interp specs (pre x) ->
                            interp specs (precond vars temp_size s k rv_postcond x))
                           :: syn_req vars temp_size (s;; k) :: nil) ->
                      vcs (VerifCond (do_compile s k pre)))
             k (pre : assert),
        let s := Syntax.While e s in
        vcs (verifCond vars temp_size s k rv_postcond pre) ->
        vcs
          (VerifCond (do_compile s k pre)).
    Proof.

      unfold verifCond, imply.
      intros.

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
      repeat hiding ltac:(step auto_ext).
      eauto.
      eapply syn_req_While_e; eauto.

      change CompileStmtImplMake.InvMake.funcs_ok with funcs_ok in *.
      change CompileStmtImplMake.InvMake.is_state with is_state in *.
      change CompileStmtImplMake.InvMake.is_heap with is_heap in *.
      change CompileStmtImplMake.InvMake.layout_option with layout_option in *.
      eapply H2 in H0.
      unfold precond in *.
      unfold inv in *.
      unfold inv_template in *.
      unfold is_state in *.
      unfold CompileExpr.runs_to in *.
      unfold CompileExpr.is_state in *.
      post.
      transit.
      destruct_state.
      post.
      hide_upd_sublist.
      descend.
      eauto.
      instantiate (6 := (_, _)); simpl.
      instantiate (7 := l).
      unfold_all; repeat rewrite length_upd_sublist.
      repeat hiding ltac:(step auto_ext).
      eauto.
      unfold_all; rewrite length_upd_sublist; eauto.
      eauto.
      eauto.

      repeat hiding ltac:(step auto_ext).

      descend.

      hiding ltac:(evaluate auto_ext).

      change CompileStmtImplMake.InvMake.funcs_ok with funcs_ok in *.
      change CompileStmtImplMake.InvMake.is_state with is_state in *.
      change CompileStmtImplMake.InvMake.is_heap with is_heap in *.
      change CompileStmtImplMake.InvMake.layout_option with layout_option in *.
      eapply post_ok in H0.
      unfold postcond in *.
      unfold inv in *.
      unfold inv_template in *.
      unfold is_state in *.
      unfold CompileExpr.runs_to in *.
      unfold CompileExpr.is_state in *.
      post.
      transit.
      destruct_state.
      post.
      hide_upd_sublist.
      descend.
      eauto.
      instantiate (6 := (_, _)); simpl.
      instantiate (7 := l).
      unfold_all; repeat rewrite length_upd_sublist.
      repeat hiding ltac:(step auto_ext).
      eauto.
      unfold_all; rewrite length_upd_sublist; eauto.
      eauto.
      eauto.

      repeat hiding ltac:(step auto_ext).

      descend.

      unfold verifCond in *.
      unfold imply in *.
      wrap0.
      post.
      descend; eauto.
      find_cond.
      eapply Safe_Seq_While_true; eauto.

      repeat hiding ltac:(step auto_ext).

      descend.
      find_cond.
      eapply RunsTo_Seq_While_true; eauto.
      eapply syn_req_While; eauto.

      eapply IHs.
      wrap0.
      post.
      descend; eauto.
      find_cond.
      eapply Safe_Seq_While_true; eauto.

      repeat hiding ltac:(step auto_ext).

      descend.
      find_cond.
      eapply RunsTo_Seq_While_true; eauto.
      eapply syn_req_While; eauto.

      unfold CompileExpr.verifCond in *.
      unfold CompileExpr.imply in *.
      wrap0.
      eapply post_ok in H.
      unfold postcond in *.
      unfold inv in *.
      unfold inv_template in *.
      unfold is_state in *.
      unfold CompileExpr.is_state in *.
      post.
      descend.
      repeat hiding ltac:(step auto_ext).
      eauto.

      unfold verifCond in *.
      unfold imply in *.
      wrap0.
      post.
      descend; eauto.
      find_cond.
      eapply Safe_Seq_While_true; eauto.

      repeat hiding ltac:(step auto_ext).

      descend.
      find_cond.
      eapply RunsTo_Seq_While_true; eauto.
      eapply syn_req_While; eauto.

      eapply syn_req_While_e; eauto.

    Qed.

  End TopSection.

End Make.