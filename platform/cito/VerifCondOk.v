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

    (* call *)
    wrap0.
    unfold stack_slot in *.
    replace (4 * 1) with 4 in * by eauto.
    eapply H2 in H.
    unfold precond, inv, inv_template, is_state in *.
    unfold has_extra_stack in *.
    post.
    Ltac evaluate' hints :=
      match goal with
        | [ H : Safe _ _ _ |- _ ] =>
          generalize dependent H; clear_imports; evaluate hints; intro
      end.

    evaluate' auto_ext.

    unfold stack_slot in *.
    replace (4 * 1) with 4 in * by eauto.
    eapply H2 in H3.
    unfold precond, inv, inv_template, is_state in *.
    unfold has_extra_stack in *.
    post.
    evaluate' auto_ext.

    unfold expose_callee_stack in *.
    destruct (Compare_dec.zerop (Datatypes.length l)).
    wrap0.
    wrap0.
    eapply H2 in H3.
    unfold precond, inv, inv_template, is_state in *.
    unfold has_extra_stack in *.
    post.
    unfold stack_slot in *.
    replace (4 * 1) with 4 in * by eauto.
    eval_instrs auto_ext.
    Set Printing Coercions.
    assert (
        interp specs
         (![SEP.ST.star (fun (stn : ST.settings) (sm : smem) => x1 (stn, sm))
              (SEP.ST.star (Malloc.FreeList.mallocHeap (natToW 0))
                 (SEP.ST.star
                    ((Ex ls, array ls (Regs st Sp ^+ $(callee_stack_start vars temp_size + 8)) *
                     [| length ls = wordToNat x6 - 2 |]) *
                     (Regs x Sp ^+ $(callee_stack_start vars temp_size)) =?> 2)
                    (SEP.ST.star (is_heap layout (snd x2))
                       (SEP.ST.star
                          (locals vars (fst x2) 0 (Regs x Sp ^+ natToW 8))
                          (SEP.ST.star
                             (array x3
                                (Regs x Sp ^+ natToW 8
                                 ^+ natToW (4 * Datatypes.length vars)))
                             (SEP.ST.star (Regs x Sp =*> x4)
                                ((Regs x Sp ^+ natToW 4) =*> x6)))))))]
            (stn, st))
      ) by admit; clear H3.
    assert ($0 < natToW (wordToNat x6 - 2)) by admit.
    assert (
        evalInstrs stn st
          (Assign (LvReg Rv)
             (RvLval
                (LvMem
                   (Imm (Regs st Sp ^+ $(callee_stack_start vars temp_size + 8)))))
           :: nil) = None
      ) by admit; clear H13.
    admit.
    (* eval_instrs auto_ext. *)
    
    unfold expose_callee_stack in *.
    destruct (Compare_dec.zerop (Datatypes.length l)).
    Lemma length_0_nil : forall A (ls : list A), length ls = 0 -> ls = nil.
      admit.
    Qed.
    eapply length_0_nil in e0.
    subst.
    simpl in *.
    admit.

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
    eval_instrs auto_ext.
    destruct x; simpl in *.
    assert (
        interp specs
         (![SEP.ST.star (fun (stn : ST.settings) (sm : smem) => x3 (stn, sm))
              (SEP.ST.star (Malloc.FreeList.mallocHeap (natToW 0))
                 (SEP.ST.star
                    ((Ex ls, array ls (Regs x0 Sp ^+ $(callee_stack_start vars temp_size + 8)) * 
                            [| length ls = wordToNat x8 - 2 |]) *
                     (Regs x0 Sp ^+ $(callee_stack_start vars temp_size)) =?> 2)
                    (SEP.ST.star (is_heap layout (snd x4))
                       (SEP.ST.star
                          (locals vars (fst x4) 0 (Regs x1 Sp ^+ natToW 8))
                          (SEP.ST.star
                             (array x5
                                (Regs x1 Sp ^+ natToW 8
                                 ^+ natToW (4 * Datatypes.length vars)))
                             (SEP.ST.star (Regs x1 Sp =*> x6)
                                ((Regs x1 Sp ^+ natToW 4) =*> x8)))))))]
            (s, x0))
) by admit; clear H3.
    assert ($0 < natToW (wordToNat x8 - 2)) by admit.
    assert (
        evalInstrs s x0 (Assign Rv (LvMem (Imm (Regs x0 Sp ^+ $(callee_stack_start vars temp_size + 8)))) :: nil) = Some s0
      ) by admit; clear H13.
    destruct x4; simpl in *.
    generalize H5 H14 H3; clear; intros.
    assert (
        interp specs
         (![SEP.ST.star (fun (stn : ST.settings) (sm : smem) => x3 (stn, sm))
                    ((Ex ls : list W,
                      array ls
                        (Regs x0 Sp
                         ^+ $ (callee_stack_start vars temp_size + 8)) *
                      [|Datatypes.length ls = wordToNat x8 - 2|]))]
            (s, x0))
      ) by admit; clear H5.
    assert False.
    set (wordToNat x8 - 2) in *.
    set ($(callee_stack_start vars temp_size + 8)) in *.
    post.
    generalize H14 H3 H; clear; intros.
    assert (0 < n)%nat by admit.
    (* here *)
    evaluate auto_ext.
    eval_instrs auto_ext.





    assert (
        interp specs
          (![SEP.ST.star
               (fun (stn : ST.settings) (sm : smem) => x2 (stn, sm))
               (SEP.ST.star (Malloc.FreeList.mallocHeap (natToW 0))
                  (SEP.ST.star
                     ((Ex ls, array ls (Regs s0 Sp ^+ $(callee_stack_start vars temp_size + 8)) * [| length ls = wordToNat x7 - 2 |]) *
                      (Regs s0 Sp ^+ $(callee_stack_start vars temp_size + 8)) =?> 2
                     )
                     (SEP.ST.star (is_heap layout h)
                        (SEP.ST.star
                           (locals vars v 0 (Regs x0 Sp ^+ natToW 8))
                           (SEP.ST.star
                              (array x4
                                 (Regs x0 Sp ^+ natToW 8
                                  ^+ natToW (4 * Datatypes.length vars)))
                              (SEP.ST.star (Regs x0 Sp =*> x5)
                                 ((Regs x0 Sp ^+ natToW 4) =*> x7)))))))]
             (s, s0))
) by admit; clear H10.
    assert ($0 < natToW (wordToNat x7 - 2)) by admit.
    assert (
        evalInstrs s s0 (Assign Rv (LvMem (Imm (Regs s0 Sp ^+ $(callee_stack_start vars temp_size + 8)))) :: nil) <> None
      ) by admit.
    eval_instrs auto_ext.
    post.
    evaluate' auto_ext.

    post.


    descend.

    le_wordToN


    admit.

    Require Import PostOk.

    (* skip *)
    wrap0.

    (* seq *)
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