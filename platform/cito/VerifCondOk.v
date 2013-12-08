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

    Open Scope nat.

    Lemma replace_it : forall (a : W) b c, a ^+ $(4 * 2 + 4 * b + 4 * c +8) = a ^+ $8 ^+ $(4 * (b + c)) ^+ $8.
      admit.
    Qed.

    Lemma replace_it2 : forall (a : W) b c, a ^+ $8 ^+ $(4 * (b + c)) ^+ $4 = a ^+ $(4 * 2 + 4 * b + 4 * c + 4 * 1).
      admit.
    Qed.

    Ltac evaluate' hints :=
      match goal with
        | [ H : Safe _ _ _ |- _ ] =>
          generalize dependent H; clear_imports; evaluate hints; intro
      end.

    Ltac hide_evalInstrs :=
      repeat match goal with
               | H : evalInstrs _ _ _ = _ |- _ => generalize dependent H
             end.

    Ltac clear_all :=
      repeat match goal with
               | H : _ |- _ => clear H
             end.

    Ltac destruct_state :=
      repeat 
        match goal with
          | [ x : State |- _ ] => destruct x; simpl in *
          | [ x : (settings * state)%type |- _ ] => destruct x; simpl in *
        end.

    Ltac hide_all_eq_except H1 :=
      repeat match goal with
               | H : _ = _ |- _ => not_eq H H1; generalize dependent H
             end.

    Ltac unfold_all :=
      repeat match goal with
               | H := _ |- _ => unfold H in *; clear H
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
    replace (4 * 1) with 4 in * by eauto.
    evaluate' auto_ext.
    destruct_state.
    unfold CompileExprs.runs_to in *.
    unfold CompileExprs.is_state in *.
    simpl in *.
    hide_evalInstrs.
    assert (2 <= x8) by admit.
    evaluate' hints_buf_2_fwd.
    evaluate' hints_array.
    unfold callee_stack_start in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    rewrite <- H in *.
    rewrite H12 in *.
    rewrite replace_it in *.
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
    rewrite replace_it2 in *.
    rewrite <- H18 in *.
    rewrite <- H20 in *.
    hide_all_eq_except H6.
    eval_instrs auto_ext.

    inversion H16; clear H16; subst.
    inversion H29; clear H29; subst.
    Focus 2.

    (* foreign *)
    unfold_all.
    simpl in *.
    Transparent funcs_ok.
    generalize H7; intro is_funcs_ok.
    unfold funcs_ok in H7.
    Opaque funcs_ok.
    simpl in *.
    post.
    specialize (Imply_sound (H12 _ _) (Inj_I _ _ H28)); propxFo.
    descend.
    rewrite H2.
    rewrite H26.
    eauto.
    step auto_ext.
    descend.
    clear H29.
    clear H12.
    clear H6.
    clear H5 H13.
    repeat match goal with
               | H : evalInstrs _ _ _ = _ |- _ => clear H
           end.
    
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
    Ltac hide_upd_sublist :=
      repeat match goal with
               | H : context [ upd_sublist ?L _ _ ] |- _ => set (upd_sublist L _ _) in *
             end.

    hide_upd_sublist.

    Require Import SepHints2.

    clear H33.
    clear H34.
    Ltac hide_all_eq :=
      repeat match goal with
               | H : _ = _ |- _ => generalize dependent H
             end.

    hide_all_eq.
    rewrite (@replace_array_to_split l2 _ (length l)) in H3.
    assert (splittable l2 (length l)) by admit.
    evaluate hints_array_split.
    fold (@firstn W) in *.
    fold (@skipn W) in *.
    intros.
    unfold_all.
    Hint Resolve map_length.

    Lemma firstn_upd_sublist : forall a b n, n = length b -> firstn n (upd_sublist a 0 b) = b.
      admit.
    Qed.
    
    erewrite firstn_upd_sublist in * by eauto.

    Lemma skipn_upd_sublist : forall a b n, n = length b -> skipn n (upd_sublist a 0 b) = skipn n a.
      admit.
    Qed.

    erewrite skipn_upd_sublist in * by eauto.

    set (skipn _ _) in *.
    hide_all_eq.
    hide_upd_sublist.
    set (map _ _) in H5.
    assert (to_elim l0) by (unfold to_elim; eauto); evaluate hints_array_elim.
    intros.
    unfold_all.
    erewrite CancelIL.skipn_length in *.
    rewrite H27 in *.
    Lemma replace_it3 : forall a b, $(a) ^- $(S (S b)) = natToW (a - 2 - b).
      admit.
    Qed.

    rewrite replace_it3 in *.
    rewrite Mult.mult_0_r in *.
    Lemma wplus_0 : forall w : W, w ^+ $0 = w.
      intros; rewrite wplus_comm; eapply wplus_unit.
    Qed.
    rewrite wplus_0 in *.
    replace (4 * 2) with 8 in * by omega.
    Lemma replace4 : forall (a : W) b c, a ^+ $(b) ^+ $(c) = a ^+ $(b + c).
      admit.
    Qed.
    rewrite replace4 in *.
    rewrite replace4 in *.
    rewrite map_length in *.
    Lemma replace5 : forall n, $4 ^* $(n) = natToW (4 * n).
      admit.
    Qed.

    rewrite replace5 in *.
    rewrite Mult.mult_plus_distr_l in *.
    replace (4 * 1) with 4 in * by eauto.
    generalize dependent H6; clear_all; intros.
    hide_upd_sublist.
    set (map _ _) in *.
    set (x8 - _ - _) in *.

    set (locals nil _ _ _) in *.
    unfold locals in h0.
    unfold array in h0.
    simpl in h0.
    subst h0.
    rewrite (@Plus.plus_comm 8) in *.
    rewrite (@Plus.plus_comm 8) in *.
    Lemma replace6 : forall a b, 4 * a + 4 * b + 8 = 4 * a + 8 + 4 * b.
      admit.
    Qed.

    rewrite replace6 in *.

    clear_imports.
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
    clear H5 H3.
    clear H6 H12 H29.
    hide_upd_sublist.

    clear_imports.
    hiding ltac:(step auto_ext).

    unfold is_state in *.
    unfold has_extra_stack in *.
    unfold frame_len_w in *.
    unfold frame_len in *.
    unfold temp_start in *.
    unfold vars_start in *.
    simpl in *.
    rewrite H29 in *.
    rewrite H in *.
    Lemma wplus_wminus_same : forall a b : W, a ^+ b ^- b = a.
      admit.
    Qed.

    rewrite wplus_wminus_same in *.
    set (locals nil _ _ _) in *.
    unfold locals in h0.
    unfold array in h0.
    simpl in h0.
    subst h0.
    rewrite Mult.mult_0_r in *.
    rewrite wplus_0 in *.
    replace (4 * 2) with 8 in * by omega.
    repeat rewrite replace4 in *.
    rewrite Mult.mult_plus_distr_l in *.
    replace (4 * 1) with 4 in * by eauto.
    repeat rewrite (@Plus.plus_comm 8) in *.
    rewrite replace6 in *.

    instantiate (6 := (_, _)); simpl in *.
    instantiate (8 := v).
    instantiate (7 := upd_sublist l0 0 x13).
    
    subst l0.
    rewrite length_upd_sublist in *.
    rewrite length_upd_sublist in *.
    set (upd_sublist x6 _ _) in *.
    set (upd_sublist l0 _ _) in *.
    assert (length x15 = length l) by admit.
    generalize H32 H27 H13.
    repeat match goal with
               | H : _ <= _ |- _ => generalize dependent H
           end.
    clear_all.
    intros.

    hiding ltac:(step auto_ext).
    assert (to_elim x15) by (unfold to_elim; eauto).
    hiding ltac:(step hints_array_elim).
    rewrite H32 in *.
    set (4 * _ + _ + 4 * _) in *.
    Lemma replace7 : forall (a : W) b c, a ^+ $(b + c) = a ^+ $(b) ^+ $(c).
      admit.
    Qed.

    repeat rewrite replace7 in *.
    set (Regs x Sp ^+ _) in *.

    set (length l) in *.
    set (x8 - _ - _) in *.

    Definition buf_to_split p len (_ : nat) := (p =?> len)%Sep.

    Definition buf_splittable (len pos : nat) := pos <= len.

    Lemma buf_split_bwd : forall p len pos, buf_splittable len pos -> p =?> pos * (p ^+ $(4 * pos)) =?> (len - pos) ===> buf_to_split p len pos.
      admit.
    Qed.

    Definition hints_buf_split_bwd : TacPackage.
      prepare tt buf_split_bwd.
    Defined.

    replace (w =?> x8)%Sep with (buf_to_split w x8 2) by (unfold buf_to_split; eauto).
    assert (buf_splittable x8 2) by admit.
    hiding ltac:(step hints_buf_split_bwd).
    post.
    hiding ltac:(step auto_ext).

    replace (4 * 2) with 8 in * by omega.

    set (w ^+ _) in *.
    set (x8 - _) in *.
    subst n1.
    set (length l) in *.
    replace (w0 =?> n0)%Sep with (buf_to_split w0 n0 n1) by (unfold buf_to_split; eauto).
    assert (buf_splittable n0 n1) by admit.
    hiding ltac:(step hints_buf_split_bwd).

    Focus 2.
    eauto.

    Focus 2.

    Fixpoint heap_upd_option h addr a :=
      match a with
        | None => h
        | Some v => heap_upd h addr v
      end.

    rewrite fold_second in *.
    set (snd (decide_ret _ _)) in *.
    destruct_state.

    hiding ltac:(step auto_ext).
    hiding ltac:(step auto_ext).
    hiding ltac:(step auto_ext).
    unfold is_state in *.
    unfold has_extra_stack in *.
    instantiate (2 := (_, _)); simpl in *.
    instantiate (2 := heap_upd_option h0 x17 y).
    clear_all.

    hiding ltac:(step auto_ext).

    admit. (* himp specs (layout_option layout x17 y * is_heap layout h0)%Sep
     (is_heap layout (heap_upd_option h0 x17 y)) *)

    simpl in *.

    descend.
    Focus 2.
    rewrite H36.
    rewrite H29.
    rewrite H.
    rewrite wplus_wminus_same.
    eauto.

    (* here *)


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
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    eauto.
    rewrite H23.
    admit. (* length l <= wordToNat x7 - 2 *)

    (* vc 4*)
    Lemma in_scope_Call_args : forall vars temp_size x f args k, in_scope vars temp_size (Syntax.Call x f args ;; k) -> CompileExprs.in_scope vars temp_size args 0.
      admit.
    Qed.

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
    clear_imports.
    repeat hiding ltac:(step auto_ext).
    rewrite length_upd_sublist; eauto.
    
    (* vc 6 *)
    Lemma in_scope_Call_f : forall vars temp_size x f args k, in_scope vars temp_size (Syntax.Call x f args ;; k) -> CompileExpr.in_scope vars temp_size f 0.
      admit.
    Qed.

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