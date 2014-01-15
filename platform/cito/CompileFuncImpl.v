Require Import CompileFuncSpec.
Require Import SyntaxFunc.
Require Import String.
Require Import List.
Require Import GetLocalVars GoodFunc GoodOptimizer.

Set Implicit Arguments.

Section TopSection.

  Variable func : Func.

  Variable module_name : string.

  Hypothesis good_func : GoodFunc func.

  Variable optimizer : Optimizer.

  Hypothesis good_optimizer : GoodOptimizer optimizer.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Definition body_stmt := optimizer (Body func).

  Definition local_vars := get_local_vars body_stmt (ArgVars func) (RetVar func).

  Definition vars := ArgVars func ++ local_vars.

  Require Import Depth.
  Definition temp_size := depth body_stmt.

  Definition stack_slot n := LvMem (Sp + (4 * n)%nat)%loc.
  Definition vars_start := 8.
  Definition var_slot x := LvMem (Sp + (vars_start + variablePosition vars x)%nat)%loc.

  Definition Seq2 := @Seq_ _ imports_global module_name.

  Definition Skip := Skip_ imports module_name.

  Fixpoint Seq ls :=
    match ls with
      | nil => Skip
      | a :: ls' => Seq2 a (Seq ls')
    end.

  Definition Strline := Straightline_ imports module_name.

  Definition CheckExtraStack (n : nat) cmd :=
    Seq2 
      (Strline (IL.Assign Rv (stack_slot 1) :: nil))
      (Structured.If_ imports_global n Le Rv cmd
                      (Diverge_ imports module_name)).

  Require CompileStmt.
  Definition compile_stmt (s : Stmt) := CompileStmt.compile vars temp_size imports_global module_name (fun rv v => rv = sel (fst v) (RetVar func)) s Syntax.Skip.

  Definition len_local_vars := length local_vars.

  Infix "/\" := cons : tmp_scope.
  Open Scope tmp_scope.
  Definition body' :=
    let stack_needed := len_local_vars + temp_size in
    CheckExtraStack 
      stack_needed
      (Seq
         (Strline 
            (Binop (stack_slot 1) (stack_slot 1) Minus stack_needed /\
             IL.Assign (stack_slot 0) Rp /\ nil) /\
          compile_stmt body_stmt /\
          Strline 
            (IL.Assign Rv (var_slot (RetVar func)) /\ 
             IL.Assign Rp (stack_slot 0) /\ nil) /\
          IGoto _ _ Rp /\ nil)).
  Close Scope tmp_scope.
  Require Import Wrap.

  Lemma verifCond_ok : forall pre : assert, vcs (verifCond func pre) -> vcs (VerifCond (body' pre)).
  Proof.
    Require Inv.

    Opaque Inv.funcs_ok.
    Opaque mult.

    Require Import WordFacts.
    Require Import CompileStmtTactics.
    Require Import Arith.
    Require Import SemanticsFacts2 StringSetFacts.

    Open Scope nat.

    Set Printing Coercions.

    Ltac auto_apply_in t :=
      match goal with
          H : _ |- _ => eapply t in H
      end.

    unfold verifCond, imply; wrap0.

    Focus 4.
    (* vc 4 *)
    unfold CompileStmtSpec.imply in *.
    unfold CompileStmtSpec.precond in *.
    post.
    eapply H2 in H0.
    unfold spec in *.
    unfold inv, inv' in *.
    post.
    unfold is_state in *.
    unfold stack_slot in *.
    rewrite fold_4_mult_1 in *.
    rewrite mult_0_r in *.
    destruct_state.
    hiding ltac:(evaluate auto_ext).
    fold (@length string) in *.
    rewrite_natToW_plus.
    repeat rewrite wplus_assoc in *.
    Ltac gen_le :=
      match goal with
        | H : (natToW ?a ^+ natToW ?b <= natToW ?c)%word |- _ => assert (a + b <= c) by (eapply wle_goodSize_le; [rewrite_natToW_plus | eapply GoodFunc_GoodOptimizer_goodSize]; eauto); assert (a <= c) by omega; assert (b <= c - a) by omega
      end.

    gen_le.
    Require Import SepHints2.
    set (len_args := length (ArgVars func)) in *.
    set (w := Regs x1 _ ^+ _ ^+ _) in *.
    replace (w =?> x5)%Sep with (buf_to_split w x5 len_local_vars) in * by (unfold buf_to_split; eauto).
    assert (buf_splittable x5 len_local_vars) by (unfold buf_splittable; eauto).
    Require Import SepHints5.
    hiding ltac:(evaluate hints_split_buf).
    rewrite fold_4_mult in *.

    unfold_all.
    set (w := Regs x1 _ ^+ _ ^+ _ ^+ _) in *.
    set (buf := x5 - _) in *.
    replace (w =?> buf)%Sep with (buf_to_split w buf temp_size) in * by (unfold buf_to_split; eauto).
    assert (buf_splittable buf temp_size) by (unfold buf_splittable; eauto).
    hiding ltac:(evaluate hints_split_buf).
    fold (@length string) in *.
    rewrite fold_4_mult in *.
    assert (to_intro_array w) by (unfold to_intro_array; eauto).
    hiding ltac:(evaluate hints_intro_array).
    fold (@length string) in *.
    fold (@length W) in *.

    set (p_local_vars := Regs x1 _ ^+ _ ^+ _) in *.
    assert (to_intro_array p_local_vars) by (unfold to_intro_array; eauto).
    hiding ltac:(evaluate hints_intro_array).
    fold (@length string) in *.
    fold (@length W) in *.

    Require Import SepHints3.
    rewrite (@replace_array_to_locals x4 _ local_vars) in H19.
    assert (array_to_locals_ok x4 local_vars) by (unfold_all; unfold array_to_locals_ok; descend; eauto; eapply NoDup_elements; eauto).
    hiding ltac:(evaluate hints_array_to_locals).
    fold (@length W) in *.

    unfold_all.
    unfold vars in *.
    set (extra := _ - _ - _) in *.
    descend.
    eauto.
    match goal with
      | H : _ = Regs x1 Sp |- _ => rewrite H in *
    end.
    unfold Inv.is_state in *.
    unfold Inv.has_extra_stack in *.
    instantiate (6 := (_, _)); simpl.
    instantiate (7 := x).
    match goal with
      | H : _ = temp_size |- _ => rewrite H in *
    end.
    instantiate (3 := extra).
    repeat rewrite app_length in *.
    repeat rewrite Mult.mult_plus_distr_l in *.
    rewrite_natToW_plus.
    repeat rewrite natToW_plus.
    repeat rewrite wplus_assoc in *.

    Lemma minus_plus_two : forall a b c, a - (b + c) = a - b - c.
      intros; omega.
    Qed.

    replace (natToW _ ^- _) with (natToW extra) in * by (unfold_all; rewrite <- minus_plus_two; rewrite natToW_minus; [rewrite natToW_plus | ]; eauto).

    match goal with
      | H : GoodFunc _ |- _ => generalize dependent H
    end.

    generalize H19; clear_all; intros.

    repeat hiding ltac:(step auto_ext).
    fold (@length string) in *.
    fold (@app string) in *.
    fold (@length W) in *.

    instantiate (1 := merge v x7 (ArgVars func)).
    set (avars := ArgVars _) in *.
    rewrite wplus_0 in *.
    set (w := Regs _ _ ^+ natToW 8) in *.
    rewrite fold_combined_locals.
    assert (locals_combinable avars local_vars) by (unfold locals_combinable; eapply GoodFunc_NoDup_vars; eauto).

    hiding ltac:(step hints_combine_locals).
    rewrite fold_4_mult in *.
    repeat hiding ltac:(step auto_ext).

    eapply Safe_Seq_Skip_Safe.
    unfold body_stmt.
    eapply GoodOptimizer_Safe; eauto.
    eapply GoodFunc_Safe; eauto.
    eapply agree_in_merge.
    
    eauto.
    eauto.
    eauto.

    hiding ltac:(step auto_ext).
    hiding ltac:(step auto_ext).
    hiding ltac:(step auto_ext).

    unfold Inv.is_state in *.
    unfold Inv.has_extra_stack in *.

    rewrite fold_locals_to_split.

    hiding ltac:(step hints_split_locals).
    fold (@length string) in *.
    fold (@app string) in *.
    rewrite fold_first in *.
    rewrite fold_4_mult in *.

    repeat rewrite app_length in *.
    repeat rewrite Mult.mult_plus_distr_l in *.
    rewrite_natToW_plus.
    repeat rewrite wplus_assoc in *.
    
    match goal with
      | H : _ = Regs x1 Sp |- _ => rewrite <- H in *
    end.
    match goal with
      | H : _ = Regs s0 Sp |- _ => rewrite <- H in *
    end.

    set (w := Regs _ _ ^+ _ ^+ _) in *.
    replace (w =?> x5)%Sep with (buf_to_split w x5 (len_local_vars + temp_size)) by (unfold buf_to_split; eauto).
    assert (buf_splittable x5 (len_local_vars + temp_size)) by (unfold buf_splittable; eauto).
    hiding ltac:(step hints_buf_split_bwd).
    fold (@length string) in *.
    rewrite fold_4_mult in *.
    rewrite fold_first in *.

    unfold extra.
    rewrite minus_plus_two.
    match goal with
      | H : length x10 = _ |- _ => rewrite H
    end.
    repeat rewrite Mult.mult_plus_distr_l in *.
    rewrite_natToW_plus.
    repeat rewrite wplus_assoc in *.
    unfold len_local_vars.
    hiding ltac:(step auto_ext).
    Require Import StringSet.
    fold (@length elt) in *.
    rewrite fold_first in *.

    set (buf := _ + _) in *.
    replace (w =?> buf)%Sep with (buf_to_split w buf len_local_vars) by (unfold buf_to_split; eauto).
    assert (buf_splittable buf len_local_vars) by (unfold buf_splittable; unfold_all; unfold len_local_vars in *; eauto).
    hiding ltac:(step hints_buf_split_bwd).
    fold (@length elt) in *.
    rewrite fold_first in *.
    rewrite fold_4_mult in *.

    unfold_all.
    match goal with
      | H : _ = temp_size |- _ => rewrite <- H in *
    end.
    Lemma a_plus_b_minus_a : forall a b, a + b - a = b.
      intros; omega.
    Qed.

    rewrite a_plus_b_minus_a.

    clear_all.
    unfold len_local_vars.
    assert (to_elim x10) by (unfold to_elim; eauto).
    hiding ltac:(step hints_array_elim).
    fold (@length string) in *.
    rewrite fold_first in *.

    Require Import SepHints4.
    clear_all.
    assert (locals_to_elim local_vars) by (unfold locals_to_elim; eauto).
    hiding ltac:(step hints_elim_locals).
    
    descend.
    auto_apply_in RunsTo_Seq_Skip_RunsTo.
    unfold body_stmt in *.
    auto_apply_in GoodOptimizer_RunsTo.
    eapply GoodFunc_RunsTo; eauto.
    eapply agree_in_comm.
    eapply agree_in_merge.
    eauto.

    (* vc 1 *)
    eapply H2 in H.
    unfold spec in *.
    unfold inv, inv' in *.
    unfold is_state in *.
    unfold stack_slot in *.
    rewrite fold_4_mult_1 in *.
    post.
    hiding ltac:(evaluate auto_ext).

    (* vc 2 *)
    eapply H2 in H1.
    unfold spec in *.
    unfold inv, inv' in *.
    unfold is_state in *.
    unfold stack_slot in *.
    rewrite fold_4_mult_1 in *.
    post.
    hiding ltac:(evaluate auto_ext).

    (* vc 3 *)
    eapply H2 in H1.
    unfold spec in *.
    unfold inv, inv' in *.
    unfold is_state in *.
    unfold stack_slot in *.
    post.
    rewrite fold_4_mult_1 in *.
    rewrite mult_0_r in *.
    hiding ltac:(evaluate auto_ext).

    (* vc 4 *)
    eapply GoodFunc_GoodOptimizer_syn_req; eauto.

    (* vc 5 *)
    post.
    unfold Inv.is_state in *.
    unfold Inv.has_extra_stack in *.
    unfold var_slot in *.
    unfold vars_start in *.
    unfold stack_slot in *.
    rewrite mult_0_r in *.
    repeat rewrite Mult.mult_plus_distr_l in *.
    rewrite_natToW_plus.
    set (ret := RetVar _) in *.
    assert (List.In ret vars) by (eapply ret_in_vars).
    assert (
        evalInstrs stn st
                   (IL.Assign (LvReg Rv)
                           (RvLval
                              (LvMem
                                 (Imm (Regs st Sp ^+ $8 ^+ $(variablePosition vars ret)))))
                           :: IL.Assign (LvReg Rp) (RvLval (LvMem (Sp + natToW 0)%loc)) :: nil) =
        None
) ; [ | clear H0 ].
    rewrite <- H0.
    Transparent evalInstrs.
    simpl.
    repeat rewrite wplus_assoc in *.
    eauto.
    Opaque evalInstrs.
    destruct_state.
    hiding ltac:(evaluate auto_ext).

    (* vc 6 *)
    post.
    unfold Inv.is_state in *.
    unfold Inv.has_extra_stack in *.
    unfold var_slot in *.
    unfold vars_start in *.
    unfold stack_slot in *.
    rewrite mult_0_r in *.
    rewrite_natToW_plus.
    set (ret := RetVar _) in *.
    assert (List.In ret vars) by (eapply ret_in_vars).
    assert (
        evalInstrs stn x
                   (IL.Assign (LvReg Rv)
                           (RvLval
                              (LvMem
                                 (Imm (Regs x Sp ^+ $8 ^+ $(variablePosition vars ret)))))
                           :: IL.Assign (LvReg Rp) (RvLval (LvMem (Sp + natToW 0)%loc)) :: nil) =
        Some st
) ; [ | clear H1 ].
    rewrite <- H1.
    Transparent evalInstrs.
    simpl.
    repeat rewrite wplus_assoc in *.
    eauto.
    Opaque evalInstrs.
    destruct_state.
    hiding ltac:(evaluate auto_ext).
    fold (@length string) in *.
    descend.
    eauto.

    hiding ltac:(step auto_ext).
    descend.
    instantiate (2 := (_, _)); simpl.
    match goal with
      | H : Regs st Sp = _ |- _ => rewrite <- H in *
    end.
    repeat hiding ltac:(step auto_ext).

    econstructor; eauto.
    eauto.
    eauto.

  Qed.

  Definition body : cmd imports module_name.
    refine (
        Wrap imports imports_global module_name 
             body'
             (fun pre => Postcondition (body' pre))
             (verifCond func)
             _ _).
    wrap0.
    eapply verifCond_ok.
  Defined.

End TopSection.