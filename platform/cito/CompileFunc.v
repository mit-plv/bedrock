Set Implicit Arguments.

Section TopSection.

  Require Import String.
  Variable module_name : string.

  Require Import SyntaxFunc.
  Variable func : Func.

  Require Import List.
  Require Import WellFormed.
  Record GoodFunc f := 
    {
      NoDupVars : NoDup (ArgVars f ++ LocalVars f);
      WellFormed : wellformed (Body f)
    }.

  Hypothesis good_func : GoodFunc func.

  Definition Optimizer := Stmt -> Stmt.

  Variable optimizer : Optimizer.

  Definition GoodOptimizer : Optimizer -> Prop.
    admit.
  Qed.

  Hypothesis good_optimizer : GoodOptimizer optimizer.

  Require Import Inv.
  Require Import Malloc.
  Require Import Semantics Safe.
  Definition inv vars temp_size s : assert := 
    st ~> Ex fs, 
    funcs_ok (fst st) fs /\
    ExX, Ex v, Ex temps, Ex rp, Ex e_stack,
    ![^[is_state st#Sp rp e_stack vars v temps * mallocHeap 0] * #0] st /\
    [| Safe fs s v /\
       length temps = temp_size |] /\
    (st#Rp(*the only difference from Inv.inv*), fst st) 
      @@@ (
        st' ~> Ex v', Ex temps',
        ![^[is_state st'#Sp rp e_stack vars v' temps' * mallocHeap 0] * #1] st' /\
        [| RunsTo fs s v v' /\
           length temps' = temp_size /\
           st'#Sp = st#Sp |]).

  Definition spec := inv (SyntaxFunc.ArgVars func) 0 (SyntaxFunc.Body func).

  Section Body.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Definition stack_slot n := LvMem (Sp + (4 * n)%nat)%loc.

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

  Definition vars := SyntaxFunc.ArgVars func ++ LocalVars func.

  Require Import Depth.
  Definition temp_size := depth (SyntaxFunc.Body func).

  Require CompileStmt.
  Definition compile_stmt s := CompileStmt.compile vars temp_size imports_global module_name s Syntax.Skip.

  Definition body_stmt := optimizer (SyntaxFunc.Body func).

  Infix "/\" := cons : tmp_scope.
  Open Scope tmp_scope.
  Definition body' :=
    let stack_needed := length (LocalVars func) + temp_size in
    CheckExtraStack 
      stack_needed
      (Seq
         (Strline 
            (Binop (stack_slot 1) (stack_slot 1) Minus stack_needed /\
             Assign (stack_slot 0) Rp /\ nil) /\
          compile_stmt body_stmt /\
          Strline 
            (Assign Rp (stack_slot 0) /\ nil) /\
          IGoto _ _ Rp /\ nil)).
  Close Scope tmp_scope.

  Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

  Definition verifCond pre := imply pre spec :: nil.

  Require Import Wrap.

  Lemma verifCond_ok : forall pre : assert, vcs (verifCond pre) -> vcs (VerifCond (body' pre)).
  Proof.
    Opaque funcs_ok.
    Opaque mult.

    Require Import WordFacts.
    Require Import CompileStmtTactics.
    Require Import Arith.

    Open Scope nat.

    Set Printing Coercions.

    unfold verifCond, imply; wrap0.

    Focus 4.
    (* vc 4 *)
    unfold CompileStmtSpec.imply in *.
    unfold CompileStmtSpec.precond in *.
    post.
    eapply H2 in H0.
    unfold spec in *.
    unfold inv in *.
    unfold inv_template in *.
    unfold is_state in *.
    unfold has_extra_stack in *.
    unfold stack_slot in *.
    post.
    match goal with
      | H : length _ = 0 |- _ => rewrite H in *
    end.
    rewrite plus_0_r in *.
    rewrite fold_4_mult_1 in *.
    rewrite mult_0_r in *.
    destruct_state.
    hiding ltac:(evaluate auto_ext).
    fold (@length string) in *.
    rewrite_natToW_plus.
    repeat rewrite wplus_assoc in *.
    Lemma GoodFunc_goodSize : forall f, GoodFunc f -> goodSize (length (LocalVars f) + depth (SyntaxFunc.Body f)).
      admit.
    Qed.

    Ltac gen_le :=
      match goal with
        | H : (natToW ?a ^+ natToW ?b <= natToW ?c)%word |- _ => assert (a + b <= c) by (eapply wle_goodSize_le; [rewrite_natToW_plus | eapply GoodFunc_goodSize]; eauto); assert (a <= c) by omega; assert (b <= c - a) by omega
      end.

    gen_le.
    Require Import SepHints2.
    set (len_args := length (SyntaxFunc.ArgVars func)) in *.
    set (w := Regs x1 _ ^+ _ ^+ _) in *.
    set (len_local := length (LocalVars func)) in *.
    replace (w =?> x7)%Sep with (buf_to_split w x7 len_local) in * by (unfold buf_to_split; eauto).
    assert (buf_splittable x7 len_local) by (unfold buf_splittable; eauto).
    Require Import SepHints5.
    hiding ltac:(evaluate hints_split_buf).
    rewrite fold_4_mult in *.

    unfold_all.
    set (w := Regs x1 _ ^+ _ ^+ _ ^+ _) in *.
    set (buf := x7 - _) in *.
    replace (w =?> buf)%Sep with (buf_to_split w buf temp_size) in * by (unfold buf_to_split; eauto).
    assert (buf_splittable buf temp_size) by (unfold buf_splittable; eauto).
    hiding ltac:(evaluate hints_split_buf).
    fold (@length string) in *.
    rewrite fold_4_mult in *.
    Definition to_intro_array (_ : W) := True.

    Lemma intro_array : forall len p, to_intro_array p -> p =?> len ===> Ex ls, [| length ls = len |] * array ls p.
      admit.
    Qed.

    Definition hints_intro_array : TacPackage.
      prepare intro_array tt.
    Defined.

    assert (to_intro_array w) by (unfold to_intro_array; eauto).
    hiding ltac:(evaluate hints_intro_array).
    fold (@length string) in *.

    set (p_local_vars := Regs x1 _ ^+ _ ^+ _) in *.
    assert (to_intro_array p_local_vars) by (unfold to_intro_array; eauto).
    hiding ltac:(evaluate hints_intro_array).
    fold (@length string) in *.

    Lemma GoodFunc_NoDup_LocalVars : forall f, GoodFunc f -> NoDup (LocalVars f).
      admit.
    Qed.
    
    Require Import SepHints3.
    set (lvars := LocalVars _) in *.
    rewrite (@replace_array_to_locals x4 _ lvars) in H20.
    assert (array_to_locals_ok x4 lvars) by (unfold_all; unfold array_to_locals_ok; descend; eapply GoodFunc_NoDup_LocalVars; eauto).
    hiding ltac:(evaluate hints_array_to_locals).

    unfold_all.
    unfold vars in *.
    set (extra := _ - _ - _) in *.
    descend.
    eauto.
    match goal with
      | H : _ = Regs x1 Sp |- _ => rewrite H in *
    end.
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

    generalize H20; clear_all; intros.

    repeat hiding ltac:(step auto_ext).

    fold (@length string) in *.
    fold (@app string) in *.

    Definition combined_locals vars1 vars2 vs1 vs2 p  := locals (vars1 ++ vars2) (merge vs1 vs2 vars1) 0 p.

    Definition locals_combinable A (vars vars2 : list A) := NoDup (vars ++ vars2).

    Lemma combine_locals : forall vars1 vars2 vs1 vs2 p, locals vars1 vs1 0 p * locals vars2 vs2 0 (p ^+ $(4 * length vars1)) ===> combined_locals vars1 vars2 vs1 vs2 p.
      admit.
    Qed.

    Definition hints_combine_locals : TacPackage.
      prepare tt combine_locals.
    Defined.

    instantiate (1 := merge v x9 (SyntaxFunc.ArgVars func)).
    set (avars := SyntaxFunc.ArgVars _) in *.
    set (lvars := SyntaxFunc.LocalVars _) in *.
    rewrite wplus_0 in *.
    set (w := Regs _ _ ^+ natToW 8) in *.
    Lemma fold_combined_locals : forall vars1 vars2 vs1 vs2 p, locals (vars1 ++ vars2) (merge vs1 vs2 vars1) 0 p = combined_locals vars1 vars2 vs1 vs2 p.
      eauto.
    Qed.

    rewrite fold_combined_locals.

    assert (locals_combinable avars lvars).
    unfold locals_combinable.
    Lemma GoodFunc_NoDup_vars : forall f, GoodFunc f -> NoDup (SyntaxFunc.ArgVars f ++ LocalVars f).
      admit.
    Qed.

    eapply GoodFunc_NoDup_vars; eauto.
    admit.

    repeat hiding ltac:(step hints_combine_locals).
    (*here*)


    (* vc 1 *)
    eapply H2 in H.
    unfold spec in *.
    unfold inv in *.
    unfold inv_template in *.
    unfold is_state in *.
    unfold has_extra_stack in *.
    unfold stack_slot in *.
    rewrite fold_4_mult_1 in *.
    post.
    hiding ltac:(evaluate auto_ext).

    (* vc 2 *)
    eapply H2 in H1.
    unfold spec in *.
    unfold inv in *.
    unfold inv_template in *.
    unfold is_state in *.
    unfold has_extra_stack in *.
    unfold stack_slot in *.
    rewrite fold_4_mult_1 in *.
    post.
    hiding ltac:(evaluate auto_ext).

    (* vc 3 *)
    eapply H2 in H1.
    unfold spec in *.
    unfold inv in *.
    unfold inv_template in *.
    unfold is_state in *.
    unfold has_extra_stack in *.
    unfold stack_slot in *.
    post.
    rewrite fold_4_mult_1 in *.
    rewrite mult_0_r in *.
    hiding ltac:(evaluate auto_ext).

    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
  Qed.

  Definition body : cmd imports module_name.
    refine (
        Wrap imports imports_global module_name 
             body'
             (fun pre => Postcondition (body' pre))
             verifCond
             _ _).
    wrap0.
    eapply verifCond_ok.
  Defined.

  End Body.

  Require Import StructuredModule.
  Definition compile : function module_name :=
    (Name func, spec, body).

End TopSection.