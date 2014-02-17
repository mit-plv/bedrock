Require Import AutoSep.
Require Import SyntaxExpr.
Require Import CompileStmtImpl.

Set Implicit Arguments. 

Section ExprComp.

  Variable vars : list string.

  Variable temp_size : nat.

  Definition is_state sp vs temps : HProp :=
    (locals vars vs 0 (sp ^+ $8) *
     array temps (sp ^+ $8 ^+ $(4 * length vars)))%Sep.

  Definition new_pre : assert := 
    x ~> ExX, Ex vs, Ex temps,
    ![^[is_state x#Sp vs temps] * #0]x /\
    [| length temps = temp_size |].

  Require Import SemanticsExpr.
  Require Import DepthExpr.
  Require Import ListFacts.

  Local Open Scope nat.

  Definition runs_to expr base x_pre x := 
    forall specs other vs temps,
      interp specs (![is_state x_pre#Sp vs temps * other ] x_pre)
      -> length temps = temp_size
      -> Regs x Sp = x_pre#Sp /\
      exists changed,
        interp specs (![is_state (Regs x Sp) vs (upd_sublist temps base changed) * other ] (fst x_pre, x)) /\
        length changed <= depth expr /\
        Regs x Rv = eval vs expr.

  Definition post expr base (pre : assert) := 
    st ~> Ex st_pre, 
    pre (fst st, st_pre) /\
    [| runs_to expr base (fst st, st_pre) (snd st) |].

  Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

  Require Import FreeVarsExpr.
  Require Import StringSet.
  Import StringSet.
  Require Import SetUtil.

  Definition syn_req expr base := 
    Subset (free_vars expr) (to_set vars) /\
    base + depth expr <= temp_size.

  Definition verifCond expr base pre := imply pre new_pre :: syn_req expr base :: nil.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Definition Seq2 := @Seq_ _ imports_global modName.

  Definition Skip := Straightline_ imports modName nil.

  Fixpoint Seq ls :=
    match ls with
      | nil => Skip
      | a :: ls' => Seq2 a (Seq ls')
    end.

  Definition Strline := Straightline_ imports modName.

  Fixpoint do_compile (expr : Expr) (base : nat) :=
    match expr with
      | Var str => Strline (Assign (LvReg Rv) (RvLval (var_slot vars str)) :: nil)
      | Const w => Strline (Assign (LvReg Rv) (RvImm w) :: nil)
      | Binop op a b => Seq (
        do_compile a base :: 
        Strline(Assign (temp_slot vars base) (RvLval (LvReg Rv)) :: nil) :: 
        do_compile b (S base) :: 
        (Strline (IL.Binop (LvReg Rv) (RvLval (temp_slot vars base)) op (RvLval (LvReg Rv)) :: nil)) :: nil)
      | TestE te a b => Seq (do_compile a base ::
        Strline( Assign (temp_slot vars base) (RvLval (LvReg Rv)) :: nil ) ::
        do_compile b (S base) ::
        Structured.If_ imports_global (RvLval (temp_slot vars base)) te (RvLval (LvReg Rv))
        (Strline (Assign Rv (RvImm $1) :: nil))
        (Strline (Assign Rv (RvImm $0) :: nil))
        ::nil)
    end.

  Definition body := do_compile.

  Require Import Wrap.

  Hint Extern 1 (_ <= _) => omega.

  Definition compile (expr : Expr) (base : nat) : cmd imports modName.
    refine (Wrap imports imports_global modName (body expr base) (post expr base) (verifCond expr base) _ _).

    unfold verifCond, syn_req; wrap0.
    destruct x; simpl in *.

    Opaque mult.

    Lemma postOk : forall specs sm expr base pre st,
      Subset (free_vars expr) (to_set vars)
      -> base + depth expr <= temp_size
      -> interp specs (Postcondition (do_compile expr base pre) (sm, st))
      -> exists st', interp specs (pre (sm, st')) /\ runs_to expr base (sm, st') st.
      induction expr; simpl; propxFo.

      do 2 esplit.
      eauto.
      hnf.
      intros.
      unfold is_state in H; simpl in H.

      Lemma evalInstrs_read_var : forall sm x s,
        evalInstrs sm x (Assign Rv (var_slot vars s) :: nil)
        = evalInstrs sm x (Assign Rv (LvMem (Imm ((Regs x Sp ^+ natToW vars_start) ^+ natToW (variablePosition vars s)))) :: nil).
        Transparent evalInstrs.
        simpl.
        intros.
        replace (Regs x Sp ^+ natToW (vars_start + variablePosition vars s))
          with (Regs x Sp ^+ natToW vars_start ^+ natToW (variablePosition vars s)); auto.
        rewrite natToW_plus.
        words.
        Opaque evalInstrs.
      Qed.

      hnf in H.
      assert (In s (singleton s)).
      apply singleton_spec; auto.
      apply H in H5.
      assert (List.In s vars) by admit.
      rewrite evalInstrs_read_var in H3.
      unfold vars_start in H3.
      change (4 * 2) with 8 in *.
      clear_fancy.
      unfold is_state in H1; simpl in H1.
      evaluate auto_ext.
      simpl.
      intuition idtac.
      exists nil; simpl; intuition idtac.
      unfold is_state.
      rewrite H1.
      step auto_ext.
      auto.

      do 2 esplit; eauto.
      hnf; intros.
      simpl.
      clear_fancy.
      evaluate auto_ext.
      intuition idtac.
      exists nil; simpl; intuition.
      step auto_ext.

      apply IHexpr2 in H2; clear IHexpr2.
      Focus 2.
      hnf; intros.
      apply H.
      apply union_spec; auto.
      destruct H2; propxFo.
      apply IHexpr1 in H2; clear IHexpr1.
      Focus 2.
      hnf; intros.
      apply H.
      apply union_spec; auto.
      destruct H2; intuition.
      do 2 esplit; eauto.
      hnf; simpl; intros.
      unfold is_state in H1; simpl in H1.

      Lemma evalInstrs_write_temp : forall sm x base',
        evalInstrs sm x (Assign (temp_slot vars base') Rv :: nil)
        = evalInstrs sm x (Assign (LvMem (Imm (Regs x Sp ^+ $8 ^+ $(4 * length vars) ^+ $4 ^* natToW base'))) Rv :: nil).
        Transparent evalInstrs.
        simpl.
        intros.
        replace (Regs x Sp ^+ natToW (temp_start vars + 4 * base'))
          with (Regs x Sp ^+ $ (8) ^+ $(4 * length vars) ^+ $4 ^* natToW base'); auto.
        rewrite natToW_plus.
        unfold temp_start, vars_start.
        change (4 * 2) with 8.
        rewrite natToW_plus.
        unfold natToW.
        rewrite (Mult.mult_comm 4 base').
        change (natToWord 32 (base' * 4)) with (natToW (base' * 4)).
        rewrite (natToW_times4 base').
        unfold natToW.
        words.
        Opaque evalInstrs.
      Qed.

      Lemma evalInstrs_binop_temp : forall sm x base' b,
        evalInstrs sm x (IL.Binop Rv (temp_slot vars base') b Rv :: nil)
        = evalInstrs sm x (IL.Binop Rv (LvMem (Imm (Regs x Sp ^+ $8 ^+ $(4 * length vars) ^+ $4 ^* natToW base'))) b Rv :: nil).
        Transparent evalInstrs.
        simpl.
        intros.
        replace (Regs x Sp ^+ natToW (temp_start vars + 4 * base'))
          with (Regs x Sp ^+ $ (8) ^+ $(4 * length vars) ^+ $4 ^* natToW base'); auto.
        rewrite natToW_plus.
        unfold temp_start, vars_start.
        change (4 * 2) with 8.
        rewrite natToW_plus.
        unfold natToW.
        rewrite (Mult.mult_comm 4 base').
        change (natToWord 32 (base' * 4)) with (natToW (base' * 4)).
        rewrite (natToW_times4 base').
        unfold natToW.
        words.
        Opaque evalInstrs.
      Qed.

      rewrite evalInstrs_write_temp in H6.
      assert (natToW base < natToW (length temps))%word.
      apply lt_goodSize.
      assert (max (depth expr1) (S (depth expr2)) > 0).
      generalize (Max.le_max_r (depth expr1) (S (depth expr2))).
      omega.
      omega.
      apply goodSize_weaken with (length temps); eauto.
      eauto.
      apply H7 in H1; clear H7.
      apply H1 in H8; clear H1.
      destruct H8 as [ ? [ ? [ ? [ ] ] ] ]; simpl in *.
      generalize dependent H5; generalize dependent H4; generalize dependent H3.
      clear_fancy.
      unfold is_state in H7; simpl in H7.
      assert (natToW base < natToW (length (upd_sublist temps base x4)))%word.
      rewrite length_upd_sublist; assumption.
      evaluate auto_ext.
      intros.
      hnf in H14.
      assert (interp specs0 (![is_state ((sm, x1)) # (Sp) vs
        (Array.upd (upd_sublist temps base x4) base (eval vs expr1))* other] (sm, x1))).
      unfold is_state; simpl.
      clear_fancy; step auto_ext.
      replace (Regs x2 Sp) with (Regs x1 Sp) by words.
      step auto_ext.
      apply H14 in H15; clear H14.
      destruct H15 as [ ? [ ? [ ? [ ] ] ] ]; simpl in *.      
      rewrite evalInstrs_binop_temp in H13.
      clear_fancy.
      destruct b.
      assert (natToW base < natToW (length (upd_sublist
        (Array.upd (upd_sublist temps base x4) base
          (eval vs expr1)) (S base) x5)))%word.
      rewrite length_upd_sublist; rewrite upd_length; assumption.
      clear H11; unfold is_state in H15.
      evaluate auto_ext.
      intuition idtac.
      congruence.

      Lemma selN_updN_eq : forall a p v,
        p < length a
        -> selN (updN a p v) p = v.
        induction a; simpl; intuition.
        destruct p; simpl; intuition.
      Qed.

      Lemma sel_upd_eq : forall a p v,
        p < length a
        -> goodSize (length a)
        -> Array.sel (Array.upd a p v) p = v.
        unfold Array.sel, Array.upd; intros.
        apply selN_updN_eq; auto.
        rewrite wordToNat_natToWord_idempotent; auto.
        change (goodSize p).
        eapply goodSize_weaken; eauto.
      Qed.

      Lemma selN_updN_ne : forall a p v p',
        p <> p'
        -> selN (updN a p v) p' = selN a p'.
        induction a; simpl; intuition.
        destruct p, p'; simpl; intuition.
      Qed.

      Lemma sublist_irrel : forall base, goodSize base
        -> forall v base' a,
          base < base'
          -> Array.sel (upd_sublist a base' v) base = Array.sel a base.
        induction v; simpl; intuition.
        rewrite IHv; auto.
        rewrite sel_selN by auto.
        rewrite selN_updN_ne; try omega.
        unfold Array.sel.
        rewrite wordToNat_natToWord_idempotent; auto.
      Qed.

      rewrite sublist_irrel in H19.
      rewrite sel_upd_eq in H19.
      simpl.
    Admitted.      

    admit.
    admit.
  Defined.

End ExprComp.
