Require Import SyntaxExpr SemanticsExpr Syntax Semantics.
Require Import SemanticsExprLemmas.
Require Import ExprLemmas VariableLemmas GeneralTactics.
Require Import Arith.

Section Safe_coind.
  Variable R : Statement -> st -> Prop.

  Import WMake.

  Hypothesis ReadAtCase : forall var arr idx vs arrs, R (Syntax.ReadAt var arr idx) (vs, arrs) -> safe_access arrs (exprDenote arr vs) (exprDenote idx vs).

  Hypothesis WriteAtCase : forall arr idx val vs arrs, R (Syntax.WriteAt arr idx val) (vs, arrs) -> safe_access arrs (exprDenote arr vs) (exprDenote idx vs).

  Hypothesis SeqCase : forall a b v, R (Syntax.Seq a b) v -> R a v /\ forall v', RunsTo functions a v v' -> R b v'.

  Hypothesis ConditionalCase : forall cond t f v, R (Syntax.Conditional cond t f) v -> (wneb (exprDenote cond (fst v)) $0 = true /\ R t v) \/ (wneb (exprDenote cond (fst v)) $0 = false /\ R f v).

  Hypothesis LoopCase : forall cond body v, R (Syntax.Loop cond body) v -> (wneb (exprDenote cond (fst v)) $0 = true /\ R body v /\ (forall v', RunsTo functions body v v' -> R (Loop cond body) v')) \/ (wneb (exprDenote cond (fst v)) $0 = false).

  Hypothesis MallocCase : forall var size vs arrs, R (Syntax.Malloc var size) (vs, arrs) -> goodSize (wordToNat (exprDenote size vs) + 2).

  Hypothesis FreeCase : forall arr vs arrs, R (Syntax.Free arr) (vs, arrs) -> (exprDenote arr vs) %in (fst arrs).

  Hypothesis LenCase : forall var arr vs arrs, R (Syntax.Len var arr) (vs, arrs) -> (exprDenote arr vs) %in (fst arrs).

  Hypothesis ForeignCallCase : forall vs arrs f arg,
    R (Syntax.Call f arg) (vs, arrs)
    -> (exists spec arrs', functions (exprDenote f vs) = Some (Foreign spec)
      /\ spec {| Arg := exprDenote arg vs; InitialHeap := arrs; FinalHeap := arrs' |}) \/
    (exists body, functions (exprDenote f vs) = Some (Internal body) /\ forall vs_arg, Locals.sel vs_arg "__arg" = exprDenote arg vs -> R body (vs_arg, arrs)).

  Hint Constructors Safe.

  Ltac openhyp := 
    repeat match goal with
             | H : _ /\ _ |- _  => destruct H
             | H : _ \/ _ |- _ => destruct H
             | H : exists x, _ |- _ => destruct H
           end.

  Ltac break_pair :=
    match goal with
      V : (_ * _)%type |- _ => destruct V
    end.

  Theorem Safe_coind : forall c v, R c v -> Safe c v.
    cofix; unfold st; intros; break_pair; destruct c.

    eauto.
    Guarded.

    eapply ReadAtCase in H; openhyp; eauto.
    Guarded.

    eapply WriteAtCase in H; openhyp; eauto.
    Guarded.

    eapply SeqCase in H; openhyp; eauto.
    Guarded.

    eauto.
    Guarded.

    eapply ConditionalCase in H; openhyp; eauto.
    Guarded.

    eapply LoopCase in H; openhyp; eauto.
    Guarded.

    eapply MallocCase in H; openhyp; eauto.
    Guarded.

    eapply FreeCase in H; openhyp; eauto.
    Guarded.

    eapply LenCase in H; openhyp; eauto.
    Guarded.

    eapply ForeignCallCase in H; openhyp; eauto.
    Guarded.
  Qed.

End Safe_coind.

Fixpoint footprint (statement : Statement) :=
  match statement with
    | Syntax.Assignment var val => var :: varsIn val
    | Syntax.Seq a b => footprint a ++ footprint b
    | Syntax.Skip => nil
    | Syntax.Conditional cond t f => varsIn cond ++ footprint t ++ footprint f
    | Syntax.Loop cond body => varsIn cond ++ footprint body
    | Syntax.ReadAt var arr idx => var :: varsIn arr ++ varsIn idx 
    | Syntax.WriteAt arr idx val => varsIn arr ++ varsIn idx ++ varsIn val
    | Syntax.Malloc var size => var :: varsIn size
    | Syntax.Free arr => varsIn arr
    | Syntax.Len var arr => var :: varsIn arr
    | Syntax.Call f arg => varsIn f ++ varsIn arg
  end.

Ltac pattern_r := 
  match goal with
    |- _ = ?A => pattern A
  end.

Ltac pattern_l := 
  match goal with
    |- ?A = _ => pattern A
  end.

Ltac rv_solver := 
  match goal with
    | H : Regs ?ST Rv = exprDenote ?E _ |- Regs ?ST Rv = exprDenote ?E _ => pattern_l; rewriter
    | H : Regs ?ST Rv = exprDenote ?E _ |- exprDenote ?E _ = Regs ?ST Rv => pattern_r; rewriter
    | H : exprDenote ?E _ = Regs ?ST Rv |- Regs ?ST Rv = exprDenote ?E _ => pattern_l; rewriter_r
    | H : exprDenote ?E _ = Regs ?ST Rv |- exprDenote ?E _ = Regs ?ST Rv => pattern_r; rewriter_r
  end.

Ltac clear_inv :=
  repeat match goal with
           | H : _ |- _ => unfold H in *; clear H
           | H : _ |- _ => rewrite <- H in *; clear H
         end.

Ltac use_changed_trans2 :=
  match goal with
    | H1 : changed_in ?VS1 ?VS2 ?A, 
      H2 : changed_in ?VS2 ?VSF ?B
      |- changed_in ?VS1 ?VSF ?FF => eapply (@changedVariables_trans VS1 VS2 VSF A FF FF H1); try eapply (@changedVariables_incl VS2 VSF B FF H2)
  end.

Ltac use_changed_unchanged :=
  match goal with
    H : changed_in ?VS1 ?VS2 _ |- unchanged_in ?VS1 ?VS2 _ => eapply (changed_unchanged H)
  end.

Ltac use_changed_unchanged' :=
  match goal with
    H : changed_in ?VS1 ?VS2 _ |- unchanged_in ?VS2 ?VS1 _ => eapply unchanged_in_symm; eapply (changed_unchanged H)
  end.

Ltac use_changed_trans3 :=
  match goal with
    | H1 : changed_in ?VS1 ?VS2 ?A, 
      H2 : changed_in ?VS2 ?VS3 ?B,
      H3 : changed_in ?VS3 ?VSF ?C
      |- changed_in ?VS1 ?VSF ?FF => eapply (@changedVariables_trans VS1 VS2 VSF A FF FF H1); try eapply (@changedVariables_trans VS2 VS3 VSF B FF FF H2); try eapply (@changedVariables_incl VS3 VSF C FF H3)
  end.

Ltac use_changed_trans4 :=
  match goal with
    | H1 : changed_in ?VS1 ?VS2 ?A, 
      H2 : changed_in ?VS2 ?VS3 ?B,
      H3 : changed_in ?VS3 ?VS4 ?C,
      H4 : changed_in ?VS4 ?VSF ?D
      |- changed_in ?VS1 ?VSF ?FF => eapply (@changedVariables_trans VS1 VS2 VSF A FF FF H1); try eapply (@changedVariables_trans VS2 VS3 VSF B FF FF H2); try eapply (@changedVariables_trans VS3 VS4 VSF C FF FF H3); try eapply (@changedVariables_incl VS4 VSF D FF H4)
  end.

Ltac use_changed_incl :=
  match goal with
    H : changed_in ?VS1 ?VS2 ?A |- changed_in ?VS1 ?VS2 ?B => eapply (changedVariables_incl H)
  end.

Ltac use_changed_upd_fwd := 
  match goal with
    | H : changedVariables ?VS1 ?VS2 ?A |- changedVariables ?VS1 _ ?C => 
      match C with
        context [ _ :: _ ] => eapply (@changedVariables_trans VS1 VS2 _ A _ C H); try eapply changedVariables_upd_fwd
      end
  end.

Ltac use_disjoint_trans_lr :=
  match goal with
    H : disjoint ?A ?B |- disjoint ?C (tempVars ?D) =>
      match A with context [ C ] =>
        match B with context [ D ] =>
          eapply (@disjoint_trans_lr _ A B C (tempVars D) H)
        end end end.

Ltac RunsTo_solver := 
  match goal with
    | |- RunsTo _ (Seq _ _) _ _ => econstructor 2
  end.

Ltac open_hyp := repeat openHyp.

Ltac condition_solver' :=  
  match goal with
    H : wneb _ _ = ?A |- wneb _ _ = ?A => rewriter_r; f_equal
  end.

Ltac use_unchanged_in_symm :=
  match goal with
    H : unchanged_in ?VS1 ?VS2 ?A |- unchanged_in ?VS2 ?VS1 ?A => eapply unchanged_in_symm; assumption
  end.

Ltac use_changed_in_symm :=
  match goal with
    H : changed_in ?VS1 ?VS2 ?A |- changed_in ?VS2 ?VS1 ?A => eapply changedVariables_symm; assumption
  end.

Ltac break_pair :=
  match goal with
    V : (_ * _)%type |- _ => destruct V
  end.

Ltac generalize_except t :=
  repeat
    match goal with
      H : _ |- _ => not_eq t H; generalize H; clear H
    end.

Ltac inv_clear H := generalize_except H; inversion H; clear H; clear_inv; intros.

Ltac inv_Safe_clear :=
  match goal with
    H : Safety.Safe _ _ _ |- _ => inv_clear H
  end.

Ltac f_equal_expr :=
  match goal with
    |- context [exprDenote ?E ?VS1] =>
    match goal with
      |- context [exprDenote ?E ?VS2] => not_eq VS1 VS2; replace (exprDenote E VS2) with (exprDenote E VS1)
    end
  end; [try f_equal_expr | .. ].

Lemma unchanged_exprDenote : forall expr vs1 vs2, 
  unchanged_in vs1 vs2 (varsIn expr) ->
  exprDenote expr vs2 = exprDenote expr vs1.
  unfold unchanged_in; induction expr; simpl; intuition; f_equal; intuition; f_equal_expr; intuition.
Qed.

Ltac rewrite_expr :=
  match goal with
    | H : context [exprDenote ?E ?VS1] |- context [exprDenote ?E ?VS2] => not_eq VS1 VS2; rewrite (unchanged_exprDenote _ VS1 VS2)
  end.

Section functions.
Variable functions : W -> option Callee.

Inductive runs_loop_partially cond body : st -> st -> Prop :=
| LoopPartialEmtpy : forall v, 
  runs_loop_partially cond body v v
| LoopPartialStep : forall v v' v'', 
  runs_loop_partially cond body v v' -> 
  wneb (exprDenote cond (fst v')) $0 = true -> 
  RunsTo functions body v' v'' -> 
  runs_loop_partially cond body v v''.

Ltac use_runs_loop_partially_cons :=
  match goal with
    H : runs_loop_partially ?E ?B ?ST _ |- runs_loop_partially ?E ?B ?ST _ => econstructor 2
  end.

Ltac pre_eauto := try first [
  use_runs_loop_partially_cons | 
  use_changed_trans4 | 
  use_changed_trans3 | 
  use_changed_trans2 | 
  use_changed_upd_fwd | 
  use_changed_incl |
  use_disjoint_trans_lr | 
  RunsTo_solver |
  eapply incl_app].

Section HintsSection.

  Hint Rewrite sum_S : arith.
  Hint Resolve S_le_lt.
  Hint Resolve sel_upd_firstn.
  Hint Resolve firstn_S_upd.
  Hint Resolve noChange.
  Hint Resolve Max.le_max_l Max.le_max_r.
  Hint Resolve incl_app_backl incl_app_backr.
  Hint Resolve in_or_app. 
  Hint Extern 12 => rv_solver.
  Hint Extern 12 => sp_solver.
  Hint Resolve le_plus_lt lt_max_l lt_max_r.
  Hint Resolve plus_le.
  Hint Resolve lt_le_S plus_lt.

  Hint Resolve in_or_app in_eq In_incl.
  Hint Resolve List.incl_cons incl_cons_l incl_cons_r incl_app incl_appl incl_appr incl_refl incl_array incl_tran incl_nil incl_tl.
  Hint Immediate incl_cons_back.
  Hint Resolve disjoint_trans_lr.
  Hint Resolve changedVariables_upd.
  Hint Resolve unchanged_in_except_disjoint unchanged_in_except_upd unchanged_in_except_shrink.
  Hint Constructors or.
  Hint Resolve sel_upd_eq.

  Hint Constructors RunsTo.
  Hint Constructors runs_loop_partially.
  Hint Resolve unchanged_exprDenote.
  Hint Resolve changedVariables_upd_bwd.
  Hint Resolve unchanged_incl.
  Hint Resolve two_merge_equiv.
  Hint Resolve changed_in_upd_same.

  Hint Extern 12 (unchanged_in _ _ _) => use_changed_unchanged.
  Hint Extern 12 (unchanged_in _ _ _) => use_changed_unchanged'.
  Hint Extern 12 (changed_in _ _ _) => use_changed_trans2.
  Hint Extern 12 (changed_in _ _ _) => use_changed_incl.
  Hint Extern 12 => condition_solver'.
  Hint Extern 12 (unchanged_in _ _ _) => use_unchanged_in_symm.
  Hint Extern 12 (changed_in _ _ _) => use_changed_in_symm.

  Lemma runs_loop_partially_finish' : forall e b v v', 
    runs_loop_partially e b v v' -> 
    forall v'',
      RunsTo functions (Loop e b) v' v''  -> 
      RunsTo functions (Loop e b) v v''.
    induction 1; eauto.
  Qed.

  Lemma runs_loop_partially_finish : forall e b v v', 
    runs_loop_partially e b v v' -> 
    wneb (exprDenote e (fst v')) $0 = false -> 
    RunsTo functions (Loop e b) v v'.
    intros; eapply runs_loop_partially_finish'; eauto.
  Qed.

  Hint Resolve runs_loop_partially_finish.

  Lemma exprDenote_disjoint : forall expr vs1 vs2 changed, 
    changedVariables vs1 vs2 changed ->  
    disjoint (varsIn expr) changed -> 
    exprDenote expr vs2 = exprDenote expr vs1.
    eauto.
  Qed.

  Hint Resolve exprDenote_disjoint.

  Lemma RunsTo_footprint : forall statement vs1 vs2,
    RunsTo functions statement vs1 vs2 ->
    changed_in (fst vs1) (fst vs2) (footprint statement).
    induction 1; intros; simpl in *; clear_inv; pre_eauto; eauto.
  Qed.

  Hint Resolve RunsTo_footprint.

  Lemma unchanged_in_eval : forall x v' vs1' a b,
    equiv x (merge v' vs1' a) ->
    unchanged_in_except vs1' v' (a ++ b) a ->
    unchanged_in v' x b.
    intros.
    eapply unchanged_in_equiv.
    eauto.
    eapply unchanged_in_symm.
    eapply changed_back.
    eapply unchanged_in_except_symm.
    eapply unchanged_in_except_shrink; eauto.
  Qed.

  Lemma changed_unchanged_unchanged_except : forall vs1 vs2 vs3 a b,
    unchanged_in vs1 vs2 a ->
    changed_in vs2 vs3 b ->
    unchanged_in_except vs1 vs3 a b.
    intros.
    eapply changed_in_unchanged_in_except'.
    eapply unchanged_in_unchanged_in_except; eauto.
    eapply changedVariables_symm; eauto.
  Qed.

  Ltac protect_hyp :=
    repeat 
      match goal with 
        | H : snd _ = _ |- _ => generalize dependent H
        | H : length _ = _ |- _ => generalize dependent H
      end.

  Lemma RunsTo_immune : forall statement vs1 vs2,
    RunsTo functions statement vs1 vs2 ->
    forall vs1', unchanged_in (fst vs1) (fst vs1') (footprint statement) ->
    snd vs1' = snd vs1 ->
    exists vs2',
      RunsTo functions statement vs1' vs2' 
      /\ equiv (fst vs2') (merge (fst vs2) (fst vs1') (footprint statement))
      /\ snd vs2' = snd vs2.
    induction 1; intros; simpl in *; protect_hyp; clear_inv; intros.
    Focus 8.
    (* loop - true *)
    destruct (IHRunsTo1 vs1').
    eauto.
    eauto.
    open_hyp.
    destruct (IHRunsTo2 x).
    eapply unchanged_in_eval.
    eauto.
    eapply changed_unchanged_unchanged_except.
    eapply unchanged_incl.
    eapply unchanged_in_symm; eauto.
    repeat eapply incl_app; eauto.
    eauto.
    eauto.
    open_hyp.
    descend.
    econstructor 8.
    eauto.
    eauto.
    eauto.
    eapply equiv_trans.
    eauto.
    eapply two_merge_equiv.
    eapply changedVariables_symm; eauto.
    eauto.
    eauto.

    (* assign *)
    break_pair; simpl in *.
    descend.
    eauto.
    eapply equiv_merge.
    erewrite unchanged_exprDenote; eauto.
    eapply unchanged_in_upd_same.
    eapply unchanged_in_symm; eauto.
    simpl; eapply changedVariables_trans; eauto.
    simpl; eauto.

    (* read *)
    break_pair; simpl in *.
    rewrite H1 in *.
    descend.
    econstructor 2.
    repeat rewrite_expr; eauto.
    simpl.
    eapply equiv_merge.
    repeat rewrite_expr; eauto.
    eapply unchanged_in_upd_same.
    eapply unchanged_in_symm; eauto.
    simpl; eapply changedVariables_trans; eauto.
    simpl; eauto.

    (* write *)
    break_pair; simpl in *.
    rewrite H1 in *.
    descend.
    econstructor 3.
    repeat rewrite_expr; eauto.
    simpl.
    eapply equiv_merge.
    eauto.
    eauto.
    simpl; eauto.
    repeat rewrite_expr; eauto.
    repeat (f_equal; eauto).

    (* seq *)
    destruct (IHRunsTo1 vs1').
    eauto.
    eauto.
    open_hyp.
    destruct (IHRunsTo2 x).
    Focus 3.
    open_hyp.
    descend.
    eauto.
    eapply equiv_eval.
    eauto.
    eauto.
    eapply unchanged_in_unchanged_except.
    Focus 2.
    eauto.
    eapply changed_in_unchanged_in_except.
    eauto.
    eapply changed_in_unchanged_in_except.
    eauto.
    eauto.
    eapply unchanged_in_eval.
    eauto.
    eapply changed_unchanged_unchanged_except.
    eapply unchanged_incl.
    eapply unchanged_in_symm; eauto.
    eauto.
    eauto.
    eauto.

    (* skip *)
    descend.
    eauto.
    eapply changed_merge_fwd.
    eauto.

    (* conditional - true *)
    destruct (IHRunsTo vs1').
    eauto.
    eauto.
    open_hyp.
    descend.
    econstructor 6; eauto.
    eapply equiv_trans.
    eauto.
    eapply equiv_merge.
    eapply changed_back.
    eapply unchanged_in_except_trans.
    eapply changed_in_unchanged_in_except.
    Focus 2.
    eapply unchanged_in_unchanged_in_except.
    eauto.
    eapply changedVariables_symm; eauto.
    eauto.
    eauto.
    eapply changedVariables_incl.
    eapply changed_merge_bwd.
    eauto.
    eauto.

    (* conditional - false *)
    destruct (IHRunsTo vs1').
    eauto.
    eauto.
    open_hyp.
    descend.
    econstructor 7; eauto.
    eapply equiv_trans.
    eauto.
    eapply equiv_merge.
    eapply changed_back.
    eapply unchanged_in_except_trans.
    eapply changed_in_unchanged_in_except.
    Focus 2.
    eapply unchanged_in_unchanged_in_except.
    eauto.
    eapply changedVariables_symm; eauto.
    eauto.
    eauto.
    eapply changedVariables_incl.
    eapply changed_merge_bwd.
    eauto.
    eauto.

    (* loop - false *)
    descend.
    econstructor 9; eauto.
    eapply equiv_merge; eauto.
    eauto.

    (* malloc *)
    break_pair; simpl in *.
    rewrite H3 in *.
    descend.
    econstructor 10.
    eauto.
    repeat rewrite_expr; eauto.
    repeat rewrite_expr; eauto.
    simpl.
    eapply equiv_merge.
    eapply unchanged_in_upd_same.
    eapply unchanged_in_symm; eauto.
    simpl; eapply changedVariables_trans; eauto.
    simpl; eauto.
    repeat (f_equal; eauto).

    (* free *)
    break_pair; simpl in *.
    rewrite H1 in *.
    descend.
    econstructor 11.
    repeat rewrite_expr; eauto.
    simpl.
    eapply equiv_merge.
    eauto.
    eauto.
    simpl.
    repeat (f_equal; eauto).

    (* len *)
    break_pair; simpl in *.
    rewrite H1 in *.
    descend.
    econstructor 12.
    repeat rewrite_expr; eauto.
    simpl.
    eapply equiv_merge.
    repeat rewrite_expr; eauto.
    eapply unchanged_in_upd_same.
    eapply unchanged_in_symm; eauto.
    simpl; eapply changedVariables_trans; eauto.
    simpl; eauto.

    (* call foreign *)
    break_pair; simpl in *.
    subst.
    descend.
    econstructor; try rewrite_expr; eauto.
    simpl.
    eapply equiv_merge.
    eapply unchanged_in_symm; eauto.
    eauto.
    simpl; eauto.

    (* call internal *)
    break_pair; simpl in *.
    subst.
    descend.
    econstructor 14; try rewrite_expr; eauto.
    simpl.
    eapply equiv_merge.
    eapply unchanged_in_symm; eauto.
    eauto.
    simpl; eauto.
  Qed.

  Lemma changed_in_eval : forall x11 x7 x4 x6 inner outer,
    equiv x11 (merge x6 x4 inner) ->
    changed_in x4 x6 (inner ++ outer) ->
    changed_in x6 x7 outer ->
    changed_in x11 x7 outer.
    intros.
    eapply changed_trans.
    eapply changedVariables_incl; eauto.
    eapply changed_trans.
    eapply changed_merge; eauto.
    eauto.
  Qed.

  Import Safety.

  Lemma Safe_immune : forall statement vs1 vs2 arrs,
    Safe functions statement (vs1, arrs) ->
    unchanged_in vs1 vs2 (footprint statement) ->
    Safe functions statement (vs2, arrs).

    intros.
    eapply (Safe_coind (fun c v2 => exists v1, Safe functions c v1 /\ unchanged_in (fst v1) (fst v2) (footprint c) /\ snd v1 = snd v2)).

    intros.
    openhyp.
    inversion H1; clear_inv.
    simpl in *.
    rewriter_r.
    repeat rewrite_expr; eauto.
    Guarded.

    intros.
    openhyp.
    inversion H1; clear_inv.
    simpl in *.
    rewriter_r.
    repeat rewrite_expr; eauto.
    Guarded.

    intros.
    openhyp.
    simpl in *.
    inversion H1; protect_hyp; clear_inv; intros.
    split.
    eexists; eauto.
    intros.

    Ltac change_RunsTo :=
      match goal with
        H : RunsTo _ _ ?V1 _, H2 : unchanged_in (fst ?V2) (fst ?V1) _ |- _ => 
          generalize H; eapply RunsTo_immune with (vs1' := V2) in H; intros
      end.

    change_RunsTo.
    Focus 2.
    eapply unchanged_in_symm; eauto.
    Focus 2.
    eauto.
    openhyp.
    exists x0.
    split.
    eauto.
    split.
    eapply unchanged_in_symm.
    eapply unchanged_in_eval.
    eauto.
    eapply changed_unchanged_unchanged_except.
    eapply unchanged_incl.
    eauto.
    repeat eapply incl_app; eauto.
    eauto.
    eauto.
    Guarded.
    
    Focus 2.
    intros.
    openhyp.
    simpl in *.
    inversion H1.
    unfold statement1 in *; clear statement1.
    unfold statement2 in *; clear statement2.
    rewrite <- H4 in *; clear H4.
    rewrite <- H5 in *; clear H5.
    rewrite <- H8 in *; clear H8.
    left.
    repeat split.
    repeat rewrite_expr; eauto.
    eexists; eauto.
    intros.
    change_RunsTo.
    Focus 2.
    eapply unchanged_in_symm; eauto.
    Focus 2.
    eauto.
    openhyp.
    exists x0.
    split.
    eauto.
    split.
    eapply unchanged_in_symm.
    eapply unchanged_in_eval.
    eauto.
    eapply changed_unchanged_unchanged_except.
    eapply unchanged_incl.
    eauto.
    repeat eapply incl_app; eauto.
    eauto.
    eauto.
    Guarded.
    
    rewrite <- H4 in *; clear H4.
    rewrite <- H5 in *; clear H5.
    rewrite <- H6 in *; clear H6.
    right.
    repeat rewrite_expr; eauto.
    
    intros.
    openhyp.
    simpl in *.
    inversion H1.
    rewrite <- H4 in *; clear H4.
    rewrite <- H5 in *; clear H5.
    rewrite <- H6 in *; clear H6.
    rewrite <- H7 in *; clear H7.
    left.
    repeat split.
    repeat rewrite_expr; eauto.
    eexists.
    split.
    eauto.
    split.
    eauto.
    eauto.
    rewrite <- H4 in *; clear H4.
    rewrite <- H5 in *; clear H5.
    rewrite <- H6 in *; clear H6.
    rewrite <- H7 in *; clear H7.
    right.
    repeat split.
    repeat rewrite_expr; eauto.
    eexists.
    split.
    eauto.
    split.
    eauto.
    eauto.
    Guarded.

    intros.
    openhyp.
    simpl in *.
    inversion H1.
    unfold size_v in *; clear size_v.
    rewrite <- H4 in *; clear H4.
    rewrite <- H6 in *; clear H6.
    rewrite <- H5 in *; clear H5.
    simpl in *.
    repeat rewrite_expr; eauto.
    Guarded.

    intros.
    openhyp.
    simpl in *.
    inversion H1.
    unfold arr_v in *; clear arr_v.
    rewrite <- H4 in *; clear H4.
    rewrite <- H6 in *; clear H6.
    simpl in *.
    rewriter_r.
    repeat rewrite_expr; eauto.
    Guarded.

    intros.
    openhyp.
    simpl in *.
    inversion H1.
    unfold arr_v in *; clear arr_v.
    rewrite <- H4 in *; clear H4.
    rewrite <- H6 in *; clear H6.
    rewrite <- H5 in *; clear H5.
    simpl in *.
    repeat rewrite_expr; eauto.
    Guarded.

    intros.
    openhyp.
    simpl in *.
    subst.
    inversion H1.
    subst.
    unfold arg_v in *.
    openhyp.
    simpl; eauto.
    left.
    repeat esplit; try rewrite_expr; eauto.
    subst.
    unfold arg_v in *.
    openhyp.
    simpl; eauto.
    right.
    repeat esplit; try rewrite_expr; eauto.
    simpl in *.
    instantiate (1 := vs_arg).
    eapply changed_unchanged.
    instantiate (1 := nil).
    Lemma upd_no_effect : forall vs s a, sel vs s = a -> changed_in (upd vs s a) vs nil.
      clear; intros; unfold changedVariables; intros; destruct (string_dec x s); contradict H0.
      rewriter; rewrite sel_upd_eq; eauto.
      rewrite sel_upd_ne; eauto.
    Qed.
    eapply upd_no_effect.
    rewrite_expr; eauto.
    eapply unchanged_in_symm.
    eauto.
    eapply disjoint_nil_r.

    eauto.
  Qed.

  Lemma true_false_contradict : forall b, b = true -> b = false -> False.
    intros; destruct b; intuition.
  Qed.

  Hint Resolve true_false_contradict.

  Lemma Safe_cond_true : forall cond t f v, Safe functions (Syntax.Conditional cond t f) v -> wneb (exprDenote cond (fst v)) $0 = true -> Safe functions t v.
    intros; inv_Safe_clear; [ | contradict H4 ]; eauto.
  Qed.

  Lemma Safe_cond_false : forall cond t f v, Safe functions (Syntax.Conditional cond t f) v -> wneb (exprDenote cond (fst v)) $0 = false -> Safe functions f v.
    intros; inv_Safe_clear; [ contradict H4 | ]; eauto.
  Qed.

  Lemma runs_loop_partially_safe : forall cond body v v', 
    runs_loop_partially cond body v v' -> 
    Safe functions (Loop cond body) v -> 
    Safe functions (Loop cond body) v'.
    induction 1.
    eauto.

    intros.
    eapply IHruns_loop_partially in H2.
    inv_Safe_clear; eauto.
    contradict H3; eauto.
  Qed.
    
  Lemma runs_loop_partially_body_safe : forall cond body v v', 
    runs_loop_partially cond body v v' -> 
    Safe functions (Loop cond body) v -> 
    wneb (exprDenote cond (fst v')) $0 = true -> 
    Safe functions body v'.
    intros.
    eapply runs_loop_partially_safe in H.
    2 : eauto.
    clear H0.
    inv_Safe_clear; eauto.
    contradict H3; eauto.
  Qed.

  Print Assumptions Safe_immune.
  Print Assumptions RunsTo_immune.
  Print Assumptions runs_loop_partially_safe.

End HintsSection.
End functions.
