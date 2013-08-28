Require Import SyntaxExpr SemanticsExpr.
Require Import Syntax Semantics SyntaxNotations.
Require Import VariableLemmas.
Require Import Depth Footprint.
Require Import GeneralTactics.
Require Import ExprLemmas.
Require Import SemanticsLemmas.
Require Import Arith.

Open Scope nat.

Lemma le_max_l_trans : forall a b c, (a <= b -> a <= max b c)%nat.
  intros; eapply le_trans.
  2: eapply Max.le_max_l.
  eauto.
Qed.

Lemma le_max_r_trans : forall a b c, (a <= c -> a <= max b c)%nat.
  intros; eapply le_trans.
  2: eapply Max.le_max_r.
  eauto.
Qed.

Ltac max_le_solver :=
  repeat 
    match goal with
      | |- ?A <= ?A => eapply le_n
      | |- max ?A ?B <= _ => eapply Max.max_lub
      | |- ?S <= max ?A _ =>
        match A with
          context [ S ] => eapply le_max_l_trans
        end
      | |- ?S <= max _ ?B =>
        match B with
          context [ S ] => eapply le_max_r_trans
        end
    end.

Ltac incl_app_solver :=
  repeat 
    match goal with
      | |- List.incl ?A ?A => eapply List.incl_refl
      | |- List.incl (?A ++ ?B) _ => eapply incl_app
      | |- List.incl (?A :: ?B) _ => eapply List.incl_cons
      | |- List.incl ?S (?A ++ _) =>
        match A with
          context [ S ] => eapply incl_appl
        end
      | |- List.incl ?S (_ ++ ?B) =>
        match B with
          context [ S ] => eapply incl_appr
        end
      | |- List.incl ?S (?A :: _) =>
        match A with
          context [ S ] => eapply (@incl_appl _ _ _ (_ :: nil))
        end
      | |- List.incl ?S (?A :: ?B) =>
        match B with
          context [ S ] => eapply (@incl_appr _ _ (_ :: nil))
        end
    end.

Ltac change_RunsTo_for_goal :=
  match goal with
    H : RunsTo _ ?S ?VS1 _ |- context [ RunsTo _ ?S ?VS1' _ ] => generalize H; eapply RunsTo_immune with (vs1' := VS1') in H; intros
  end.

Ltac apply_in_all t :=
  repeat match goal with
           H : _ |- _ => eapply t in H
         end.

Ltac use_changed_in_eval :=
  match goal with
    H : VariableLemmas.equiv ?V (merge _ _ _) |- changed_in ?V _ _ =>
      apply_in_all RunsTo_footprint; eapply changed_in_eval; [eassumption | ..]
  end.

Ltac auto_apply_in t :=
  match goal with
    H : _ |- _ => eapply t in H
  end.

Ltac use_disjoint_trans'' := 
  match goal with
    | H : disjoint ?A ?B |- disjoint ?C _ =>
      match A with context [ C ] =>
        eapply (@disjoint_trans_lr _ A B C _ H)
      end 
    | H : disjoint ?A ?B |- disjoint (?C1 ++ ?C2) _ =>
      match A with context [ C1 ] =>
        match A with context [ C2 ] =>
          eapply (@disjoint_trans_lr _ A B (C1 ++ C2) _ H)
        end
      end 
  end.

Ltac change_RunsTo_to t :=
  match goal with
    H : RunsTo _ ?S ?VS1 _ |- _ => generalize H; eapply RunsTo_immune with (vs1' := t) in H; intros
  end.

Section Hints.

  Definition RunsToRelax fs s v v_new := 
    exists v', RunsTo fs s v v' 
      /\ changed_in (fst v') (fst v_new) (tempVars (depth s))
      /\ snd v_new = snd v'.

  Local Notation "fs ~:~ v1 ~~ s ~~> v2" := (RunsToRelax fs s v1 v2) (no associativity, at level 60).
  Local Notation "v [( e )]" := (exprDenote e (fst v)) (no associativity, at level 60).
  Local Notation agree_except := changed_in.
  Local Notation "'tmps' s" := (tempVars (depth s)) (at level 60).
  Local Notation edepth := DepthExpr.depth.
  Local Notation "'etmps' s" := (tempVars (edepth s)) (at level 60).
  Local Notation "v [ e ]" := (exprDenote e v) (no associativity, at level 60).
  Local Notation "b [ vars => c ]" := (merge c b vars) (no associativity, at level 60).
  Local Notation agree_except_trans := changedVariables_trans.
  Local Notation "fs -:- v1 -- s --> v2" := (RunsTo fs s v1 v2) (no associativity, at level 60).
  Infix "==" := VariableLemmas.equiv.

  Definition st_agree_except (v1 v2 : st) vars := agree_except (fst v1) (fst v2) vars /\ snd v1 = snd v2.

  Local Notation "v1 =~= v2 [^ except ]" := (st_agree_except v1 v2 except) (no associativity, at level 60).

  Hint Rewrite sum_S : arith.
  Hint Resolve S_le_lt.
  Hint Resolve sel_upd_firstn.
  Hint Resolve firstn_S_upd.
  Hint Resolve VariableLemmas.noChange.
  Hint Resolve Max.le_max_l Max.le_max_r.
  Hint Extern 12 => rv_solver.
  Hint Extern 12 => sp_solver.
  Hint Resolve le_plus_lt lt_max_l lt_max_r.
  Hint Resolve plus_le.
  Hint Resolve lt_le_S plus_lt.

  Hint Resolve le_max_l_trans.
  Hint Resolve le_max_r_trans.
  Hint Extern 0 (_ <= _) => progress max_le_solver.
  Hint Extern 0 (List.incl _ _) => progress incl_app_solver.

  Hint Resolve in_eq In_incl.
  Hint Resolve List.incl_cons incl_cons_l incl_cons_r List.incl_refl incl_nil incl_tl incl_array.
  Hint Resolve incl_app incl_appl incl_appr.
  Hint Resolve List.incl_tran.
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

  Hint Resolve runs_loop_partially_finish.
  Hint Resolve exprDenote_disjoint.
  Hint Resolve RunsTo_footprint.

  Lemma RunsToRelax_loop_false : forall fs e b k v1 v2, 
    fs ~:~ v1 ~~ k ~~> v2 -> 
    wneb (v1[(e)]) $0 = false -> 
    fs ~:~ v1 ~~ While e b;: k ~~> v2.
    unfold RunsToRelax; intros; openhyp; descend; eauto.
  Qed.

  Hint Resolve RunsToRelax_loop_false.

  Lemma st_agree_except_symm : forall v1 v2 ex, v1 =~= v2 [^ex] -> v2 =~= v1 [^ex].
    unfold st_agree_except; intuition.
  Qed.

  Lemma RunsToRelax_immune : forall fs s v1 v2 v1' v2', 
    fs ~:~ v1 ~~ s ~~> v2 ->
    v1' =~= v1 [^ tmps s] -> 
    v2' =~= v2 [^ tmps s] ->
    disjoint (footprint s) (tmps s) ->
    fs ~:~ v1' ~~ s ~~> v2'.
    intros; eapply st_agree_except_symm in H0; eapply st_agree_except_symm in H1; unfold st_agree_except, RunsToRelax in *; openhyp; change_RunsTo_for_goal; eauto; openhyp; descend.
    eauto.
    use_changed_in_eval; eauto; eapply changedVariables_symm in H0; eauto.
    congruence.
  Qed.

  Lemma inversion_RunsTo_seq : forall fs a b v1 v2, fs -:- v1 -- a;: b --> v2 -> exists v, fs -:- v1 -- a --> v /\ fs -:- v -- b --> v2.
    inversion 1; eauto.
  Qed.

  Lemma RunsToRelax_cond_true' : forall fs e t f k v1 v2,
    fs ~:~ v1 ~~ t;: k ~~> v2 ->
    wneb (v1[(e)]) $0 = true ->
    fs ~:~ v1 ~~ Syntax.If e t f;: k ~~> v2.
    unfold RunsToRelax; intros; openhyp; auto_apply_in inversion_RunsTo_seq; openhyp; descend; simpl in *; eauto 6.
  Qed.

  Hint Resolve RunsToRelax_cond_true'.

  Lemma RunsToRelax_cond_true : forall fs e t f k v1 v1' v2,
    let s := Syntax.If e t f;: k in
      fs ~:~ v1 ~~ t;: k ~~> v2 ->
      v1' =~= v1 [^etmps e] ->
      wneb (v1'[(e)]) $0 = true ->
      disjoint (footprint s) (tmps s) ->
      fs ~:~ v1' ~~ s ~~> v2.
    admit.
(*    intros; eapply RunsToRelax_immune; unfold s, st_agree_except in *; openhyp; descend; simpl in *; eauto.*)
  Qed.

  Lemma RunsToRelax_cond_false' : forall fs e t f k v1 v2,
    fs ~:~ v1 ~~ f;: k ~~> v2 ->
    wneb (v1[(e)]) $0 = false ->
    fs ~:~ v1 ~~ Syntax.If e t f;: k ~~> v2.
    unfold RunsToRelax; intros; openhyp; auto_apply_in inversion_RunsTo_seq; openhyp; descend; simpl in *; eauto 6.
  Qed.

  Hint Resolve RunsToRelax_cond_false'.

  Lemma RunsToRelax_cond_false : forall fs e t f k v1 v1' v2,
    let s := Syntax.If e t f;: k in
      fs ~:~ v1 ~~ f;: k ~~> v2 ->
      v1' =~= v1 [^etmps e] ->
      wneb (v1'[(e)]) $0 = false ->
      disjoint (footprint s) (tmps s) ->
      fs ~:~ v1' ~~ s ~~> v2.
    admit.
(*    intros; eapply RunsToRelax_immune; unfold s, st_agree_except in *; openhyp; descend; simpl in *; eauto.*)
  Qed.

  Lemma changed_trans_l : forall vs1 vs2 vs3 a c, 
    changedVariables vs1 vs2 a -> 
    changedVariables vs2 vs3 c ->
    List.incl a c ->
    changedVariables vs1 vs3 c.
    eauto.
  Qed.

  Definition tmps_diff big small := tempChunk (depth small) (depth big - depth small).

  Lemma incl_tempChunk2 : forall b n m, b + n <= m -> List.incl (tempChunk b n) (tempVars m).
    intros; eapply incl_tempChunk; eauto.
  Qed.

  Hint Resolve incl_tempChunk2.

  Lemma agree_except_app_comm : forall vs1 vs2 a b,
    agree_except vs1 vs2 (a ++ b) ->
    agree_except vs1 vs2 (b ++ a).
    intros; eauto.
  Qed.

  Lemma merge_comm : forall v vars1 v1 vars2 v2,
    disjoint vars1 vars2 ->
    v [vars1 => v1] [vars2 => v2] == v [vars2 => v2] [vars1 => v1].
    intros.
    unfold VariableLemmas.equiv, changedVariables.
    intros.
    contradict H0.
    destruct (In_dec string_dec x vars1).
    destruct (In_dec string_dec x vars2).
    unfold disj in *.
    contradict H.
    eauto.
    rewrite sel_merge by eauto.
    rewrite sel_merge_outside by eauto.
    rewrite sel_merge by eauto.
    eauto.
    destruct (In_dec string_dec x vars2).
    rewrite sel_merge_outside by eauto.
    rewrite sel_merge by eauto.
    rewrite sel_merge by eauto.
    eauto.
    rewrite sel_merge_outside by eauto.
    rewrite sel_merge_outside by eauto.
    rewrite sel_merge_outside by eauto.
    rewrite sel_merge_outside by eauto.
    eauto.
  Qed.

  Lemma equiv_merge_equiv : forall v1 v2 vars v,
    v1 == v2 ->
    v1 [vars => v] == v2 [vars => v].
    intros; eapply two_merge_equiv; eauto.
  Qed.

  Hint Extern 1 => use_disjoint_trans''.

  Lemma RunsToRelax_seq_fwd : forall fs a b v1 v2,
    fs ~:~ v1 ~~ a;: b ~~> v2 ->
    disjoint (footprint (a;: b)) (tmps (a;: b)) ->
    exists v, fs ~:~ v1 ~~ a ~~> v /\ fs ~:~ v ~~ b ~~> v2.
    clear.
    unfold RunsToRelax; intros.
    openhyp.
    eapply inversion_RunsTo_seq in H.
    openhyp.
    simpl in *.
    destruct (le_lt_dec (depth a) (depth b)).
    exists (fst x0 [tmps a => fst v2], snd x0).
    split.
    descend; eauto.
    eapply changed_merge_fwd.
    change_RunsTo_for_goal.
    openhyp.
    simpl in *.
    descend; eauto.
    use_changed_in_eval.
    eapply changed_trans_l.
    eapply changed_merge_bwd.
    eauto.
    eauto.
    eauto.
    congruence.
    simpl.
    eapply changed_unchanged.
    eapply changed_merge_fwd.
    eauto.
    eauto.
    set (diff := tmps_diff a b).
    exists (fst x0 [diff => fst v2], snd x0).
    split.
    descend; eauto.
    eapply agree_except_trans.
    2 : eapply changed_merge_fwd.
    eauto.
    eauto.
    unfold diff, tmps_diff.
    eapply incl_tempChunk2.
    omega.
    change_RunsTo_for_goal.
    openhyp.
    simpl in *.
    descend; eauto.
    eapply changed_trans_l.
    Focus 2.
    eapply changed_merge.
    eapply agree_except_app_comm.
    rewrite Max.max_l in * by eauto.
    erewrite <- split_tmps.
    eauto.
    eauto.
    2 : eapply List.incl_refl.
    eapply changedVariables_incl.
    2 : eauto.
    eapply VariableLemmas.equiv_trans.
    eauto.
    apply_in_all RunsTo_footprint.
    eapply VariableLemmas.equiv_trans.
    eapply VariableLemmas.equiv_symm.
    eapply merge_comm.
    unfold diff, tmps_diff.
    eauto.
    unfold diff, tmps_diff.
    eapply equiv_merge_equiv.
    eapply changed_merge.
    eauto.
    congruence.
    simpl.
    unfold diff, tmps_diff.
    eapply changed_unchanged.
    eapply changed_merge_fwd.
    eauto.
    eauto.
  Qed.

  Lemma RunsToRelax_seq_bwd : forall fs a b v1 v2 v3,
    fs ~:~ v1 ~~ a ~~> v2 ->
    fs ~:~ v2 ~~ b ~~> v3 ->
    disjoint (footprint (a;: b)) (tmps (a;: b)) ->
    fs ~:~ v1 ~~ a;: b ~~> v3.
    unfold RunsToRelax; intros; openhyp; generalize dependent H; simpl in *; change_RunsTo_to x0; eauto; openhyp; descend; eauto; try use_changed_in_eval; eauto.
    congruence.
  Qed.

  Hint Resolve RunsToRelax_seq_bwd.

  Lemma RunsToRelax_assoc_left : forall fs a b c v1 v2,
    fs ~:~ v1 ~~ a;: (b;: c) ~~> v2 ->
    disjoint (footprint (a;: (b;: c))) (tmps (a;: (b;: c))) ->
    fs ~:~ v1 ~~ a;: b;: c ~~> v2.
    clear; simpl; intros; eapply RunsToRelax_seq_fwd in H; eauto; openhyp; eapply RunsToRelax_seq_fwd in H1; eauto; openhyp; repeat eapply RunsToRelax_seq_bwd; repeat (simpl; eauto).
  Qed.

  Lemma RunsTo_loop_true : forall fs e b v1 v2,
    fs -:- v1 -- b;: While e b --> v2 ->
    wneb (v1[(e)]) $0 = true ->
    fs -:- v1 -- While e b --> v2.
    clear; intros; eapply inversion_RunsTo_seq in H; openhyp; eauto.
  Qed.

  Hint Resolve RunsTo_loop_true.

  Lemma RunsToRelax_loop_true : forall fs e b v1 v2, 
    fs ~:~ v1 ~~ b;: While e b ~~> v2 -> 
    wneb (v1[(e)]) $0 = true -> 
    fs ~:~ v1 ~~ While e b ~~> v2.
    unfold RunsToRelax; intros; openhyp; simpl in *; descend; eauto.
  Qed.

  Hint Resolve RunsToRelax_loop_true.

  Lemma RunsToRelax_loop_true_k : forall fs e b k v1 v2, 
    let s := While e b;: k in
      fs ~:~ v1 ~~ b;: s ~~> v2 -> 
      wneb (v1[(e)]) $0 = true -> 
      disjoint (footprint s) (tmps s) ->
      fs ~:~ v1 ~~ s ~~> v2.
    simpl; intros; eapply RunsToRelax_assoc_left in H; simpl; eauto; eapply RunsToRelax_seq_fwd in H; simpl; eauto; openhyp; eauto.
  Qed.

  Hint Resolve RunsToRelax_loop_true_k.

  Lemma RunsToRelax_skip : forall fs s v1 v2,
    fs ~:~ v1 ~~ s ~~> v2 ->
    fs ~:~ v1 ~~ skip;: s ~~> v2.
    unfold RunsToRelax; intros; openhyp; descend; eauto.
  Qed.

  Hint Resolve RunsToRelax_skip.

  Lemma RunsTo_RunsToRelax : forall fs s v1 v2,
    fs -:- v1 -- s --> v2 ->
    fs ~:~ v1 ~~ s ~~> v2.
    clear; unfold RunsToRelax; intro; descend; eauto.
  Qed.

  Hint Resolve RunsTo_RunsToRelax.

End Hints.