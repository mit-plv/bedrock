Require Import SyntaxExpr SemanticsExpr.
Require Import Syntax Semantics SyntaxNotations.
Require Import VariableLemmas.
Require Import Depth.
Require Import GeneralTactics.

Section Hints.

  Definition RunsToRelax fs s v v_new := 
    exists v', RunsTo fs s v v' 
      /\ changed_in (fst v') (fst v_new) (tempVars (depth s))
      /\ snd v_new = snd v'.

  Local Notation "fs ~:~ v1 ~~ s ~~> v2" := (RunsToRelax fs s v1 v2) (no associativity, at level 60).

  Local Notation "v [( e )]" := (exprDenote e (fst v)) (no associativity, at level 60).
  
  Lemma RunsToRelax_loop_false : forall fs e b k v1 v2, 
    fs ~:~ v1 ~~ k ~~> v2 -> 
    wneb (v1[(e)]) $0 = false -> 
    fs ~:~ v1 ~~ While e b;: k ~~> v2.
    unfold RunsToRelax; intros; openhyp; descend; eauto.
  Qed.

  Hint Resolve RunsToRelax_loop_false.

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

  Lemma RunsToRelax_assign : forall fs var e k v1 v2 v3,
    fs ~:~ v2 ~~ k ~~> v3 ->
    denote_sem (var <- e) v1 =~= v2 [^etmps e] ->
    disjoint (footprint k) (etmps e) ->
    fs ~:~ v1 ~~ var <- e;: k ~~> v3.
    intros; eapply st_agree_except_symm in H0; unfold denote_sem, RunsToRelax, st_agree_except in *; openhyp; change_RunsTo_to (denote_sem (var <- e) v1); eauto; openhyp; destruct v1; simpl in *; descend.
    eauto.
    eapply changedVariables_symm in H0; use_changed_in_eval; eauto.
    congruence.
  Qed.

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

  Hint Resolve Safe_assoc_left.

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