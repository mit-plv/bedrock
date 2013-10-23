Require Import StepsTo.
Require Import StepsSafe.
Require Import Syntax Semantics.
Require Import GeneralTactics.
Import Safety.

Set Implicit Arguments.

Definition is_backward_simulation (R : vals -> Statement -> vals -> Statement -> Prop) : Prop :=
  forall vs s vt t, 
    R vs s vt t -> 
    (forall heap vt' heap',
       Step t (vt, heap) (Done (vt', heap')) -> 
       exists vs',
         Step s (vs, heap) (Done (vs', heap')) /\
         R vs' Syntax.Skip vt' Syntax.Skip) /\
    (forall heap f x t' vt' heap', 
       Step t (vt, heap) (ToCall f x t' (vt', heap')) -> 
       exists s' vs', 
         Step s (vs, heap) (ToCall f x s' (vs', heap')) /\ 
         R vs' s' vt' t').

Definition is_backward_similar vs s vt t := exists R, is_backward_simulation R /\ R vs s vt t.

(* each function can be optimized by different optimizors *)
Inductive is_backward_similar_callee : Callee -> Callee -> Prop :=
  | BothForeign :
      forall spec1 spec2 : callTransition -> Prop,
        (forall x, spec2 x -> spec1 x) ->
        is_backward_similar_callee (Foreign spec1) (Foreign spec2)
  | BothInternal :
      forall body1 body2 R,
        is_backward_simulation R ->
        (forall v, R v body1 v body2) ->
        is_backward_similar_callee (Internal body1) (Internal body2).

Definition is_backward_similar_fs fs1 fs2 := 
  forall (w : W) callee2,
    fs2 w = Some callee2 ->
    exists callee1,
      fs1 w = Some callee1 /\
      is_backward_similar_callee callee1 callee2.

Hint Resolve RunsTo_StepsTo StepsTo_RunsTo.

Hint Unfold is_backward_similar is_backward_simulation.

Lemma correct_StepsTo : 
  forall tfs t v v',
    StepsTo tfs t v v' ->
    forall vt heap vt' heap',
      v = (vt, heap) ->
      v' = (vt', heap') ->
      forall R, 
        is_backward_simulation R -> 
        forall s vs, 
          R vs s vt t -> 
          forall sfs, 
            is_backward_similar_fs sfs tfs -> 
            exists vs', 
              StepsTo sfs s (vs, heap) (vs', heap') /\ 
              R vs' Syntax.Skip vt' Syntax.Skip.
Proof.
  induction 1; simpl; intuition.

  subst.
  eapply H2 in H3; openhyp.
  eapply H0 in H; openhyp.
  econstructor; eauto.

  subst.
  destruct v'; simpl in *.
  eapply H5 in H6; openhyp.
  eapply H4 in H; openhyp.
  eapply H7 in H0; openhyp.
  inversion H8; subst.
  edestruct IHStepsTo; eauto.
  openhyp.
  eexists.
  split.
  econstructor 2; eauto.
  eapply H11; eauto.
  eauto.

  subst.
  destruct v'; simpl in *.
  destruct v''; simpl in *.
  eapply H6 in H7; openhyp.
  eapply H4 in H; openhyp.
  eapply H8 in H0; openhyp.
  inversion H7; subst.
  edestruct IHStepsTo1; eauto.
  eauto.
  openhyp.
  edestruct IHStepsTo2.
  eauto.
  eauto.
  2 : eauto.
  eauto.
  eauto.
  openhyp.
  eexists.
  split.
  econstructor 3; eauto.
  eauto.
Qed.
Hint Resolve correct_StepsTo.

Theorem correct_RunsTo : 
  forall tfs t v v',
    RunsTo tfs t v v' ->
    forall vt heap vt' heap',
      v = (vt, heap) ->
      v' = (vt', heap') ->
      forall R, 
        is_backward_simulation R -> 
        forall s vs, 
          R vs s vt t -> 
          forall sfs, 
            is_backward_similar_fs sfs tfs -> 
            exists vs', 
              RunsTo sfs s (vs, heap) (vs', heap') /\ 
              R vs' Syntax.Skip vt' Syntax.Skip.
Proof.
  intros; edestruct correct_StepsTo; intuition eauto.
Qed.

Theorem is_backward_similar_trans : 
  forall va a vb b vc c, 
    is_backward_similar va a vb b -> 
    is_backward_similar vb b vc c -> 
    is_backward_similar va a vc c.
Proof.
  intros.
  destruct H; openhyp.
  destruct H0; openhyp.
  exists (fun va a vc c => exists vb b, x va a vb b /\ x0 vb b vc c); intuition eauto.
  unfold is_backward_simulation in *.
  intros.
  openhyp.
  split.
  intros.
  eapply H0 in H4; openhyp.
  eapply H in H3; openhyp.
  eapply H4 in H5; openhyp.
  eapply H3 in H5; openhyp.
  eexists; intuition eauto.

  intros.
  eapply H0 in H4; openhyp.
  eapply H6 in H5; openhyp.
  eapply H in H3; openhyp.
  eapply H8 in H5; openhyp.
  do 2 eexists; intuition eauto.
Qed.

(* Safety part *)

Definition is_safety_preserving (R : vals -> Statement -> vals -> Statement -> Prop) : Prop :=
  forall vs s vt t,
    R vs s vt t ->
    (forall heap,
       StepSafe s (vs, heap) -> 
       StepSafe t (vt, heap)) /\
    (forall heap f x t' vt' heap',
       Step t (vt, heap) (ToCall f x t' (vt', heap')) ->
       exists s' vs',
         Step s (vs, heap) (ToCall f x s' (vs', heap')) /\
         R vs' s' vt' t').

Definition preserves_safety vs s vt t := exists R, is_safety_preserving R /\ R vs s vt t.

Variable some_relation : Statement -> Statement -> Prop.

Inductive callee_preserves_safety : Callee -> Callee -> Prop :=
  | SafeBothForeign : 
      forall spec1 spec2 : callTransition -> Prop, 
        (forall x a, ForeignSafe spec1 x a -> ForeignSafe spec2 x a) -> 
        callee_preserves_safety (Foreign spec1) (Foreign spec2)
  | SafeBothInternal : 
      forall body1 body2 R, 
        is_safety_preserving R ->
        (forall v, R v body1 v body2) -> 
        callee_preserves_safety (Internal body1) (Internal body2).

Definition fs_preserves_safety fs1 fs2 := 
  forall (w : W) callee1,
    fs1 w = Some callee1 ->
    exists callee2,
      fs2 w = Some callee2 /\
      callee_preserves_safety callee1 callee2.

Hint Resolve Safe_StepsSafe StepsSafe_Safe.

Hint Unfold preserves_safety fs_preserves_safety.

Lemma correct_StepsSafe : 
  forall sfs s vs heap, 
    StepsSafe sfs s (vs, heap) -> 
    forall t vt, 
      preserves_safety vs s vt t -> 
      forall tfs, 
        fs_preserves_safety sfs tfs -> 
        is_backward_similar_fs sfs tfs -> 
        StepsSafe tfs t (vt, heap).
  intros.
  eapply (
      StepsSafe_coind (
          fun tfs t v => 
            exists sfs s vt heap vs, 
              v = (vt, heap) /\
              StepsSafe sfs s (vs, heap) /\ 
              preserves_safety vs s vt t /\
              fs_preserves_safety sfs tfs /\
              is_backward_similar_fs sfs tfs
    )).
  2 : do 5 eexists; intuition eauto.
  clear.
  intros.
  openhyp.
  subst.

  split.
  inversion H0; subst.
  destruct H1; openhyp.
  eapply H1 in H5; openhyp.
  eauto.

  intros.
  inversion H0; subst.
  destruct H1; openhyp.
  eapply H1 in H6; openhyp.
  destruct v'; simpl in *.
  eapply H7 in H; openhyp.
  eapply H5 in H; openhyp.
  simpl in *.

  left.
  generalize H; intro.
  eapply H2 in H; openhyp.
  inversion H12; subst.
  eexists; intuition eauto.
  eapply H3 in H; openhyp.
  inversion H15; subst.
  rewrite H11 in H; injection H; intros; subst.
  do 5 eexists; intuition eauto.

  right.
  generalize H; intro.
  eapply H2 in H; openhyp.
  inversion H11; subst.
  eexists; intuition eauto.

  eapply H3 in H; openhyp.
  inversion H15; subst.
  rewrite H10 in H; injection H; intros; subst.
  edestruct H9; eauto.
  do 5 eexists; intuition eauto.
  eexists; intuition eauto.

  eapply H3 in H; openhyp.
  inversion H16; subst.
  rewrite H10 in H; injection H; intros; subst.
  edestruct H9; eauto.
  do 5 eexists.
  split.
  eauto.
  split.
  Focus 2.
  split.
  eexists.
  split.
  2 : eauto.
  eauto.
  intuition eauto.
  destruct v''; simpl in *.
  eapply H17.
  (*here*)
  eauto.
Qed.

Hint Resolve correct_StepsSafe.

Theorem correct_Safe : forall sfs s v, Safe sfs s v -> forall t, preserves_safety s t -> forall tfs, fs_preserves_safety sfs tfs -> is_backward_similar_fs sfs tfs -> Safe tfs t v.
  eauto.
Qed.

Theorem preserves_safety_trans : forall a b c, preserves_safety a b -> preserves_safety b c -> preserves_safety a c.
  intros.
  destruct H; openhyp.
  destruct H0; openhyp.
  exists (fun a c => exists b, x a b /\ x0 b c); intuition eauto.
  unfold is_safety_preserving in *.
  intros.
  openhyp.
  split.
  intros.
  eapply H0 in H4; openhyp.
  eapply H in H3; openhyp.
  eauto.

  intros.
  eapply H0 in H4; openhyp.
  eapply H6 in H5; openhyp.
  eapply H in H3; openhyp.
  eapply H8 in H5; openhyp.
  intuition eauto.
Qed.

Hint Resolve correct_RunsTo correct_Safe.

Theorem correct : 
  forall sfs s tfs t, 
    is_backward_similar s t -> 
    preserves_safety s t ->
    is_backward_similar_fs sfs tfs -> 
    fs_preserves_safety sfs tfs ->
    forall v, 
      (Safe sfs s v -> Safe tfs t v) /\ 
      forall v', 
        RunsTo tfs t v v' -> RunsTo sfs s v v'.
  intuition eauto.
Qed.

Print Assumptions correct.