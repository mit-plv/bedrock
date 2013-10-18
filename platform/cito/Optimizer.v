Require Import StepsTo.
Require Import StepsSafe.
Require Import Syntax Semantics.
Require Import GeneralTactics.
Import Safety.

Set Implicit Arguments.

Definition is_backward_simulation (R : Statement -> Statement -> Prop) : Prop :=
  forall s t, 
    R s t -> 
    (forall v v',
       Step t v (Done v') -> Step s v (Done v')) /\
    (forall v f x v' t', 
       Step t v (ToCall f x t' v') -> 
       exists s', 
         Step s v (ToCall f x s' v') /\ 
         R s' t').

(* an extended one supposed to be used later *)
Definition is_backward_simulation_ext (R : Statement -> Statement -> Prop) (Rstate : vals -> vals -> Prop) : Prop :=
  forall vs s vt t, 
    R s t -> 
    Rstate vs vt ->
    (forall heap vt',
       Step t (vt, heap) (Done vt') -> 
       exists vs',
         Step s (vs, heap) (Done vs') /\
         Rstate (fst vs') (fst vt')) /\
    (forall heap f x vt' t', 
       Step t (vt, heap) (ToCall f x t' vt') -> 
       exists s' vs', 
         Step s (vs, heap) (ToCall f x s' vs') /\ 
         R s' t' /\
         Rstate (fst vs') (fst vt')).

Definition is_backward_similar s t := exists R, is_backward_simulation R /\ R s t.

(* each function can be optimized by different optimizors *)
Inductive is_backward_similar_callee : Callee -> Callee -> Prop :=
  | BothForeign : 
      forall spec1 spec2 : callTransition -> Prop, 
        (forall x, spec2 x -> spec1 x) -> 
        is_backward_similar_callee (Foreign spec1) (Foreign spec2)
  | BothInternal : 
      forall body1 body2, 
        is_backward_similar body1 body2 -> 
        is_backward_similar_callee (Internal body1) (Internal body2).

Definition is_backward_similar_fs fs1 fs2 := 
  forall (w : W) callee2,
    fs2 w = Some callee2 ->
    exists callee1,
      fs1 w = Some callee1 /\
      is_backward_similar_callee callee1 callee2.

Hint Resolve RunsTo_StepsTo StepsTo_RunsTo.

Hint Unfold is_backward_similar is_backward_simulation.

Lemma correct_StepsTo : forall tfs t v v', StepsTo tfs t v v' -> forall s, is_backward_similar s t -> forall sfs, is_backward_similar_fs sfs tfs -> StepsTo sfs s v v'.
  induction 1; simpl; intuition.

  destruct H0; openhyp.
  eapply H0 in H2; openhyp.
  econstructor; eauto.

  destruct H3; openhyp.
  eapply H3 in H5; openhyp.
  eapply H6 in H; openhyp.
  eapply H4 in H0; openhyp.
  inversion H8; subst.
  econstructor 2; eauto.
  eapply H11; eauto.

  destruct H4; openhyp.
  eapply H4 in H6; openhyp.
  eapply H7 in H; openhyp.
  eapply H5 in H0; openhyp.
  inversion H9; subst.
  econstructor 3; eauto.
Qed.
Hint Resolve correct_StepsTo.

Theorem correct_RunsTo : forall sfs s tfs t, is_backward_similar s t -> is_backward_similar_fs sfs tfs -> forall v v', RunsTo tfs t v v' -> RunsTo sfs s v v'.
  intuition eauto.
Qed.

Hint Resolve Safe_StepsSafe StepsSafe_Safe.

Definition is_safety_preserving (R : Statement -> Statement -> Prop) : Prop :=
  forall s t,
    R s t ->
    (forall v,
      StepSafe s v ->
      StepSafe t v) /\
    (forall v f x t' v',
       Step t v (ToCall f x t' v') ->
       exists s',
         Step s v (ToCall f x s' v') /\
         R s' t').

Definition preserves_safety s t := exists R, is_safety_preserving R /\ R s t.

Inductive callee_preserves_safety : Callee -> Callee -> Prop :=
  | SafeBothForeign : 
      forall spec1 spec2 : callTransition -> Prop, 
        (forall x a, ForeignSafe spec1 x a -> ForeignSafe spec2 x a) -> 
        callee_preserves_safety (Foreign spec1) (Foreign spec2)
  | SafeBothInternal : 
      forall body1 body2, 
        preserves_safety body1 body2 -> 
        callee_preserves_safety (Internal body1) (Internal body2).

Definition fs_preserves_safety fs1 fs2 := 
  forall (w : W) callee1,
    fs1 w = Some callee1 ->
    exists callee2,
      fs2 w = Some callee2 /\
      callee_preserves_safety callee1 callee2.

Hint Unfold preserves_safety fs_preserves_safety.

Theorem is_backward_similar_trans : forall a b c, is_backward_similar a b -> is_backward_similar b c -> is_backward_similar a c.
  intros.
  destruct H; openhyp.
  destruct H0; openhyp.
  exists (fun a c => exists b, x a b /\ x0 b c); intuition eauto.
  unfold is_backward_simulation in *.
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

Lemma correct_StepsSafe : 
  forall sfs s v, 
    StepsSafe sfs s v -> 
    forall t, 
      preserves_safety s t -> 
      forall tfs, 
        fs_preserves_safety sfs tfs -> 
        is_backward_similar_fs sfs tfs -> 
        StepsSafe tfs t v.
  intros.
  eapply (
      StepsSafe_coind (
          fun tfs t v => 
            exists sfs s, 
              StepsSafe sfs s v /\ 
              preserves_safety s t /\
              fs_preserves_safety sfs tfs /\
              is_backward_similar_fs sfs tfs
    )).
  2 : do 3 eexists; intuition eauto.
  intros.
  openhyp.

  split.
  inversion H3; subst.
  destruct H4; openhyp.
  eapply H4 in H9; openhyp.
  eauto.

  intros.
  inversion H3; subst.
  destruct H4; openhyp.
  eapply H4 in H10; openhyp.
  eapply H11 in H7; openhyp.
  eapply H9 in H7; openhyp.

  left.
  generalize H7; intro.
  eapply H5 in H7; openhyp.
  inversion H16; subst.
  eexists; intuition eauto.
  eapply H6 in H7; openhyp.
  inversion H19; subst.
  rewrite H15 in H7; injection H7; intros; subst.
  do 2 eexists; intuition eauto.

  right.
  generalize H7; intro.
  eapply H5 in H7; openhyp.
  inversion H15; subst.
  eexists; intuition eauto.

  eapply H6 in H7; openhyp.
  inversion H18; subst.
  rewrite H14 in H7; injection H7; intros; subst.
  edestruct H13; eauto.
  do 2 eexists; intuition eauto.

  eapply H6 in H7; openhyp.
  inversion H19; subst.
  rewrite H14 in H7; injection H7; intros; subst.
  edestruct H13; eauto.
  do 2 eexists; intuition eauto.

Qed.

Hint Resolve correct_StepsSafe.

Theorem correct_Safe : forall sfs s v, Safe sfs s v -> forall t, preserves_safety s t -> forall tfs, fs_preserves_safety sfs tfs -> is_backward_similar_fs sfs tfs -> Safe tfs t v.
  eauto.
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