Require Import Syntax Semantics.
Require Import CompileStatement.
Require Import GeneralTactics.

Set Implicit Arguments.

Definition is_good_optimizer optimizer :=
  (forall fs s v vs' heap', RunsTo fs (optimizer s) v (vs', heap') -> exists vs'', RunsTo fs s v (vs'', heap')) /\ 
  (forall fs s v, Safety.Safe fs s v -> Safety.Safe fs (optimizer s) v) /\
  (forall s, List.incl (SemanticsLemmas.footprint (optimizer s)) (SemanticsLemmas.footprint s)) /\
  (forall s, CompileStatement.depth (optimizer s) <= CompileStatement.depth s).

Definition compose A B C (g : B -> C) (f : A -> B) x := g (f x).

Lemma is_good_optimizer_trans : 
  forall a b,
    is_good_optimizer a ->
    is_good_optimizer b ->
    is_good_optimizer (compose a b).
Proof.
  unfold is_good_optimizer, compose; intros.

  openhyp.
  repeat split.
  intros.
  eapply H in H7; eauto; openhyp.
  eapply H0 in H7; eauto; openhyp.

  eauto.

  eauto.

  eauto using Le.le_trans.
Qed.