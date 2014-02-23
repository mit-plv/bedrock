Set Implicit Arguments.

Require Import GoodOptimizer.

Definition id_opt : Optimizer := fun s _ => s.

Require Import ADT.

Module Make (Import E : ADT).

  Module Import GoodOptimizerMake := GoodOptimizer.Make E.
  Require Import Semantics.
  Import Semantics.

  Lemma id_opt_good : GoodOptimizer id_opt.
    unfold GoodOptimizer.
    repeat split.
    unfold PreserveSafe.
    intros.
    unfold id_opt in *.
    eauto.

    unfold PreserveRunsTo.
    intros.
    unfold id_opt in *.
    destruct v'; simpl in *.
    eexists.
    split; eauto.

    unfold PreserveGoodSize.
    intros.
    unfold id_opt in *.
    destruct H.
    Require Import GeneralTactics.
    openhyp; simpl in *.
    eauto.
    destruct H1.
    inversion H2.

