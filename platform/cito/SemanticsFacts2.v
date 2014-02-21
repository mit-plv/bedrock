Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import Semantics.
  Module Import SemanticsMake := Semantics.Make E.

  Section TopSection.

    Require Import Notations.
    Local Open Scope stmt.

    Hint Constructors Semantics.Safe.
    Hint Unfold Safe.

    Lemma Safe_Seq_Skip_Safe : forall fs s v, Safe fs s v -> Safe fs (s ;; skip) v.
      auto.
    Qed.

    Lemma RunsTo_Seq_Skip_RunsTo : forall fs s v v', RunsTo fs (s ;; skip) v v' -> RunsTo fs s v v'.
      inversion 1; subst.
      inversion H5; subst.
      auto.
    Qed.

  End TopSection.

End Make.