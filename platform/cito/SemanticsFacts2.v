Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import Safe.
  Module Import SafeMake := Safe.Make E.
  Import SafeMake.SemanticsMake.

  Section TopSection.

    Require Import Notations.
    Local Open Scope stmt.

    Lemma Safe_Seq_Skip_Safe : forall fs s v, Safe fs s v -> Safe fs (s ;; skip) v.
      admit.
    Qed.

    Lemma RunsTo_Seq_Skip_RunsTo : forall fs s v v', RunsTo fs (s ;; skip) v v' -> RunsTo fs s v v'.
      admit.
    Qed.

  End TopSection.

End Make.