Require Import Reflection.
Require Import Bool.

Ltac think' ext solver :=
  repeat match goal with
           | [ H : Some _ = Some _ |- _ ] => inversion H ; clear H ; subst
           | [ H : inl _ = inr _ |- _ ] => inversion H ; clear H ; subst
           | [ H : inr _ = inr _ |- _ ] => inversion H ; clear H ; subst
           | [ H : _ |- _ ] => erewrite H in * |- by solver
           | [ H : _ |- _ ] => erewrite H by solver
           | [ H : andb _ _ = true |- _ ] => 
             apply andb_true_iff in H ; destruct H
           | [ H : orb _ _ = false |- _ ] => 
             apply orb_false_iff in H ; destruct H
           | [ H : Equivalence.equiv _ _ |- _ ] => 
             unfold Equivalence.equiv ; subst
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : exists x, _ |- _ ] => destruct H
           | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
             ((consider X ; try congruence); []) ||
             (consider X ; solve [ congruence | solver ]) 
         end.

Ltac think := think' tt ltac:(eauto).