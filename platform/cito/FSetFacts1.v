Set Implicit Arguments.

Require Import DecidableTypeEx.
Require Import FSetInterface.

Module UWFacts_fun (E : UsualDecidableType) (Import M : WSfun E).
  
  Require Import FSetFacts.
  Module Import F := WFacts_fun E M.

  Definition of_list ls := List.fold_left (fun s e => add e s) ls empty.

  Definition Disjoint a b := forall x, ~ (In x a /\ In x b).

  Import ListNotations.
  Require Import GeneralTactics.

  Lemma of_list_spec : forall e ls, In e (of_list ls) <-> List.In e ls.
    admit.
  Qed.

  Lemma of_list_singleton : forall e, Equal (of_list [e]) (singleton e).
    intros.
    unfold of_list.
    simpl.
    unfold Equal.
    split; intros.
    eapply singleton_iff.
    eapply add_iff in H.
    openhyp.
    eauto.
    eapply empty_iff in H.
    intuition.
    eapply singleton_iff in H.
    eapply add_iff; eauto.
  Qed.

  Lemma of_list_cons : forall e ls, Equal (of_list (e :: ls)) (union (singleton e) (of_list ls)).
    admit.
  Qed.

  Add Morphism Disjoint with signature Equal ==> Equal ==> iff as Disjoint_m.
    admit.
  Qed.

  Lemma Disjoint_union : forall s1 s2 s3, Disjoint s1 (union s2 s3) <-> (Disjoint s1 s2 /\ Disjoint s1 s3).
    admit.
  Qed.

  Lemma Disjoint_singletons : forall e1 e2, Disjoint (singleton e1) (singleton e2) <-> e1 <> e2.
    admit.
  Qed.

  Lemma Disjoint_singleton : forall e s, Disjoint (singleton e) s <-> ~ In e s.
    admit.
  Qed.

  Lemma inter_is_empty_iff : forall s1 s2, is_empty (inter s1 s2) = true <-> Disjoint s1 s2.
    admit.
  Qed.

  Lemma Equal_Subset_iff : forall s1 s2, Equal s1 s2 <-> (Subset s1 s2 /\ Subset s2 s1).
    admit.
  Qed.

End UWFacts_fun.