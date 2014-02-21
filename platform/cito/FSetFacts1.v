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

  Lemma of_list_fwd' : forall e ls acc,
    In e (List.fold_left (fun s e => add e s) ls acc)
    -> List.In e ls \/ In e acc.
    induction ls; simpl; intuition.
    apply IHls in H; intuition.
    apply add_iff in H0; intuition.
  Qed.

  Lemma of_list_fwd : forall e ls,
    In e (of_list ls)
    -> List.In e ls.
    intros.
    apply of_list_fwd' in H; intuition.
    apply empty_iff in H0; tauto.
  Qed.

  Lemma of_list_bwd' : forall e ls acc,
    List.In e ls \/ In e acc
    -> In e (List.fold_left (fun s e => add e s) ls acc).
    induction ls; simpl; intuition.
  Qed.

  Lemma of_list_bwd : forall e ls,
    List.In e ls
    -> In e (of_list ls).
    intros.
    apply of_list_bwd'; auto.
  Qed.

  Local Hint Resolve of_list_fwd of_list_bwd.

  Lemma of_list_spec : forall e ls, In e (of_list ls) <-> List.In e ls.
    generalize of_list_fwd, of_list_bwd; firstorder.
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
    unfold Equal; intuition.
    unfold of_list in H; simpl in H.
    apply of_list_fwd' in H; intuition.
    apply add_iff in H0; intuition (subst; eauto).
    apply union_iff; left; apply singleton_iff; auto.
    apply empty_iff in H; tauto.
    unfold of_list; simpl.
    apply union_iff in H.
    apply of_list_bwd'; intuition.
  Qed.

  Add Morphism Disjoint with signature Equal ==> Equal ==> iff as Disjoint_m.
    unfold Equal, Disjoint; firstorder.
  Qed.

  Local Hint Resolve union_2 union_3.

  Lemma Disjoint_union : forall s1 s2 s3, Disjoint s1 (union s2 s3) <-> (Disjoint s1 s2 /\ Disjoint s1 s3).
    unfold Disjoint; intuition eauto.
    apply union_iff in H3; intuition eauto.
  Qed.

  Local Hint Resolve singleton_2.

  Lemma Disjoint_singletons : forall e1 e2, Disjoint (singleton e1) (singleton e2) <-> e1 <> e2.
    unfold Disjoint; intuition eauto.
    apply singleton_iff in H1; apply singleton_iff in H2.
    congruence.
  Qed.

  Lemma Disjoint_singleton : forall e s, Disjoint (singleton e) s <-> ~ In e s.
    unfold Disjoint; intuition eauto.
    apply singleton_iff in H1.
    congruence.
  Qed.

  Local Hint Resolve inter_1 inter_2 inter_3.

  Lemma inter_is_empty_iff : forall s1 s2, is_empty (inter s1 s2) = true <-> Disjoint s1 s2.
    unfold Disjoint; intuition eauto.
    apply is_empty_2 in H.
    eapply H; eauto.
    apply is_empty_1.
    hnf; intuition.
    eauto.
  Qed.

  Lemma Equal_Subset_iff : forall s1 s2, Equal s1 s2 <-> (Subset s1 s2 /\ Subset s2 s1).
    unfold Equal, Subset; firstorder.
  Qed.

End UWFacts_fun.