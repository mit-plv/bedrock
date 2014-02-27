Set Implicit Arguments.

Require Import ADT.
Require Import RepInv WordMap.
Require Import Inv.

Lemma starL_in : forall A P x (ls : list A),
  NoDup ls
  -> In x ls
  -> exists ls', (P x * Bags.starL P ls' ===> Bags.starL P ls)
    /\ NoDup ls'
    /\ (forall y, In y ls' <-> y <> x /\ In y ls).
  induction 1; simpl; intuition subst.

  eexists; intuition idtac.
  apply Himp_refl.
  auto.
  congruence.
  tauto.
  congruence.
  auto.

  destruct H1; intuition.
  exists (x0 :: x1); intuition idtac.
  simpl.
  eapply Himp_trans; [ | apply Himp_star_frame; [
    apply Himp_refl | apply H3 ] ].
  generalize dependent (Bags.starL P); intros.
  sepLemma.
  constructor; auto.
  intro.
  apply H5 in H4.
  tauto.
  subst; simpl in *; intuition subst.
  auto.
  apply H5 in H6; intuition.
  simpl in *; intuition subst.
  apply H5 in H6; intuition.
  subst; simpl; tauto.
  right; apply H5.
  auto.
Qed.

Lemma starL_out : forall A P x (ls : list A),
  NoDup ls
  -> In x ls
  -> exists ls', (Bags.starL P ls ===> P x * Bags.starL P ls')
    /\ NoDup ls'
    /\ (forall y, In y ls' <-> y <> x /\ In y ls).
  induction 1; simpl; intuition subst.

  eexists; intuition idtac.
  apply Himp_refl.
  auto.
  congruence.
  tauto.
  congruence.
  auto.

  destruct H1; intuition.
  exists (x0 :: x1); intuition idtac.
  simpl.
  eapply Himp_trans; [ apply Himp_star_frame; [
    apply Himp_refl | apply H3 ] | ].
  generalize dependent (Bags.starL P); intros.
  sepLemma.
  constructor; auto.
  intro.
  apply H5 in H4.
  tauto.
  subst; simpl in *; intuition subst.
  auto.
  apply H5 in H6; intuition.
  simpl in *; intuition subst.
  apply H5 in H6; intuition.
  subst; simpl; tauto.
  right; apply H5.
  auto.
Qed.

Lemma starL_permute : forall A P (ls1 : list A),
  NoDup ls1
  -> forall ls2, NoDup ls2
    -> (forall x, In x ls1 <-> In x ls2)
    -> Bags.starL P ls1 ===> Bags.starL P ls2.
  induction 1.

  inversion_clear 1; simpl; intros.
  apply Himp_refl.
  exfalso; eapply H; eauto.

  intros.
  eapply starL_in in H1.
  Focus 2.
  apply H2.
  simpl; eauto.

  destruct H1; intuition.
  simpl.
  eapply Himp_trans; [ | apply H3 ].
  apply Himp_star_frame; try apply Himp_refl.
  apply IHNoDup; auto.
  intuition.
  simpl in *.
  apply H5; intuition.
  apply H2; auto.
  apply H5 in H4; intuition.
  simpl in *.
  apply H2 in H7.
  intuition.
Qed.

Local Hint Constructors NoDup.

Theorem In_InA : forall A x ls,
  In x ls -> SetoidList.InA (WordMap.eq_key (elt:=A)) x ls.
  induction ls; simpl; intuition.
Qed.

Theorem NoDupA_NoDup : forall A ls,
  SetoidList.NoDupA (WordMap.eq_key (elt:=A)) ls -> NoDup ls.
  induction 1; eauto.
  constructor; auto.
  intro; apply H.
  eauto using In_InA.
Qed.

Theorem In_InA' : forall A x ls,
  In x ls -> SetoidList.InA (WordMap.eq_key_elt (elt:=A)) x ls.
  induction ls; simpl; intuition.
  subst; constructor; hnf; auto.
Qed.

Theorem InA_In : forall A x ls,
  SetoidList.InA (WordMap.eq_key_elt (elt:=A)) x ls -> In x ls.
  induction 1; simpl; intuition idtac.
  destruct x, y; simpl in *.
  hnf in H; simpl in *; intuition subst.
  tauto.
Qed.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Inv.
  Module Import InvMake := Make E.
  Module Import InvMake2 := Make M.
  Module Import Sem := Semantics.Make E.
  Require Import WordMap.
  Require Import FMapFacts.
  Module Properties := Properties WordMap.
  
  Lemma preserve_store : forall k v pairs h,
    List.Forall (fun p => match snd p with
                            | inl _ => True
                            | inr _ => ~WordMap.In (fst p) h
                          end) pairs
    -> NoDup (map fst (filter (fun p => Semantics.is_adt (snd p)) pairs))
    -> WordMap.MapsTo k v h
    -> WordMap.MapsTo k v (fold_left store_pair pairs h).
    induction pairs; simpl in *; intuition.
    inversion_clear H; simpl in *.
    apply IHpairs; auto.

    simpl in *.
    inversion_clear H; simpl in *.
    inversion_clear H0.
    apply IHpairs; auto.
    unfold store_pair; simpl.
    eapply Forall_forall; intros.
    case_eq (snd x); intuition idtac.
    eapply Forall_forall in H3; [ | eassumption ].
    unfold heap_upd in H6.
    rewrite H5 in *.
    apply Properties.F.add_in_iff in H6; intuition subst.
    apply H.
    apply in_map.
    apply filter_In; intuition idtac.
    unfold Semantics.is_adt.
    unfold WordMap.key, Semantics.ArgIn in *.
    rewrite H5; reflexivity.
    unfold store_pair; simpl.
    unfold heap_upd.
    apply Properties.F.add_mapsto_iff.
    right; intuition subst.
    apply H2.
    exists v; auto.
  Qed.

  Lemma keep_key : forall w a1 pairs,
    In (w, inr a1) pairs
    -> In w (map fst (filter
      (fun p : W * (W + ADTValue) =>
        match snd p with
          | inl _ => false
          | inr _ => true
        end) pairs)).
    induction pairs; simpl; intuition (subst; simpl in *); intuition idtac.
  Qed.

  Lemma store_keys : forall k v pairs h,
    WordMap.MapsTo k v (fold_left store_pair pairs h)
    -> In (k, inr v) pairs \/ WordMap.MapsTo k v h.
    induction pairs; simpl; intuition idtac.
    apply IHpairs in H; intuition idtac.
    unfold store_pair in H0; simpl in H0.
    destruct b; auto.
    unfold heap_upd in H0.
    apply Properties.F.add_mapsto_iff in H0; intuition subst; auto.
  Qed.
  
  Lemma store_keys'' : forall k v pairs h,
    WordMap.MapsTo k v h
    -> ~In k (map fst (filter (fun p => Semantics.is_adt (snd p)) pairs))
    -> WordMap.MapsTo k v (fold_left store_pair pairs h).
    induction pairs; simpl; intuition (try discriminate; eauto);
      unfold Semantics.is_adt in *; simpl in *.

    destruct b; auto.
    simpl in *; intuition subst.
    apply IHpairs; auto.
    unfold store_pair, heap_upd; simpl.
    apply Properties.F.add_mapsto_iff; auto.
  Qed.

  Lemma store_keys' : forall k v pairs h,
    In (k, inr v) pairs
    -> NoDup (map fst (filter (fun p => Semantics.is_adt (snd p)) pairs))
    -> WordMap.MapsTo k v (fold_left store_pair pairs h).
    induction pairs; simpl; intuition (try discriminate; eauto);
      unfold Semantics.is_adt in *; simpl in *.

    injection H1; clear H1; intros; subst.
    inversion_clear H0.
    apply store_keys''; auto.
    unfold store_pair, heap_upd; simpl.
    apply Properties.F.add_mapsto_iff; auto.

    inversion_clear H0; eauto.
  Qed.

End Make.
