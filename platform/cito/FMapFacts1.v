Set Implicit Arguments.

Require Import DecidableType.
Require Import FMapInterface.

Module WFacts_fun (E:DecidableType)(Import M:WSfun E).

  Require Import FMapFacts.

  Module Import F := WFacts_fun E M.
  Module Import P := WProperties_fun E M.

  Section Elt.
    Variable elt:Type.

    Implicit Types m : t elt.
    Implicit Types x y z k : key.
    Implicit Types e v : elt.
    Implicit Types ls : list (key * elt).

    Notation eqke := (@eq_key_elt elt).
    Notation eqk := (@eq_key elt).
    
    Definition to_map := of_list.

    Definition keys m := List.map (@fst _ _) (elements m).

    Definition find_list k := findA (B := elt) (eqb k).

    Definition option_dec A (x : option A) : {a | x = Some a} + {x = None}.
      destruct x.
      left.
      exists a.
      eauto.
      right.
      eauto.
    Qed.

    Require Import GeneralTactics.

    Definition NoDupKey := NoDupA eqk.
    Definition InPair := InA eqke.

    Lemma NoDup_app_find_list : forall ls1 ls2 k v, NoDupKey (ls1 ++ ls2) -> find_list k ls1 = Some v -> find_list k (ls1 ++ ls2) = Some v.
      admit.
    Qed.

    Lemma NoDup_app_find_list_2 : forall ls1 ls2 k v, NoDupKey (ls1 ++ ls2) -> find_list k ls2 = Some v -> find_list k (ls1 ++ ls2) = Some v.
      admit.
    Qed.

    Lemma find_list_neq : forall k v k' ls, NoDupKey ls -> ~ E.eq k' k -> find_list k' ls = find_list k' (ls ++ (k, v) :: nil).
      admit.
    Qed.

    Lemma NoDup_cons : forall ls k1 v1 k2 v2, NoDupKey ((k1, v1) :: ls) -> InPair (k2, v2) ls -> ~ E.eq k1 k2.
      admit.
    Qed.

    Lemma NoDup_incl : forall ls1 ls2, NoDupKey ls2 -> incl ls1 ls2 -> NoDupKey ls1.
      admit.
    Qed.

    Lemma In_find_list_Some_left : forall k v ls, NoDupKey ls -> InPair (k, v) ls -> find_list k ls = Some v.
    Proof.
      induction ls; simpl; intros.
      eapply InA_nil in H0; intuition.
      inversion H0; subst.
      unfold find_list in *; destruct a; simpl in *.
      destruct H2; simpl in *.
      subst.
      unfold eqb.
      destruct (eq_dec k k0).
      eauto.
      intuition.
      destruct a; simpl in *.
      generalize H2; eapply NoDup_cons in H2; eauto; intro.
      eapply IHls in H1.
      unfold find_list in *; simpl in *.
      unfold eqb in *.
      destruct (eq_dec k k0); intuition.
      eapply E.eq_sym in e0.
      intuition.
      eapply NoDup_incl.
      eauto.
      intuition.
    Qed.

    Lemma In_find_list_Some_right : forall ls k v, NoDupKey ls -> find_list k ls = Some v -> InPair (k, v) ls.
    Proof.
      induction ls; simpl; intros.
      unfold find_list in *; simpl in *.
      discriminate.
      unfold find_list in *; destruct a; simpl in *.
      unfold eqb in *.
      destruct (eq_dec k k0); intuition.
      injection H0; intros; subst.
      left.
      econstructor; simpl; eauto.
      right.
      eapply IHls.
      eapply NoDup_incl.
      eauto.
      intuition.
      eauto.
    Qed.

    Lemma In_find_list_Some : forall ls k v, NoDupKey ls -> (InPair (k, v) ls <-> find_list k ls = Some v).
      split; intros.
      eapply In_find_list_Some_left; eauto.
      eapply In_find_list_Some_right; eauto.
    Qed.

    Lemma In_find_Some : forall k v m, InPair (k, v) (elements m) <-> find k m = Some v.
      split; intros.
      eapply find_1.
      eapply elements_2; eauto.
      eapply find_2 in H.
      eapply elements_1 in H; eauto.
    Qed.

    Lemma None_not_Some : forall a, a = None <-> ~ exists v, a = Some v.
      split; intros.
      intuition.
      openhyp.
      subst.
      discriminate.
      destruct (option_dec a); eauto.
      destruct s.
      contradict H.
      eexists; eauto.
    Qed.

    Lemma option_univalence : forall A a b, a = b <-> forall (v : A), a = Some v <-> b = Some v.
      split; intros.
      subst; split; eauto.
      destruct (option_dec a).
      destruct s.
      subst.
      symmetry.
      eapply H; eauto.
      subst.
      destruct (option_dec b).
      destruct s.
      subst.
      eapply H; eauto.
      eauto.
    Qed.

    Lemma find_list_elements : forall m k, find_list k (elements m) = find k m.
      intros.
      eapply option_univalence.
      intros.
      split; intros.
      eapply In_find_Some.
      eapply In_find_list_Some in H.
      eauto.
      eapply elements_3w.
      eapply In_find_Some in H.
      eapply In_find_list_Some.
      eapply elements_3w.
      eauto.
    Qed.

    Lemma In_find_list_not_None_left : forall ls k, InA E.eq k (List.map (@fst _ _) ls) -> find_list k ls <> None.
    Proof.
      induction ls; simpl; intros.
      eapply InA_nil in H; intuition.
      inversion H; subst.
      unfold find_list in *; destruct a; simpl in *.
      unfold eqb in *.
      destruct (eq_dec k k0); intuition.
      discriminate.
      eapply IHls in H1.
      unfold find_list in *; destruct a; simpl in *.
      destruct (eqb k k0); intuition.
      discriminate.
    Qed.

    Lemma In_find_list_not_None_right : forall ls k, find_list k ls <> None -> InA E.eq k (List.map (@fst _ _) ls).
    Proof.
      induction ls; simpl; intros.
      intuition.
      unfold find_list in *; destruct a; simpl in *.
      unfold eqb in *.
      destruct (eq_dec k k0); intuition.
    Qed.

    Lemma In_find_list_not_None : forall ls k, InA E.eq k (List.map (@fst _ _) ls) <-> find_list k ls <> None.
      intros.
      split.
      eapply In_find_list_not_None_left.
      eapply In_find_list_not_None_right.
    Qed.

    Lemma ex_up : forall A (e : option A),
                    (e = None -> False)
                    -> exists (v : A), e = Some v.
      destruct e; intuition eauto.
    Qed.

    Lemma In_find_not_None : forall k m, find k m <> None <-> In k m.
      unfold In.
      split; intros.
      eapply ex_up in H.
      openhyp.
      eapply find_2 in H.
      eexists; eauto.

      openhyp.
      eapply find_1 in H.
      rewrite H.
      intuition.
      discriminate.
    Qed.

    Lemma In_In_keys : forall k m, In k m <-> InA E.eq k (keys m).
      split; intros.
      eapply In_find_not_None in H.
      eapply In_find_list_not_None.
      rewrite find_list_elements.
      eauto.
      eapply In_find_not_None.
      unfold keys in *.
      eapply In_find_list_not_None in H.
      rewrite find_list_elements in H.
      eauto.
    Qed.

    Lemma add_4 : forall m x y e, ~ E.eq x y -> find y (add x e m) = find y m.
      intros.
      eapply option_univalence.
      split; intros.
      eapply find_1.
      eapply add_3; eauto.
      eapply find_2; eauto.
      eapply find_1.
      eapply add_2; eauto.
      eapply find_2; eauto.
    Qed.

    Lemma map_3 : forall B (f : elt -> B) k m, In k m -> In k (map f m).
      intros; eapply map_in_iff; eauto.
    Qed.

    Lemma map_4 : forall B (f : elt -> B) k m, In k (map f m) -> In k m.
      intros; eapply map_in_iff; eauto.
    Qed.

    Lemma find_map : forall B (f : elt -> B) k v m, find k m = Some v -> find k (map f m) = Some (f v).
      intros.
      eapply find_2 in H.
      eapply find_1.
      eapply map_1; eauto.
    Qed.

    Lemma MapsTo_In : forall k v m, MapsTo k v m -> In k m.
      intros; eexists; eauto.
    Qed.

  End Elt.

End WFacts_fun.

Require Import DecidableTypeEx.

Module UWFacts_fun (E : UsualDecidableType) (Import M : WSfun E).

  Lemma InA_eq_List_In : forall elt ls x, InA (@eq elt) x ls <-> List.In x ls.
    induction ls; simpl; intros.
    intuition.
    eapply InA_nil in H; eauto.
    split; intros.
    inversion H; subst.
    eauto.
    right.
    eapply IHls.
    eauto.
    destruct H.
    subst.
    econstructor 1.
    eauto.
    econstructor 2.
    eapply IHls.
    eauto.
  Qed.

  Definition equiv_2 A B p1 p2 := forall (a : A) (b : B), p1 a b <-> p2 a b.

  Lemma equiv_2_trans : forall A B a b c, @equiv_2 A B a b -> equiv_2 b c -> equiv_2 a c.
    unfold equiv_2; intros; split; intros.
    eapply H0; eapply H; eauto.
    eapply H; eapply H0; eauto.
  Qed.

  Require Import GeneralTactics.

  Lemma eq_key_elt_eq : forall elt, equiv_2 (@eq_key_elt elt) eq.
    split; intros.
    unfold eq_key_elt in *.
    openhyp.
    destruct a; destruct b; simpl in *; subst; eauto.
    subst.
    unfold eq_key_elt in *.
    eauto.
  Qed.

  Theorem InA_weaken : forall A (P : A -> A -> Prop) (x : A) (ls : list A),
                         SetoidList.InA P x ls
                         -> forall (P' : A -> A -> Prop) x',
                              (forall y, P x y -> P' x' y)
                              -> SetoidList.InA P' x' ls.
    induction 1; simpl; intuition.
  Qed.
  
  Lemma equiv_InA : forall elt (eq1 eq2 : elt -> elt -> Prop), equiv_2 eq1 eq2 -> equiv_2 (InA eq1) (InA eq2).
    unfold equiv_2; split; intros; eapply InA_weaken; eauto; intros; eapply H; eauto.
  Qed.

  Lemma InA_eq_key_elt_InA_eq : forall elt, equiv_2 (InA (@eq_key_elt elt)) (InA eq).
    intros; eapply equiv_InA; eapply eq_key_elt_eq.
  Qed.

  Lemma InA_eq_key_elt_List_In : forall elt ls x, InA (@eq_key_elt elt) x ls <-> List.In x ls.
    intros; eapply equiv_2_trans.
    eapply InA_eq_key_elt_InA_eq.
    unfold equiv_2; intros; eapply InA_eq_List_In.
  Qed.

  Module Import WFacts := WFacts_fun E M.
  Import F P.

  Lemma In_fst_elements_In : forall elt m k, List.In k (List.map (@fst _ _) (elements m)) <-> @In elt k m.
    split; intros.
    eapply InA_eq_List_In in H.
    eapply In_In_keys in H; eauto.
    eapply InA_eq_List_In.
    specialize In_In_keys; intros; unfold keys in *; eapply H0; eauto.
  Qed.

  Lemma InA_eqk_elim : forall elt ls k v, InA (@eq_key elt) (k, v) ls -> exists v', InA (@eq_key_elt elt) (k, v') ls.
    induction ls; simpl; intros.
    eapply InA_nil in H; intuition.
    destruct a; simpl in *.
    inversion H; subst.
    unfold eq_key in *; simpl in *.
    subst.
    eexists.
    econstructor.
    unfold eq_key_elt; simpl in *.
    eauto.
    eapply IHls in H1.
    openhyp.
    eexists.
    econstructor 2.
    eauto.
  Qed.

  Lemma NoDupKey_NoDup_fst : forall elt ls, @NoDupKey elt ls <-> NoDup (List.map (@fst _ _) ls).
    induction ls; simpl; intros.
    split; intros; econstructor.
    destruct a; simpl in *.
    split; intros.
    inversion H; subst.
    econstructor.
    intuition.
    contradict H2.
    eapply in_map_iff in H0.
    openhyp.
    destruct x; simpl in *.
    subst.
    eapply InA_eqke_eqk.
    eauto.
    eapply InA_eq_key_elt_List_In.
    eauto.
    eapply IHls.
    eauto.

    inversion H; subst.
    econstructor.
    intuition.
    contradict H2.
    eapply InA_eqk_elim in H0.
    openhyp.
    eapply InA_eq_key_elt_List_In in H0.
    eapply in_map_iff.
    eexists.
    split.
    2 : eauto.
    eauto.
    eapply IHls; eauto.
  Qed.

  Lemma MapsTo_to_map : forall elt k (v : elt) ls, NoDupKey ls -> List.In (k, v) ls -> MapsTo k v (to_map ls).
    unfold to_map; intros.
    eapply of_list_1.
    eauto.
    eapply InA_eq_key_elt_List_In; eauto.
  Qed.

  Lemma In_to_map : forall elt ls k, @In elt k (to_map ls) <-> List.In k (List.map (@fst _ _) ls).
    unfold to_map.
    induction ls; simpl; intros.
    eapply empty_in_iff.
    unfold uncurry in *.
    destruct a; simpl in *.
    split; intros.
    eapply add_in_iff in H.
    openhyp.
    eauto.
    right.
    eapply IHls; eauto.
    eapply add_in_iff.
    openhyp.
    eauto.
    right.
    eapply IHls; eauto.
  Qed.

End UWFacts_fun.
