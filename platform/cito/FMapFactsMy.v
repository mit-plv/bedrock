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

    Lemma find_list_neq : forall k v k' ls, NoDupKey ls -> k' <> k -> find_list k' ls = find_list k' (ls ++ (k, v) :: nil).
      admit.
    Qed.

    Lemma NoDup_incl : forall ls1 ls2, NoDupKey ls2 -> incl ls1 ls2 -> NoDupKey ls1.
      admit.
    Qed.

    Lemma NoDup_cons : forall ls k1 v1 k2 v2, NoDupKey ((k1, v1) :: ls) -> InPair (k2, v2) ls -> ~ E.eq k1 k2.
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

    Definition InKey k ls := exists v, InPair (k, v) ls.

    Lemma In_fst_InKey : forall ls k, InA E.eq k (List.map (@fst _ _) ls) <-> InKey k ls.
(*      induction ls; simpl; split; intros.
      eapply InA_nil in H; intuition.
      unfold InKey in *.
      openhyp.
      eapply InA_nil in H; intuition.
      split; intros.*)
      admit.
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
(*here*)
    Lemma In_In_keys : forall k m, In k m <-> In k (keys m).
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

    Lemma add_4 : forall A m x y (e : A), x <> y -> find y (add x e m) = find y m.
      admit.
    Qed.

    Lemma map_3 : forall A B (f : A -> B) k m, In k m -> In k (map f m).
    Proof.
      intros.
      unfold In in *.
      unfold Raw.PX.In in *.
      openhyp.
      eapply map_1 in H.
      eexists.
      eauto.
    Qed.

    Lemma find_map : forall A B (f : A -> B) k v m, find k m = Some v -> find k (map f m) = Some (f v).
      intros.
      eapply find_2 in H.
      eapply find_1.
      eapply map_1; eauto.
    Qed.

