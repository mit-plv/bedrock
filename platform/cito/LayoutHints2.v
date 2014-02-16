Set Implicit Arguments.

Require Import ADT.
Require Import RepInv WordMap.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Inv.
  Module Import InvMake := Make E.
  Module Import InvMake2 := Make M.
  Import SemanticsMake.
  
  Section TopSection.

    Definition heap_to_split h (_ : list (W * ArgIn)) := is_heap h.

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

    Hint Constructors NoDup.

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

    Lemma split_heap' : forall pairs h, good_inputs h pairs -> heap_to_split h pairs ===> let h1 := make_heap pairs in is_heap h1 * is_heap (heap_diff h h1).
      unfold heap_to_split; induction pairs; simpl; intros.

      unfold heap_diff, heap_empty.
      eapply Himp_trans; [ | apply Himp_star_Emp' ].
      unfold is_heap, heap_elements.
      apply starL_permute.
      
      apply NoDupA_NoDup.
      apply WordMap.elements_3w.

      apply NoDupA_NoDup.
      apply WordMap.elements_3w.

      intuition.
      apply In_InA' in H0.
      apply InA_In.
      apply WordMap.elements_1.
      apply WordMap.elements_2 in H0.
      apply Properties.diff_mapsto_iff.
      intuition.
      destruct H1.
      eapply WordMap.empty_1; eauto.
      apply In_InA' in H0.
      apply WordMap.elements_2 in H0.
      apply Properties.diff_mapsto_iff in H0.
      intuition.
      apply InA_In.
      apply WordMap.elements_1; auto.

      unfold is_heap, heap_elements.
      destruct H.
      inversion_clear H.
      hnf in H1.
      hnf in H0.
      case_eq (snd a); intros.
      rewrite H in *; subst.
      unfold make_heap; simpl.
      unfold store_pair at 2 4.
      unfold ArgIn, Semantics.ArgIn.
      unfold WordMap.key in H.
      rewrite H.
      apply IHpairs.
      split; auto.
      hnf.
      simpl in H0.
      unfold ArgIn, Semantics.ArgIn in H0.
      rewrite H in H0.
      auto.

      rewrite H in H1.
      generalize H1; intro Ho.
      apply WordMap.find_2 in Ho.
      apply WordMap.elements_1 in Ho.
      apply InA_In in Ho.
      eapply starL_out in Ho.
      destruct Ho; intuition.
      eapply Himp_trans; [ apply H4 | ].
      clear H4; simpl.
      2: apply NoDupA_NoDup; apply WordMap.elements_3w.
      assert (In (fst a, a0) (WordMap.elements (elt:=elt) (make_heap (a :: pairs)))).
      unfold make_heap; simpl.
      
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

      apply InA_In.
      apply Properties.F.elements_mapsto_iff.
      simpl in H0.
      unfold Semantics.is_adt in H0.
      unfold WordMap.key, Semantics.ArgIn in *.
      rewrite H in *; simpl in *.
      inversion_clear H0.
      apply preserve_store; auto.
      apply Forall_forall; intros.
      case_eq (snd x0); intuition idtac.
      unfold store_pair in H8.
      unfold WordMap.key, ArgIn, Semantics.ArgIn in *.
      rewrite H in H8.
      unfold heap_upd in H8.
      eapply Properties.F.add_in_iff in H8; intuition idtac.
      2: destruct H9; eapply WordMap.empty_1; eauto.
      destruct a; simpl in *; subst.
      destruct x0; simpl in *; subst.
      
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

      eauto using keep_key.
      unfold store_pair.
      unfold WordMap.key, ArgIn, Semantics.ArgIn in *.
      rewrite H.
      unfold heap_upd.
      apply WordMap.add_1; auto.

      simpl in *.
      destruct a; simpl in *; subst; simpl in *.
      inversion_clear H0.
      eapply Himp_trans; [ | apply Himp_star_frame; [ apply starL_permute | apply Himp_refl ] ].
      instantiate (1 := (k, a0) :: heap_elements (make_heap pairs)).
      Focus 2.
      constructor.
      intro.
      unfold heap_elements, make_heap in H0.
      apply In_InA' in H0.
      apply WordMap.elements_2 in H0.

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

      apply store_keys in H0; intuition idtac.
      apply H.
      change k with (fst (k, @inr W _ a0)).
      apply in_map; apply filter_In; tauto.
      eapply WordMap.empty_1; eauto.
      apply NoDupA_NoDup; apply WordMap.elements_3w.
      2: apply NoDupA_NoDup; apply WordMap.elements_3w.
      Focus 2.
      simpl.
      split.
      destruct 1; subst.
      auto.
      unfold heap_elements in H0.
      
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

      apply InA_In.
      destruct x0.
      apply WordMap.elements_1.
      unfold make_heap; simpl.
      apply store_keys'; auto.
      apply In_InA' in H0.
      apply WordMap.elements_2 in H0.
      apply store_keys in H0; intuition idtac.
      exfalso; eapply WordMap.empty_1; eauto.

      intro.
      apply In_InA' in H0.
      destruct x0.
      apply WordMap.elements_2 in H0.
      unfold make_heap in H0; simpl in H0.
      apply store_keys in H0.
      intuition idtac.
      right.
      apply InA_In.
      apply WordMap.elements_1.
      apply store_keys'; auto.
      unfold store_pair in H7; simpl in H7.
      apply Properties.F.add_mapsto_iff in H7; intuition subst.
      auto.
      exfalso; eapply WordMap.empty_1; eauto.      
      
      simpl.
      eapply Himp_trans; [ | apply Himp_star_assoc' ].
      apply Himp_star_frame; try apply Himp_refl.
      eapply Himp_trans; [ apply starL_permute | ].
      auto.
      instantiate (1 := WordMap.elements (WordMap.remove k h)).
      apply NoDupA_NoDup; apply WordMap.elements_3w.
      split; intro.
      apply InA_In.
      destruct x0.
      apply WordMap.elements_1.
      apply Properties.F.remove_mapsto_iff.
      apply H6 in H0.
      destruct H0; split; auto.
      2: apply WordMap.elements_2; apply In_InA'; auto.
      apply In_InA' in H7; apply WordMap.elements_2 in H7.
      apply WordMap.find_1 in H7.
      congruence.
      apply In_InA' in H0.
      destruct x0; apply WordMap.elements_2 in H0.
      apply Properties.F.remove_mapsto_iff in H0.
      apply H6; intuition (try congruence).
      apply InA_In; apply WordMap.elements_1; auto.

      eapply Himp_trans; [ apply IHpairs | ]; clear IHpairs.
      split; auto.
      apply Forall_forall; intros.
      eapply Forall_forall in H2; [ | apply H0 ].
      hnf in H2; hnf.
      destruct x0; simpl in *.
      destruct s; auto.
      apply WordMap.find_1.
      apply Properties.F.remove_mapsto_iff.
      apply WordMap.find_2 in H2.
      intuition subst.
      apply H.
      change k0 with (@fst W (Semantics.ArgIn ADTValue) (k0, inr a)).
      apply in_map.
      apply filter_In; auto.

      apply Himp_star_frame; try apply Himp_refl.
      apply starL_permute; try (apply NoDupA_NoDup; apply WordMap.elements_3w); intros.
      intuition; apply InA_In; apply WordMap.elements_1;
        apply In_InA' in H0; apply WordMap.elements_2 in H0;
          apply Properties.diff_mapsto_iff; apply Properties.diff_mapsto_iff in H0; intuition idtac.
      apply Properties.F.remove_mapsto_iff in H7; tauto.
      apply Properties.F.remove_mapsto_iff in H7; intuition subst.
      destruct H0.
      eapply store_keys in H0; intuition idtac.
      simpl in *; intuition (try congruence).
      apply H8.
      eexists.
      eapply store_keys'; eauto.
      exfalso; eapply WordMap.empty_1; eauto.
      apply Properties.F.remove_mapsto_iff; intuition subst.
      apply H8.
      eexists; eapply store_keys'; eauto.
      simpl; eauto.
      auto.
      constructor; auto.
      apply H8.
      destruct H0.
      eapply store_keys in H0; intuition idtac.
      eexists.
      eapply store_keys'.
      simpl; eauto.
      constructor; auto.
      exfalso; eapply WordMap.empty_1; eauto.
    Qed.

    Lemma split_heap : forall h pairs, good_inputs h pairs -> heap_to_split h pairs ===> let h1 := make_heap pairs in is_heap h1 * is_heap (heap_diff h h1).
      eauto using split_heap'.
    Qed.

    Definition hints_split_heap : TacPackage.
      prepare split_heap tt.
    Defined.

  End TopSection.

End Make.