Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import Inv.
  Module Import InvMake := Make E.
  Import Semantics.
  Import SemanticsMake.
  Require Import WordMap.
  Require Import FMapFacts.
  Module Properties := Properties WordMap.
  Module Facts := Facts WordMap.

  Lemma make_triples_Word : forall pairs outs, length outs = length pairs -> map (@Word _) (make_triples pairs outs) = map fst pairs.
    induction pairs; destruct outs; simpl; intuition.
    f_equal; auto.
  Qed.

  Lemma make_triples_Word_ADTIn : forall pairs outs, length outs = length pairs -> map (fun x => (Word x, ADTIn x)) (make_triples pairs outs) = pairs.
    induction pairs; destruct outs; simpl; intuition.
    f_equal; auto.
  Qed.

  Lemma make_triples_ADTIn : forall pairs outs, length outs = length pairs -> map (@ADTIn _) (make_triples pairs outs) = map snd pairs.
    induction pairs; destruct outs; simpl; intuition.
    f_equal; auto.
  Qed.

  Lemma make_triples_length : forall pairs outs, length outs = length pairs -> length (make_triples pairs outs) = length pairs.
    induction pairs; destruct outs; simpl; intuition.
  Qed.

  Import WordMap.

  Lemma separated_Equal : forall h1 h2 a b,
    WordMap.Equal h1 h2
    -> Semantics.separated (ADTValue := ADTValue) h1 a b
    -> Semantics.separated h2 a b.
    unfold Semantics.separated; intuition.
    right; intro; apply H1.
    eapply Properties.F.In_m; eauto.
  Qed.

  Lemma good_inputs_Equal : forall A h1 h2 pairs,
    WordMap.Equal (elt := A) h1 h2
    -> Semantics.good_inputs h1 pairs
    -> Semantics.good_inputs h2 pairs.
    unfold Semantics.good_inputs; intuition.
    eapply Forall_weaken; [ | eassumption ].
    unfold Semantics.word_adt_match; intros.
    destruct x; simpl in *.
    destruct s; auto.
    erewrite <- Facts.find_m; eauto.
  Qed.    

  Hint Constructors Semantics.RunsTo.

  Lemma store_out_Equal : forall triples h1 h2,
    WordMap.Equal h1 h2
    -> WordMap.Equal
    (fold_left (Semantics.store_out (ADTValue:=ADTValue)) triples h1)
    (fold_left (Semantics.store_out (ADTValue:=ADTValue)) triples h2).
    induction triples; simpl; intuition.
    apply IHtriples.
    unfold Semantics.store_out.
    destruct a; simpl.
    destruct ADTIn; auto.
    destruct ADTOut; auto.
    apply Properties.F.add_m; auto.
    apply Properties.F.remove_m; auto.
  Qed.

  Lemma heap_upd_option_Equal : forall h1 h2 a b,
    WordMap.Equal h1 h2
    -> WordMap.Equal (heap_upd_option h1 a b) (heap_upd_option h2 a b).
    unfold heap_upd_option, Semantics.heap_upd_option; intros.
    destruct b; auto.
    apply Properties.F.add_m; auto.
  Qed.

  Ltac t :=
    repeat match goal with
             | [ x := _ |- _ ] => subst x
             | [ H : forall h : WordMap.t _, _, H' : WordMap.Equal _ _ |- _ ] =>
               apply H in H'; clear H;
                 destruct H'; intuition
           end; eauto.

  Lemma RunsTo_Equal : forall env s st st',
    Semantics.RunsTo (ADTValue := ADTValue) env s st st'
    -> forall h, WordMap.Equal (snd st) h
      -> exists h', WordMap.Equal (snd st') h'
        /\ Semantics.RunsTo (ADTValue := ADTValue) env s (fst st, h) (fst st', h').
    induction 1; intuition eauto.

    t.
    t.
    t.
    t.
    t.

    t.
    simpl in *.
    descend; eauto.
    change (fst v) with (fst (fst v, h)) at 2.
    eapply RunsToCallInternal; eauto.

    t.
    descend; eauto.
    change (fst v) with (fst (fst v, h)) at 2.
    eapply RunsToCallForeign; eauto.
    simpl; eapply good_inputs_Equal; eauto.
    simpl; eapply separated_Equal; eauto.
    apply store_out_Equal; auto.
    simpl.
    apply heap_upd_option_Equal.
    apply store_out_Equal; auto.

    simpl.
    descend; eauto.
    change h with (snd (fst v, h)) at 2.
    change (fst v) with (fst (fst v, h)) at 2.
    eauto.

    t.
    descend; eauto; econstructor.
  Qed.

  Lemma Safe_Equal : forall env s vs h h',
    Semantics.Safe (ADTValue := ADTValue) env s (vs, h)
    -> WordMap.Equal h h'
    -> Semantics.Safe env s (vs, h').
    intros.
    apply (Safe_coind (fun s st =>
      exists h, WordMap.Equal h (snd st)
        /\ Semantics.Safe env s (fst st, h))); eauto; intuition idtac;
    try match goal with
          | [ H : Logic.ex _ |- _ ] => destruct H; intuition idtac
        end.

    inversion_clear H3; eauto.

    inversion_clear H4.
    eapply RunsTo_Equal in H2.
    destruct H2; intuition idtac.
    apply H5 in H6.
    descend; eauto.
    apply Properties.F.Equal_sym; auto.
    apply Properties.F.Equal_sym; auto.

    inversion_clear H3; simpl in *; intuition subst.
    eauto.
    eauto.

    intros.
    destruct H1; intuition.
    inversion H3; clear H3.

    subst loop0 loop1.
    subst.
    left; intuition.
    eauto.
    simpl in *.
    eapply RunsTo_Equal in H1.
    destruct H1; intuition idtac.
    apply H8 in H4.
    descend; eauto.
    apply Properties.F.Equal_sym; auto.
    apply Properties.F.Equal_sym; auto.

    subst loop0 loop1.
    subst.
    right; intuition.

    inversion_clear H3; simpl in *.
    subst vs0 heap fs.
    subst; simpl in *.
    eauto 10.
    subst vs0 heap fs.
    subst; simpl in *.
    right; descend; eauto.
    eapply good_inputs_Equal; eauto.

    inversion_clear H4.
    tauto.
  Qed.

  Require Import RepInv.

  Module Make(R : RepInv E).
    Module Import Inner := InvMake.Make(R).

    Require Import LayoutHintsUtil.

    Lemma is_heap_Equal : forall h h',
      WordMap.Equal h h'
      -> is_heap h ===> is_heap h'.
      intros; apply starL_permute; unfold heap_elements; intuition.
      apply NoDupA_NoDup; apply WordMap.elements_3w.
      apply NoDupA_NoDup; apply WordMap.elements_3w.

      apply In_InA' in H0.
      apply InA_In.
      apply Properties.F.elements_mapsto_iff in H0.
      apply Properties.F.elements_mapsto_iff.
      eapply Properties.F.Equal_mapsto_iff; eauto.
      apply Properties.F.Equal_sym; auto.

      apply In_InA' in H0.
      apply InA_In.
      apply Properties.F.elements_mapsto_iff in H0.
      apply Properties.F.elements_mapsto_iff.
      eapply Properties.F.Equal_mapsto_iff; eauto.
    Qed.
  End Make.

  Lemma fold_weaken : forall k v ls h1 h2,
    WordMap.MapsTo k v (fold_left store_out ls h1)
    -> (forall k' v', WordMap.MapsTo k' v' h1 -> WordMap.MapsTo k' v' h2)
    -> WordMap.MapsTo k v (fold_left store_out ls h2).
    induction ls; simpl; intuition.
    eapply IHls; eauto.
    unfold store_out, Semantics.store_out; intros.
    destruct a; simpl in *.
    destruct ADTIn; auto.
    destruct ADTOut; auto.
    apply Properties.F.add_mapsto_iff;
      apply Properties.F.add_mapsto_iff in H1; intuition subst.
    eauto.

    apply Properties.F.remove_mapsto_iff;
      apply Properties.F.remove_mapsto_iff in H1; intuition subst.
    eauto.
  Qed.

  Lemma fold_fwd : forall k v ls h,
    WordMap.MapsTo k v (fold_left store_pair ls h)
    -> WordMap.MapsTo k v h
    \/ List.In (k, inr v) ls.
    induction ls; simpl; intuition.
    apply IHls in H; intuition.
    unfold store_pair in H0; simpl in H0.
    destruct b; simpl in *; auto.
    apply Properties.F.add_mapsto_iff in H0; intuition subst.
    eauto.
  Qed.

  Lemma foldp_bwd : forall k ls h,
    WordMap.In k h \/ (exists v, List.In (k, inr v) ls)
    -> WordMap.In k (fold_left store_pair ls h).
    induction ls; simpl; intuition.
    firstorder.
    destruct H0; intuition.
    eauto.
    eapply IHls.
    unfold store_pair; simpl.
    unfold heap_upd; simpl.
    left.
    apply Properties.F.add_in_iff.
    auto.
    destruct H0; intuition.
    injection H0; clear H0; intros; subst.
    apply IHls.
    unfold store_pair; simpl.
    unfold heap_upd; simpl.
    left.
    apply Properties.F.add_in_iff.
    auto.
    eauto.
  Qed.

  Lemma foldp_fwd : forall k ls h,
    WordMap.In k (fold_left store_pair ls h)
    -> WordMap.In k h \/ (exists v, List.In (k, inr v) ls).
    induction ls; simpl; intuition.
    apply IHls in H; clear IHls; intuition.
    unfold store_pair in H0; simpl in H0.
    destruct b; simpl; auto.
    unfold heap_upd in H0; simpl in H0.
    apply Properties.F.add_in_iff in H0; intuition subst.
    eauto.
    destruct H0.
    eauto.
  Qed.

  Lemma fold_fwd' : forall k v ls h,
    WordMap.MapsTo k v (fold_left store_out ls h)
    -> (WordMap.MapsTo k v h /\ forall a o, ~List.In {| Word := k; ADTIn := inr a; ADTOut := o |} ls)
    \/ exists a, List.In {| Word := k; ADTIn := inr a; ADTOut := Some v |} ls.
    induction ls; simpl; intuition.
    apply IHls in H; intuition.

    unfold store_out, Semantics.store_out in H; simpl in H.
    destruct a; simpl in *.
    destruct ADTIn.
    left; intuition eauto.
    discriminate.
    destruct ADTOut.
    apply Properties.F.add_mapsto_iff in H; intuition subst.
    eauto.
    left; intuition.
    eauto 2.
    apply Properties.F.remove_mapsto_iff in H; intuition subst.
    left; intuition.
    eauto 2.
    destruct H0.
    eauto.
  Qed.

  Lemma heap_merge_store_out : 
    forall h pairs outs, 
      good_inputs h pairs -> 
      let h1 := make_heap pairs in 
      let triples := make_triples pairs outs in
      WordMap.Equal (heap_merge (heap_diff h h1) (fold_left store_out triples h1))
      (fold_left store_out triples h).
    simpl; intros.
    unfold heap_merge, heap_diff.
    apply Properties.F.Equal_mapsto_iff; intuition.

    apply Properties.update_mapsto_iff in H0; intuition.

    eapply fold_weaken; eauto.
    intros.
    destruct H.
    apply fold_fwd in H0; intuition.
    apply Properties.F.empty_mapsto_iff in H3; tauto.
    eapply Forall_forall in H; try apply H3.
    hnf in H; simpl in H.
    apply WordMap.find_2; auto.

    apply Properties.diff_mapsto_iff in H0; intuition subst.

    Lemma In_make_heap' : forall k pairs h,
      WordMap.In (elt:=ADTValue) k (fold_left store_pair pairs h)
      -> WordMap.In k h \/ exists a, List.In (k, inr a) pairs.
      induction pairs; simpl; intuition.
      apply IHpairs in H; intuition.
      unfold store_pair in H0; simpl in H0.
      destruct b; auto.
      unfold heap_upd in H0.
      apply Properties.F.add_in_iff in H0; intuition subst.
      eauto.
      destruct H0; intuition subst.
      eauto.
    Qed.

    Lemma In_make_heap : forall k pairs,
      WordMap.In (elt:=ADTValue) k (make_heap pairs)
      -> exists a, List.In (k, inr a) pairs.
      intros.
      apply In_make_heap' in H; intuition eauto.
      apply Properties.F.empty_in_iff in H0; tauto.
    Qed.

    Lemma keep_when_agrees : forall k e pairs h outs,
      ~WordMap.In k (make_heap pairs)
      -> WordMap.MapsTo k e h
      -> WordMap.MapsTo k e (fold_left store_out (make_triples pairs outs) h).
      induction pairs; destruct outs; simpl; intuition.
      apply IHpairs; clear IHpairs; intros.
      apply H.
      unfold make_heap.
      apply foldp_bwd; right.
      apply In_make_heap in H1; destruct H1; intuition subst.
      simpl; eauto.
      unfold store_out, Semantics.store_out; simpl.
      destruct a; simpl in *.
      destruct a; auto.
      destruct a0.
      apply WordMap.add_2; auto.
      intro; subst.
      exfalso.
      apply H.
      apply foldp_bwd; simpl; eauto.
      apply WordMap.remove_2; auto.
      intro; subst.
      exfalso.
      apply H.
      apply foldp_bwd; simpl; eauto.
    Qed.

    eapply keep_when_agrees; eauto.

    apply fold_fwd' in H0; intuition idtac.

    Focus 2.
    destruct H1.
    destruct H.

    apply Properties.update_mapsto_iff; left.

    Lemma get_pair : forall k x e pairs outs h,
      Semantics.disjoint_ptrs pairs
      -> List.In {| Word := k; ADTIn := inr x; ADTOut := Some e |} (make_triples pairs outs)
      -> WordMap.MapsTo k e (fold_left store_out (make_triples pairs outs) h).
      induction pairs; destruct outs; simpl; intuition.
      simpl in *; intuition.
      injection H1; clear H1; intros; subst.
      assert (WordMap.MapsTo k e (store_out h {| Word := k; ADTIn := inr x; ADTOut := Some e |})).
      unfold store_out, Semantics.store_out; simpl.
      apply WordMap.add_1; auto.
      generalize dependent (store_out h {| Word := k; ADTIn := inr x; ADTOut := Some e |}).
      assert (forall v, ~List.In (k, inr v) pairs).
      intuition.
      hnf in H.
      simpl in H.
      inversion_clear H.
      apply H1.
      change k with (fst (k, @inr W _ v)).
      apply in_map.
      apply filter_In; tauto.
      generalize dependent H0.
      clear.
      generalize dependent outs.
      induction pairs; destruct outs; simpl; intuition.
      apply IHpairs; eauto.
      unfold store_out, Semantics.store_out; simpl.
      destruct a; simpl in *.
      destruct a; auto.
      destruct a0.
      apply WordMap.add_2; auto.
      intro; subst; eauto.
      apply WordMap.remove_2; auto.
      intro; subst; eauto.

      apply IHpairs.
      hnf in H.
      simpl in H.
      destruct b; simpl in *; auto.
      inversion H; auto.
      auto.
    Qed.

    eapply get_pair; eauto.

    case_eq (WordMap.mem k (make_heap pairs)); intros.

    apply Properties.update_mapsto_iff; left; intuition.

    Lemma get_pair' : forall k e pairs outs h,
      Semantics.disjoint_ptrs pairs
      -> WordMap.MapsTo k e h
      -> (forall a o, ~List.In {| Word := k; ADTIn := inr a; ADTOut := o |} (make_triples pairs outs))
      -> WordMap.MapsTo k e (fold_left store_out (make_triples pairs outs) h).
      induction pairs; destruct outs; simpl; intuition.
      apply IHpairs.
      hnf in H.
      simpl in H.
      destruct b; simpl in H; auto.
      inversion H; auto.
      simpl.
      unfold store_out, Semantics.store_out; simpl.
      destruct b; auto.
      destruct a0; simpl in *.
      apply WordMap.add_2; auto.
      intro; subst; eauto.
      apply WordMap.remove_2; auto.
      intro; subst; eauto.
      simpl in *.
      eauto.
    Qed.
      
    apply get_pair'; auto.
    destruct H; auto.
    apply WordMap.mem_2 in H1.
    apply In_make_heap in H1; destruct H1.
    destruct H.
    eapply Forall_forall in H; [ | eassumption ].
    hnf in H; simpl in H.
    apply WordMap.find_1 in H0.
    rewrite H0 in H; injection H; clear H; intros; subst.

    unfold make_heap.

    Lemma grab_it : forall k x pairs h,
      List.In (k, inr x) pairs
      -> Semantics.disjoint_ptrs pairs
      -> WordMap.MapsTo k x (fold_left store_pair pairs h).
      induction pairs; simpl; intuition.
      injection H1; clear H1; intros; subst.
      hnf in H0.
      simpl in H0.
      inversion_clear H0.
      generalize dependent H.
      clear IHpairs H1.
      assert (WordMap.MapsTo k x (store_pair h (k, inr x))).
      unfold store_pair; simpl.
      apply WordMap.add_1; auto.
      generalize dependent (store_pair h (k, inr x)).
      induction pairs; simpl in *; intuition.
      simpl in *; intuition subst.
      apply IHpairs.
      unfold store_pair; simpl.
      apply WordMap.add_2; auto.
      auto.

      apply IHpairs; auto.
      hnf in H0.
      simpl in H0.
      inversion_clear H0; auto.
    Qed.

    apply grab_it; auto.

    apply Properties.update_mapsto_iff; right; intuition.
    apply Properties.diff_mapsto_iff; intuition.
    apply Properties.F.not_mem_in_iff in H3; tauto.
    assert (~WordMap.In k (make_heap pairs)).
    intro.
    apply Properties.F.not_mem_in_iff in H4; tauto.
    clear H1.
    apply H4; clear H4.

    Lemma i_didn't_do_it : forall k ls h,
      (forall a o, ~List.In {| Word := k; ADTIn := inr a; ADTOut := o |} ls)
      -> WordMap.In k (fold_left store_out ls h)
      -> WordMap.In k h.
      induction ls; simpl; intuition.
      apply IHls in H0; eauto.
      unfold store_out, Semantics.store_out in H0.
      destruct a; simpl in *.
      destruct ADTIn; auto.
      destruct ADTOut.
      apply Properties.F.add_in_iff in H0; intuition subst.
      exfalso; eauto.
      apply Properties.F.remove_in_iff in H0; intuition subst.
    Qed.

    eapply i_didn't_do_it; eauto.
  Qed.

End Make.