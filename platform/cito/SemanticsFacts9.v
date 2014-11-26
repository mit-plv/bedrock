Set Implicit Arguments.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import List.

  Require Import WordMap.
  Import WordMap.
  Require Import WordMapFacts.
  Import FMapNotations.
  Open Scope fmap_scope.

  Require Import GeneralTactics4.

  Arguments empty {_}.

  Require Import SemanticsUtil.

  Definition make_heap' := fold_right (fun x m => @store_pair ADTValue m x) empty.

  Definition no_clash A (p1 p2 : A * Value ADTValue) :=
    match snd p1, snd p2 with
      | ADT _, ADT _ => (fst p1 <> fst p2)%type
      | _, _ => True
    end.

  Definition no_clash_ls A p := List.Forall (@no_clash A p).

  Definition not_in_heap elt w (v : Value ADTValue) (h : WordMap.t elt) :=
    match v with
      | SCA _ => True
      | ADT _ => ~ WordMap.In w h
    end.

  Require Import Setoid.

  Add Morphism (@store_pair ADTValue) with signature Equal ==> eq ==> Equal as store_pair_Equal_m.
  Proof.
    intros st1 st2 Heq [w v].
    unfold store_pair.
    destruct v.
    eauto.
    simpl.
    rewrite Heq.
    reflexivity.
  Qed.

  Add Parametric Morphism elt : (@not_in_heap elt) with signature eq ==> eq ==> Equal ==> iff as not_in_heap_Equal_m.
  Proof.
    intros w v st1 st2 Heq.
    destruct v; simpl in *.
    intuition.
    rewrite Heq.
    intuition.
  Qed.

  Lemma store_pair_comm p1 p2 h : no_clash p1 p2 -> store_pair (store_pair h p1) p2 == store_pair (store_pair h p2) p1.
  Proof.
    intros Hnc.
    intros p.
    destruct p1 as [w1 v1].
    destruct p2 as [w2 v2].
    unfold store_pair.
    simpl.
    destruct v1 as [? | a1]; destruct v2 as [? | a2]; eauto.
    unfold no_clash in *.
    simpl in *.
    Require Import Word.
    destruct (weq p w2) as [? | Hne2].
    {
      subst.
      rewrite add_eq_o by eauto.
      rewrite add_neq_o by eauto.
      rewrite add_eq_o by eauto.
      eauto.
    }
    rewrite add_neq_o by eauto.
    destruct (weq p w1) as [? | Hne1].
    {
      subst.
      rewrite add_eq_o by eauto.
      rewrite add_eq_o by eauto.
      eauto.
    }
    rewrite add_neq_o by eauto.
    rewrite add_neq_o by eauto.
    rewrite add_neq_o by eauto.
    eauto.
  Qed.

  Definition DisjointPtrs A := List.ForallOrdPairs (@no_clash A).

  Require Import Memory.

  Definition disjoint_ptrs_ls (p : W * Value ADTValue) (pairs : list (W * Value ADTValue)):=
    match (snd p) with
      | SCA _ => True
      | ADT _ => ~ List.In (fst p) (List.map fst (List.filter (fun p => is_adt (snd p)) pairs))
    end.

  Require Import Semantics.

  Lemma disjoint_ptrs_cons_elim' pairs : forall p, disjoint_ptrs (p :: pairs) -> disjoint_ptrs_ls p pairs /\ disjoint_ptrs pairs.
  Proof.
    induction pairs; simpl; intros [w1 v1] H.
    {
      split.
      unfold disjoint_ptrs_ls; simpl.
      destruct v1; intuition.
      unfold disjoint_ptrs; simpl.
      econstructor.
    }
    destruct a as [w2 v2]; simpl in *.
    destruct v1 as [? | a1]; destruct v2 as [? | a2]; simpl in *; try solve [unfold disjoint_ptrs, disjoint_ptrs_ls in *; simpl in *; eauto].
    {
      inversion H; subst; clear H.
      split; eauto.
    }
    {
      inversion H; subst; clear H.
      split; eauto.
    }
  Qed.

  Lemma disjoint_ptrs_ls_no_clash_ls pairs : forall p, disjoint_ptrs_ls p pairs -> no_clash_ls p pairs.
  Proof.
    induction pairs; simpl; intros [w1 v1] H.
    {
      econstructor.
    }
    destruct a as [w2 v2]; simpl in *.
    destruct v1 as [? | a1]; destruct v2 as [? | a2]; simpl in *; eauto.
    {
      unfold disjoint_ptrs_ls, no_clash_ls, no_clash in *.
      econstructor.
      eauto.
      eapply Forall_forall.
      intuition.
    }
    {
      unfold disjoint_ptrs_ls, no_clash_ls, no_clash in *.
      econstructor.
      eauto.
      eapply Forall_forall.
      intuition.
    }
    {
      unfold disjoint_ptrs_ls, no_clash_ls, no_clash in *; simpl in *.
      econstructor; simpl in *.
      eauto.
      eapply (IHpairs (w1, ADT a1)); eauto.
    }      
    {
      unfold disjoint_ptrs_ls, no_clash_ls, no_clash in *; simpl in *.
      intuition.
      econstructor; simpl in *.
      eauto.
      eapply (IHpairs (w1, ADT a1)); eauto.
    }      
  Qed.

  Lemma disjoint_ptrs_cons_elim pairs : forall p, disjoint_ptrs (p :: pairs) -> no_clash_ls p pairs /\ disjoint_ptrs pairs.
    intros p H.
    eapply disjoint_ptrs_cons_elim' in H.
    Require Import GeneralTactics.
    openhyp.
    split; eauto.
    eapply disjoint_ptrs_ls_no_clash_ls; eauto.
  Qed.

  Lemma disjoint_ptrs_DisjointPtrs ls : disjoint_ptrs ls -> DisjointPtrs ls.
  Proof.
    induction ls; simpl; intros H.
    {
      econstructor.
    }
    eapply disjoint_ptrs_cons_elim in H.
    openhyp.
    econstructor; eauto.
    eapply IHls; eauto.
  Qed.

  Lemma no_clash_ls_not_in_heap pairs : forall w v, no_clash_ls (w, v) pairs -> not_in_heap w v (make_heap' pairs).
  Proof.
    induction pairs; simpl; intros w v H.
    {
      destruct v; simpl.
      eauto.
      intros Hin.
      eapply empty_in_iff in Hin.
      eauto.
    }
    inversion H; subst.
    destruct a as [w' v'].
    destruct v as [? | a]; simpl in *.
    { eauto. }
    unfold store_pair.
    destruct v' as [? | a']; simpl in *.
    {
      eapply IHpairs in H3.
      simpl in *.
      eauto.
    }
    unfold no_clash in H2; simpl in *.
    intros Hin.
    eapply add_in_iff in Hin.
    destruct Hin as [Hin | Hin].
    {
      subst; intuition.
    }
    eapply IHpairs in H3.
    simpl in *.
    intuition.
  Qed.

  Arguments store_pair {_} _ _.

  Lemma fold_left_store_pair_comm pairs : forall w v h1 h2, no_clash_ls (w, v) pairs -> h2 == store_pair h1 (w, v) -> fold_left store_pair pairs h2 == store_pair (fold_left store_pair pairs h1) (w, v).
  Proof.
    induction pairs; simpl; intros w v h1 h2 Hnin Hh.
    rewrite Hh; reflexivity.
    destruct a as [w' v'].
    inversion Hnin; subst.
    eapply IHpairs; eauto.
    rewrite Hh.
    rewrite store_pair_comm by eauto.
    reflexivity.
  Qed.

  Lemma make_heap_make_heap' pairs : disjoint_ptrs pairs -> make_heap pairs == make_heap' pairs.
  Proof.
    induction pairs; simpl; intros Hdisj.
    reflexivity.
    unfold make_heap in *.
    simpl.
    destruct a as [w v].
    eapply disjoint_ptrs_cons_elim in Hdisj.
    destruct Hdisj as [Hnin Hdisj].
    rewrite <- IHpairs by eauto.
    eapply fold_left_store_pair_comm; eauto.
    reflexivity.
  Qed.

End ADTValue.