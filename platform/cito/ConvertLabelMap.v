Set Implicit Arguments.

Require Import List.

Require Import Labels.
Require Import LabelMap.
Module LM := LabelMap.
Require LabelMapFacts.
Module LMF := LabelMapFacts.
Require Import GLabel.
Require Import GLabelMap.
Import GLabelMap.
Require Import GLabelMapFacts.

Require Import ConvertLabel.

Definition to_bl_pair elt (p : glabel * elt) := (fst p : label, snd p).

Definition to_blm elt m := LMF.of_list (List.map (@to_bl_pair _) (@elements elt m)).

Module Notations.
  Notation "m1 === m2" := (LM.Equal m1 (to_blm m2)) (at level 70) : clm_scope.
End Notations.

Section TopSection.

  Import Notations.
  Open Scope clm_scope.
  Import ListNotations.
  Import FMapNotations.
  Open Scope fmap.

  Require Import Setoid.
  Require Import SetoidList.
  Require Import GeneralTactics.
  Require Import ListFacts1.

  Set Printing Coercions.

  Lemma NoDupKey_to_bl_pair_elements : forall elt m, LMF.NoDupKey (List.map (@to_bl_pair _) (@elements elt m)).
    intros.
    eapply LMF.NoDupKey_NoDup_fst.
    rewrite map_map.
    unfold to_bl_pair; simpl in *.
    rewrite <- map_map.
    eapply Injection_NoDup.
    unfold to_bedrock_label.
    unfold IsInjection; intuition.
    destruct x; destruct y; simpl in *.
    injection H0; intros; subst.
    intuition.
    eapply NoDupKey_NoDup_fst.
    eapply elements_3w.
  Qed.

  Lemma to_blm_spec : forall elt (k : glabel) m, @LM.find elt (k : label) (to_blm m) = find k m.
    unfold to_blm, LMF.to_map.
    intros.
    eapply option_univalence; split; intros.
    eapply LM.find_2 in H.
    eapply LMF.of_list_1 in H.
    eapply LMF.InA_eqke_In in H.
    eapply in_map_iff in H.
    openhyp.
    destruct x; simpl in *.
    unfold to_bl_pair, to_bedrock_label in *; simpl in *.
    destruct g; simpl in *.
    destruct k; simpl in *.
    injection H; intros; subst.
    eapply InA_eqke_In in H0.
    eapply elements_mapsto_iff in H0.
    eapply find_1; eauto.
    eapply NoDupKey_to_bl_pair_elements.

    eapply LM.find_1.
    eapply LMF.of_list_1.
    eapply NoDupKey_to_bl_pair_elements.
    eapply LMF.InA_eqke_In.
    eapply in_map_iff.
    exists (k, v); split; eauto.
    eapply InA_eqke_In.
    eapply elements_1.
    eapply find_2.
    eauto.
  Qed.

  Lemma to_blm_no_local : forall elt s1 s2 m, @LM.find elt (s1, Local s2) (to_blm m) = None.
    unfold to_blm, LMF.to_map.
    intros.
    eapply LMF.not_in_find.
    intuition.
    eapply LMF.In_MapsTo in H.
    openhyp.
    eapply LMF.of_list_1 in H.
    eapply LMF.InA_eqke_In in H.
    eapply in_map_iff in H.
    openhyp.
    unfold to_bl_pair, to_bedrock_label in *; simpl in *.
    discriminate.
    eapply NoDupKey_to_bl_pair_elements.
  Qed.

  Lemma to_blm_local_not_in : forall elt s1 s2 m, ~ @LM.In elt (s1, Labels.Local s2) (to_blm m).
    intros.
    eapply LMF.not_find_in_iff.
    rewrite to_blm_no_local; eauto.
  Qed.

  Lemma to_blm_mapsto_iff : forall elt k (v : elt) m, LM.MapsTo k v (to_blm m) <-> exists k' : glabel, MapsTo k' v m /\ k = (k' : label).
    split; intros.
    destruct k.
    destruct l.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) in * by eauto.
    eapply LM.find_1 in H.
    rewrite to_blm_spec in H.
    eapply find_2 in H.
    eexists; eauto.
    eapply LMF.MapsTo_In in H.
    eapply to_blm_local_not_in in H; intuition.
    openhyp.
    subst.
    eapply LM.find_2.
    rewrite to_blm_spec.
    eapply find_1; eauto.
  Qed.

  Lemma to_blm_Equal : forall elt m1 m2, @LM.Equal elt (to_blm m1) (to_blm m2) <-> m1 == m2.
    unfold Equal, LM.Equal.
    intuition.
    repeat erewrite <- to_blm_spec.
    eauto.
    destruct y.
    destruct l.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) by eauto.
    repeat erewrite to_blm_spec.
    eauto.
    repeat rewrite to_blm_no_local.
    eauto.
  Qed.

  Add Parametric Morphism elt : (@to_blm elt)
      with signature Equal ==> LM.Equal as to_blm_Equal_m.
    intros; eapply to_blm_Equal; eauto.
  Qed.

  Lemma to_blm_In : forall elt (k : glabel) m, @LM.In elt (k : label) (to_blm m) <-> In k m.
    split; intros.
    eapply in_find_iff.
    eapply LMF.in_find_iff in H.
    rewrite <- to_blm_spec.
    eauto.
    eapply in_find_iff in H.
    eapply LMF.in_find_iff.
    rewrite to_blm_spec.
    eauto.
  Qed.

  Lemma to_blm_Compat : forall elt m1 m2, @LMF.Compat elt (to_blm m1) (to_blm m2) <-> Compat m1 m2.
    unfold Compat, LMF.Compat.
    intuition.
    repeat erewrite <- to_blm_spec.
    eapply H.
    eapply to_blm_In; eauto.
    eapply to_blm_In; eauto.
    destruct k.
    destruct l.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) by eauto.
    repeat erewrite to_blm_spec.
    eapply H.
    eapply to_blm_In; eauto.
    eapply to_blm_In; eauto.
    repeat rewrite to_blm_no_local.
    eauto.
  Qed.

  Add Parametric Morphism elt : (@to_blm elt)
      with signature (@Compat elt) ==> (@LMF.Compat elt) as to_blm_Compat_m.
    intros; eapply to_blm_Compat; eauto.
  Qed.

  Lemma to_blm_empty : forall elt, LM.empty elt === {}.
    unfold Equal, LM.Equal.
    intuition.
  Qed.

  Require Import GeneralTactics2.

  Lemma to_blm_update : forall elt m1 m2, @LM.Equal elt (to_blm (update m1 m2)) (LMF.update (to_blm m1) (to_blm m2)).
    unfold Equal, LM.Equal.
    intros.
    destruct y.
    destruct l; simpl.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) by eauto.
    repeat erewrite to_blm_spec.
    destruct (In_dec m2 (s, s0)).
    rewrite update_o_2 by eauto.
    rewrite LMF.update_o_2.
    repeat erewrite to_blm_spec.
    eauto.
    eapply to_blm_In; eauto.
    rewrite update_o_1 by eauto.
    rewrite LMF.update_o_1.
    repeat erewrite to_blm_spec.
    eauto.
    not_not.
    eapply to_blm_In; eauto.
    repeat rewrite to_blm_no_local.
    symmetry.
    eapply LMF.not_in_find.
    intuition.
    eapply LMF.update_in_iff in H.
    openhyp.
    eapply to_blm_local_not_in; eauto.
    eapply to_blm_local_not_in; eauto.
  Qed.

  Lemma to_blm_diff : forall elt m1 m2, @LM.Equal elt (to_blm (diff m1 m2)) (LMF.diff (to_blm m1) (to_blm m2)).
    unfold Equal, LM.Equal.
    intros.
    destruct y.
    destruct l; simpl.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) by eauto.
    repeat erewrite to_blm_spec.
    destruct (In_dec m2 (s, s0)).
    rewrite diff_o_none by eauto.
    rewrite LMF.diff_o_none.
    eauto.
    eapply to_blm_In; eauto.
    rewrite diff_o by eauto.
    rewrite LMF.diff_o.
    repeat erewrite to_blm_spec.
    eauto.
    not_not.
    eapply to_blm_In; eauto.
    repeat rewrite to_blm_no_local.
    symmetry.
    eapply LMF.not_in_find.
    intuition.
    eapply LMF.diff_in_iff in H.
    openhyp.
    eapply to_blm_local_not_in; eauto.
  Qed.

  Lemma to_blm_add : forall elt (k : glabel) v m, @LM.Equal elt (to_blm (add k v m)) (LM.add (k : label) v (to_blm m)).
    unfold Equal, LM.Equal.
    intros.
    destruct y.
    destruct l; simpl.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) by eauto.
    repeat erewrite to_blm_spec.
    rewrite add_o.
    destruct (eq_dec k (s, s0)).
    subst.
    symmetry.
    rewrite LMF.add_eq_o; eauto.
    rewrite LMF.add_neq_o.
    repeat erewrite to_blm_spec; eauto.
    not_not.
    unfold to_bedrock_label in *.
    destruct k; simpl in *.
    injection H; intros; subst.
    eauto.
    repeat rewrite to_blm_no_local.
    symmetry.
    eapply LMF.not_in_find.
    intuition.
    eapply LMF.add_in_iff in H.
    unfold to_bedrock_label in *.
    destruct k; simpl in *.
    openhyp.
    discriminate.
    eapply to_blm_local_not_in; eauto.
  Qed.

End TopSection.