Set Implicit Arguments.

Require Import FMapFacts3.

Require Import List.

Require LabelMap.
Module BLM := LabelMap.LabelMap.
Module BLK := LabelMap.LabelKey.
Require Import Equalities.
Module BLK_as_UDT := Make_UDT BLK.
Module Import BLMFU3 := FMapFacts3.UWFacts_fun BLK_as_UDT BLM.
Module Import BLMFU := UWFacts.
Module Import BLMF := WFacts.

Require Import Label.
Module LM := LabelMap.
Module Label_as_UDT := Key'.
Module Import LMFU3 := FMapFacts3.UWFacts_fun Label_as_UDT LM.
Module Import LMFU := UWFacts.
Module Import LMF := WFacts.
Require Import ListFacts2.
Module LF := ListFacts2.
Module Import LFL := Make Label_as_UDT.

Import LM.
Import P.
Import F.

Require Import ConvertLabel.

Definition to_bl_pair elt (p : label * elt) := (fst p : Labels.label, snd p).

Definition to_blm elt m := BLMF.to_map (List.map (@to_bl_pair _) (@elements elt m)).

Module Notations.
  Notation "m1 === m2" := (BLM.Equal m1 (to_blm m2)) (at level 70) : clm_scope.
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
  Require Import ListFacts2.

  Set Printing Coercions.

  Lemma NoDupKey_to_bl_pair_elements : forall elt m, BLMF.NoDupKey (List.map (@to_bl_pair _) (@elements elt m)).
    intros.
    eapply BLMFU.NoDupKey_NoDup_fst.
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

  Lemma to_blm_spec : forall elt (k : label) m, @BLM.find elt (k : Labels.label) (to_blm m) = find k m.
    unfold to_blm, BLMF.to_map.
    intros.
    eapply option_univalence; split; intros.
    eapply BLM.find_2 in H.
    eapply BLMF.P.of_list_1 in H.
    eapply BLMFU.InA_eqke_In in H.
    eapply in_map_iff in H.
    openhyp.
    destruct x; simpl in *.
    unfold to_bl_pair, to_bedrock_label in *; simpl in *.
    destruct l; simpl in *.
    destruct k; simpl in *.
    injection H; intros; subst.
    eapply InA_eqke_In in H0.
    eapply elements_mapsto_iff in H0.
    eapply find_1; eauto.
    eapply NoDupKey_to_bl_pair_elements.

    eapply BLM.find_1.
    eapply BLMF.P.of_list_1.
    eapply NoDupKey_to_bl_pair_elements.
    eapply BLMFU.InA_eqke_In.
    eapply in_map_iff.
    exists (k, v); split; eauto.
    eapply InA_eqke_In.
    eapply elements_1.
    eapply find_2.
    eauto.
  Qed.

  Lemma to_blm_no_local : forall elt s1 s2 m, @BLM.find elt (s1, Labels.Local s2) (to_blm m) = None.
    unfold to_blm, BLMF.to_map.
    intros.
    eapply BLMFU3.not_in_find.
    intuition.
    eapply BLMFU3.In_MapsTo in H.
    openhyp.
    eapply BLMF.P.of_list_1 in H.
    eapply BLMFU.InA_eqke_In in H.
    eapply in_map_iff in H.
    openhyp.
    unfold to_bl_pair, to_bedrock_label in *; simpl in *.
    discriminate.
    eapply NoDupKey_to_bl_pair_elements.
  Qed.

  Lemma to_blm_local_not_in : forall elt s1 s2 m, ~ @BLM.In elt (s1, Labels.Local s2) (to_blm m).
    intros.
    eapply BLMF.P.F.not_find_in_iff.
    rewrite to_blm_no_local; eauto.
  Qed.

  Lemma to_blm_mapsto_iff : forall elt k (v : elt) m, BLM.MapsTo k v (to_blm m) <-> exists k' : label, MapsTo k' v m /\ k = (k' : Labels.label).
    split; intros.
    destruct k.
    destruct l.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) in * by eauto.
    eapply BLM.find_1 in H.
    rewrite to_blm_spec in H.
    eapply find_2 in H.
    eexists; eauto.
    eapply BLMF.MapsTo_In in H.
    eapply to_blm_local_not_in in H; intuition.
    openhyp.
    subst.
    eapply BLM.find_2.
    rewrite to_blm_spec.
    eapply find_1; eauto.
  Qed.

  Lemma to_blm_Equal : forall elt m1 m2, @BLM.Equal elt (to_blm m1) (to_blm m2) <-> m1 == m2.
    unfold Equal, BLM.Equal.
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
      with signature Equal ==> BLM.Equal as to_blm_Equal_m.
    intros; eapply to_blm_Equal; eauto.
  Qed.

  Lemma to_blm_In : forall elt (k : label) m, @BLM.In elt (k : Labels.label) (to_blm m) <-> In k m.
    split; intros.
    eapply in_find_iff.
    eapply BLMF.P.F.in_find_iff in H.
    rewrite <- to_blm_spec.
    eauto.
    eapply in_find_iff in H.
    eapply BLMF.P.F.in_find_iff.
    rewrite to_blm_spec.
    eauto.
  Qed.

  Lemma to_blm_Compat : forall elt m1 m2, @BLMFU3.Compat elt (to_blm m1) (to_blm m2) <-> Compat m1 m2.
    unfold Compat, BLMFU3.Compat.
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
      with signature (@Compat elt) ==> (@BLMFU3.Compat elt) as to_blm_Compat_m.
    intros; eapply to_blm_Compat; eauto.
  Qed.

  Lemma to_blm_empty : forall elt, BLM.empty elt === {}.
    unfold Equal, BLM.Equal.
    intuition.
  Qed.

  Require Import GeneralTactics2.

  Lemma to_blm_update : forall elt m1 m2, @BLM.Equal elt (to_blm (update m1 m2)) (BLMF.P.update (to_blm m1) (to_blm m2)).
    unfold Equal, BLM.Equal.
    intros.
    destruct y.
    destruct l; simpl.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) by eauto.
    repeat erewrite to_blm_spec.
    destruct (In_dec m2 (s, s0)).
    rewrite update_o_2 by eauto.
    rewrite BLMFU3.update_o_2.
    repeat erewrite to_blm_spec.
    eauto.
    eapply to_blm_In; eauto.
    rewrite update_o_1 by eauto.
    rewrite BLMFU3.update_o_1.
    repeat erewrite to_blm_spec.
    eauto.
    not_not.
    eapply to_blm_In; eauto.
    repeat rewrite to_blm_no_local.
    symmetry.
    eapply BLMFU3.not_in_find.
    intuition.
    eapply BLMF.P.update_in_iff in H.
    openhyp.
    eapply to_blm_local_not_in; eauto.
    eapply to_blm_local_not_in; eauto.
  Qed.

  Lemma to_blm_diff : forall elt m1 m2, @BLM.Equal elt (to_blm (diff m1 m2)) (BLMF.P.diff (to_blm m1) (to_blm m2)).
    unfold Equal, BLM.Equal.
    intros.
    destruct y.
    destruct l; simpl.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) by eauto.
    repeat erewrite to_blm_spec.
    destruct (In_dec m2 (s, s0)).
    rewrite diff_o_none by eauto.
    rewrite BLMFU3.diff_o_none.
    eauto.
    eapply to_blm_In; eauto.
    rewrite diff_o by eauto.
    rewrite BLMFU3.diff_o.
    repeat erewrite to_blm_spec.
    eauto.
    not_not.
    eapply to_blm_In; eauto.
    repeat rewrite to_blm_no_local.
    symmetry.
    eapply BLMFU3.not_in_find.
    intuition.
    eapply BLMF.P.diff_in_iff in H.
    openhyp.
    eapply to_blm_local_not_in; eauto.
  Qed.

  Lemma to_blm_add : forall elt (k : label) v m, @BLM.Equal elt (to_blm (add k v m)) (BLM.add (k : Labels.label) v (to_blm m)).
    unfold Equal, BLM.Equal.
    intros.
    destruct y.
    destruct l; simpl.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) by eauto.
    repeat erewrite to_blm_spec.
    rewrite add_o.
    destruct (eq_dec k (s, s0)).
    subst.
    symmetry.
    rewrite BLMF.P.F.add_eq_o; eauto.
    rewrite BLMF.P.F.add_neq_o.
    repeat erewrite to_blm_spec; eauto.
    not_not.
    unfold to_bedrock_label in *.
    destruct k; simpl in *.
    injection H; intros; subst.
    eauto.
    repeat rewrite to_blm_no_local.
    symmetry.
    eapply BLMFU3.not_in_find.
    intuition.
    eapply BLMF.P.F.add_in_iff in H.
    unfold to_bedrock_label in *.
    destruct k; simpl in *.
    openhyp.
    discriminate.
    eapply to_blm_local_not_in; eauto.
  Qed.

End TopSection.