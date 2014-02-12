Set Implicit Arguments.

Require Import AutoSep.
Require Import StructuredModule.

Definition importsMap' (imports : list import) base :=
  List.fold_left 
    (fun m p => 
       let '(modl, f, pre) := p in
       LabelMap.LabelMap.add (modl, Global f) pre m) imports base.

Require Import FMapFacts1.
Module Import BLMF := WFacts_fun LabelKey LabelMap.
Require Import Label.
Module Import LMF := WFacts_fun Key' LabelMap.
Module Import LMFU := UWFacts_fun Key' LabelMap.
Require Import ConvertLabel.

Lemma importsMap_spec' : 
  forall imps2 imps1 base, 
    NoDupKey (imps1 ++ imps2) -> 
    (forall (k : label), LabelMap.LabelMap.find (k : Labels.label) base = find_list k imps1) ->
    forall (k : label), LabelMap.LabelMap.find (k : Labels.label) (importsMap' imps2 base) = find_list k (imps1 ++ imps2).
  induction imps2; simpl.
  intros.
  rewrite app_nil_r.
  eauto.
  intros.
  rewrite <- DepList.pf_list_simpl.
  eapply IHimps2.
  rewrite DepList.pf_list_simpl.
  eauto.
  destruct a; simpl.
  destruct k0; simpl.
  intros.
  destruct (LabelMap.LabelKey.eq_dec (k0 : Labels.label) (s, Global s0)).
  unfold LabelKey.eq in *.
  erewrite LabelMap.LabelMap.find_1.
  Focus 2.
  eapply LabelMap.LabelMap.add_1.
  eauto.
  destruct k0.
  injection e; intros; subst.
  erewrite In_find_list_Some_left.
  eauto.
  rewrite <- DepList.pf_list_simpl in H.
  eapply NoDupKey_unapp1.
  eauto.
  eapply InA_eq_key_elt_List_In; intuition.
  unfold LabelKey.eq in *.
  erewrite BLMF.add_4.
  rewrite H0.
  erewrite find_list_neq.
  eauto.
  eapply NoDupKey_unapp1.
  eauto.
  intuition.
  destruct k0.
  injection H1; intros; subst; intuition.
  eauto.
Qed.

Lemma importsMap_spec : forall imps (k : label), NoDupKey imps -> LabelMap.LabelMap.find (k : Labels.label) (importsMap imps) = find_list k imps.
  intros.
  unfold importsMap.
  erewrite importsMap_spec'.
  erewrite app_nil_l; eauto.
  erewrite app_nil_l; eauto.
  intros.
  unfold find_list.
  eauto.
Qed.        

Definition fullImports' impsMap modName (functions : list (function modName)) : LabelMap.LabelMap.t assert :=
  List.fold_left 
    (fun m p => 
       let '(f, pre, _) := p in
       LabelMap.LabelMap.add (modName, Global f) pre m) functions impsMap.

Definition func_to_import mn (f : function mn) : import:= ((mn, fst (fst f)), snd (fst f)).

Lemma fullImports_spec' : 
  forall mn (fns : list (function mn)) imps impsMap, 
    let fns' := map (@func_to_import _) fns in
    let whole := imps ++ fns' in
    NoDupKey whole ->
    (forall (k : label), LabelMap.LabelMap.find (k : Labels.label) impsMap = find_list k imps) ->
    forall (k : label), LabelMap.LabelMap.find (k : Labels.label) (fullImports' impsMap fns) = find_list k whole.
Proof.
  unfold fullImports'.
  unfold func_to_import.
  induction fns; simpl; intros.
  rewrite app_nil_r in *.
  eauto.
  rewrite <- DepList.pf_list_simpl.
  eapply IHfns.
  rewrite DepList.pf_list_simpl.
  eauto.
  destruct a; simpl.
  destruct p; simpl.
  intros.
  destruct (LabelMap.LabelKey.eq_dec (k0 : Labels.label) (mn, Global s)).
  unfold LabelKey.eq in *.
  erewrite LabelMap.LabelMap.find_1.
  Focus 2.
  eapply LabelMap.LabelMap.add_1.
  eauto.
  destruct k0.
  injection e; intros; subst.
  erewrite In_find_list_Some_left.
  eauto.
  simpl in *.
  rewrite <- DepList.pf_list_simpl in H.
  eapply NoDupKey_unapp1.
  eauto.
  eapply InA_eq_key_elt_List_In; intuition.
  unfold LabelKey.eq in *.
  erewrite BLMF.add_4.
  rewrite H0.
  erewrite find_list_neq.
  eauto.
  eapply NoDupKey_unapp1.
  eauto.
  intuition.
  destruct k0.
  injection H1; intros; subst; intuition.
  eauto.
Qed.

Lemma fullImports_spec :
  forall (imps : list import) mn (fns : list (function mn)) (k : label),
    let fns' := map (@func_to_import _) fns in
    let whole := imps ++ fns' in
    NoDupKey whole ->
    LabelMap.LabelMap.find (k : Labels.label) (fullImports imps fns) = find_list k whole.
Proof.
  unfold fullImports.
  specialize fullImports_spec'; intros.
  unfold fullImports' in *.
  eapply H; eauto.
  intros.
  eapply importsMap_spec; eauto.
  eapply NoDupKey_unapp1.
  eauto.
Qed.

