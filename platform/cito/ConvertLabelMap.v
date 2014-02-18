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

  Lemma to_blm_empty : forall elt, BLM.empty elt === {}.
    admit.
  Qed.

  Lemma to_blm_Equal : forall elt m1 m2, @BLM.Equal elt (to_blm m1) (to_blm m2) <-> m1 == m2.
    admit.
  Qed.

  Require Import Setoid.

  Add Parametric Morphism elt : (@to_blm elt)
      with signature Equal ==> BLM.Equal as to_blm_Equal_m.
    intros; eapply to_blm_Equal; eauto.
  Qed.

  Lemma to_blm_Compat : forall elt m1 m2, @BLMFU3.Compat elt (to_blm m1) (to_blm m2) <-> Compat m1 m2.
    admit.
  Qed.

  Add Parametric Morphism elt : (@to_blm elt)
      with signature (@Compat elt) ==> (@BLMFU3.Compat elt) as to_blm_Compat_m.
    intros; eapply to_blm_Compat; eauto.
  Qed.

  Lemma to_blm_update : forall elt m1 m2, @BLM.Equal elt (to_blm (update m1 m2)) (BLMF.P.update (to_blm m1) (to_blm m2)).
    admit.
  Qed.

  Lemma to_blm_diff : forall elt m1 m2, @BLM.Equal elt (to_blm (diff m1 m2)) (BLMF.P.diff (to_blm m1) (to_blm m2)).
    admit.
  Qed.

  Lemma to_blm_spec : forall elt (k : label) m, @BLM.find elt (k : Labels.label) (to_blm m) = find k m.
    admit.
  Qed.

  Lemma to_blm_no_local : forall elt s1 s2 m, @BLM.find elt (s1, Labels.Local s2) (to_blm m) = None.
    admit.
  Qed.

  Lemma to_blm_add : forall elt (k : label) v m, @BLM.Equal elt (to_blm (add k v m)) (BLM.add (k : Labels.label) v (to_blm m)).
    admit.
  Qed.

End TopSection.