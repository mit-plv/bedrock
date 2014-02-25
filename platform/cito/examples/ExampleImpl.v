Set Implicit Arguments.

Require Import ExampleADT.
Import ExampleADT.ExampleADT.
Require Import RepInv MakeADT.

Require Import AutoSep.
Require Import WordMap.

Require Import Cell SimpleCell.

Parameter is_fset : W -> WordSet.t -> HProp.
Parameter is_fmap : W -> WordMap.t W -> HProp.

Definition rep_inv p adtvalue : HProp :=
  match adtvalue with
    | FSet s => is_fset p s
    | FMap m => is_fmap p m
    | Cell v => cell v p
  end.

Module ExampleRepInv <: RepInv ExampleADT.

  Definition RepInv := W -> ADTValue -> HProp.

  Definition rep_inv := rep_inv.

  Lemma rep_inv_ptr : forall p a, rep_inv p a ===> p =?> 1 * any.
    destruct a; simpl.
    admit.
    admit.
    eapply Himp_trans; [ apply cell_fwd | sepLemma ]; apply any_easy.
  Qed.

End ExampleRepInv.

Module Import Made := MakeADT.Make(ExampleADT)(ExampleRepInv).

Import Semantics.

Import LinkMake.StubsMake.StubMake.CompileFuncSpecMake.InvMake.SemanticsMake.
Import LinkMake.StubsMake.StubMake.CompileFuncSpecMake.InvMake2.
Import LinkMake.StubsMake.StubMake.CompileFuncSpecMake.InvMake.

Lemma is_heap_eat : forall w v,
  is_heap heap_empty
  ===> is_heap (WordMap.remove w (heap_upd heap_empty w v)).
  intros; apply is_heap_Equal.
  apply Properties.F.Equal_mapsto_iff; intuition.
  apply Properties.F.empty_mapsto_iff in H; tauto.
  apply Properties.F.remove_mapsto_iff in H; intuition.
  apply Properties.F.add_mapsto_iff in H1; intuition.
Qed.

Definition hints : TacPackage.
  prepare (store_pair_inl_fwd, store_pair_inr_fwd)
  (store_pair_inl_bwd, store_pair_inr_bwd).
Defined.

Definition SimpleCell_newSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => args = nil;
    PostCond := fun args ret => args = nil /\ ret = inr (Cell 0)
  |}.

Definition SimpleCell_deleteSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => exists n, args = inr (Cell n) :: nil;
    PostCond := fun args _ => exists n, args = (inr (Cell n), None) :: nil
  |}.

Definition SimpleCell_readSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => exists n, args = inr (Cell n) :: nil;
    PostCond := fun args ret => exists n, ret = inl n /\ args = (inr (Cell n), Some (Cell n)) :: nil
  |}.

Lemma readd : forall c rv,
  cell rv c * is_heap heap_empty
  ===> is_heap (WordMap.add c (Cell rv) (heap_upd heap_empty c (Cell rv))).
  intros.
  unfold is_heap at 2.
  assert (List.In (c, Cell rv) (heap_elements (WordMap.add c (Cell rv) (heap_upd heap_empty c (Cell rv))))).
  Import LayoutHintsUtil.
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H; intuition idtac.
  eapply Himp_trans; [ | apply H0 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H2 in H1; intuition.
  apply In_InA' in H4.
  apply WordMap.elements_2 in H4.
  apply Properties.F.add_mapsto_iff in H4; intuition.
  apply Properties.F.add_mapsto_iff in H5; intuition.
  apply Properties.F.empty_mapsto_iff in H6; tauto.
Qed.

Lemma get_rval : forall specs st P (Q : Prop) R S T Z,
  (Q -> interp specs (![P * R * S * T] st ---> Z)%PropX)
  -> interp specs (![P * (([|Q|] * R) * S) * T] st ---> Z)%PropX.
  intros.
  apply Imply_trans with (![[|Q|] * (P * R * S * T)]st)%PropX.
  assert (P * ([|Q|] * R * S) * T ===> [|Q|] * (P * R * S * T)).
  sepLemma.
  rewrite sepFormula_eq.
  apply H0.
  apply Imply_trans with ([|Q|] /\ ![P * R * S * T]st)%PropX.
  rewrite sepFormula_eq.
  do 2 (apply existsL; intro).
  apply andL; apply injL; intro.
  apply andL.
  apply andL.
  apply injL; intro.
  apply injL; intro.
  apply split_semp in H0; auto; subst.
  apply andR.
  apply injR; auto.
  apply Imply_refl.
  apply andL.
  apply injL; auto.
Qed.

Definition m := bimport [[ "sys"!"abort" @ [abortS], "SimpleCell"!"new" @ [newS],
                           "SimpleCell"!"delete" @ [deleteS], "SimpleCell"!"read" @ [readS] ]]
  fmodule "ADT" {{
    ffunction "SimpleCell_new" reserving 8 [SimpleCell_newSpec] := "SimpleCell"!"new"
    with ffunction "SimpleCell_delete" reserving 6 [SimpleCell_deleteSpec] := "SimpleCell"!"delete"
    with ffunction "SimpleCell_read" reserving 0 [SimpleCell_readSpec] := "SimpleCell"!"read"
  }}.

Theorem ok : moduleOk m.
  vcgen.

  do_abort (@nil string).
  do_abort (@nil string).
  do_abort (@nil string).

  do_delegate1 (@nil string) hints.
  do 2 (descend; step auto_ext).
  2: returnScalar.
  simpl.
  make_toArray (@nil string).
  step auto_ext.
  etransitivity; [ | apply himp_star_frame; [ apply (@is_state_in x4) | reflexivity ] ].
  unfolder.
  do_delegate2 (@nil string).

  do_abort ("c" :: nil).
  do_abort ("c" :: nil).
  do_abort ("c" :: nil).

  do_delegate1 ("c" :: nil) hints.
  do 2 (descend; step auto_ext).
  2: returnScalar.
  simpl.
  make_toArray ("c" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply is_heap_eat ] ].
  do_delegate2 ("c" :: nil).

  do_abort ("c" :: nil).
  do_abort ("c" :: nil).
  do_abort ("c" :: nil).

  do_delegate1 ("c" :: nil) hints.
  descend; step auto_ext.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval; intro; subst.
  step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("c" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd ] ].
  do_delegate2 ("c" :: nil).

  Grab Existential Variables.
  exact 0.
Qed.
