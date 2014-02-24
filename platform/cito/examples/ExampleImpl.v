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

Definition m := bimport [[ "sys"!"abort" @ [abortS], "SimpleCell"!"new" @ [newS],
                           "SimpleCell"!"delete" @ [deleteS] ]]
  fmodule "ADT" {{
    ffunction "SimpleCell_new" reserving 8 [SimpleCell_newSpec] := "SimpleCell"!"new"
    with ffunction "SimpleCell_delete" reserving 6 [SimpleCell_deleteSpec] := "SimpleCell"!"delete"
  }}.

Theorem ok : moduleOk m.
  vcgen.

  do_abort (@nil string).
  do_abort (@nil string).
  do_abort (@nil string).

  do_delegate1 (@nil string) hints.
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
  2: returnScalar.
  simpl.
  make_toArray ("c" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply is_heap_eat ] ].
  do_delegate2 ("c" :: nil).
Qed.
