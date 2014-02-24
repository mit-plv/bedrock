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

Definition SimpleCell_newSpec : ForeignFuncSpec ADTValue := 
  {|
    PreCond := fun args => args = nil;
    PostCond := fun args ret => args = nil /\ ret = inr (Cell 0)
  |}.

Definition m := bimport [[ "sys"!"abort" @ [abortS], "SimpleCell"!"new" @ [newS] ]]
  fmodule "ADT" {{
    ffunction "SimpleCell_new" reserving 8 [SimpleCell_newSpec] := "SimpleCell"!"new"
  }}.

Theorem ok : moduleOk m.
  wrapper (@nil string) ltac:(simpl; intuition; instantiate (1 := nil); auto).
Qed.
