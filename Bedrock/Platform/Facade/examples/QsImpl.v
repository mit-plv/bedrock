Set Implicit Arguments.

(* there is a name conflict on tactic 'unfolder' between GeneralTactics and MakeADT *)
Require Import Bedrock.Platform.Cito.GeneralTactics.

Require Import Bedrock.Platform.Facade.examples.QsADTs.
Import Adt.
Require Import Bedrock.Platform.Cito.WordMap.
Require Import Bedrock.Platform.Cito.RepInv Bedrock.Platform.Cito.MakeADT.

Require Import Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Facade.examples.ArrayTupleF Bedrock.Platform.Facade.examples.TupleListF Bedrock.Platform.Facade.examples.Tuples0F Bedrock.Platform.Facade.examples.Tuples1F.
Require Import Bedrock.Platform.Facade.examples.QsRepInv.

Module Import Made := MakeADT.Make(QsADTs.Adt)(Ri).

Import Semantics.

Import LinkMake.StubsMake.StubMake.CompileFuncSpecMake.InvMake.SemanticsMake.
Import LinkMake.StubsMake.StubMake.CompileFuncSpecMake.InvMake2.
Import LinkMake.StubsMake.StubMake.CompileFuncSpecMake.InvMake.

Definition hints : TacPackage.
  prepare (store_pair_inl_fwd, store_pair_inr_fwd)
  (store_pair_inl_bwd, store_pair_inr_bwd).
Defined.

Arguments SCA {ADTValue} _.
Arguments ADT {ADTValue} _.

Require Bedrock.Platform.Cito.AxSpec.
Import AxSpec.ConformTactic.

Definition m0 := bimport [[ "sys"!"abort" @ [abortS],

                            "ArrayTuple"!"new" @ [ArrayTupleF.newS],
                            "ArrayTuple"!"delete" @ [ArrayTupleF.deleteS],
                            "ArrayTuple"!"copy" @ [ArrayTupleF.copyS],
                            "ArrayTuple"!"get" @ [ArrayTupleF.getS],
                            "ArrayTuple"!"set" @ [ArrayTupleF.setS] ]]
  fmodule "ADT" {{
    ffunction "Tuple_new" reserving 7 [Tuple_new] := "ArrayTuple"!"new"
    with ffunction "Tuple_delete" reserving 6 [Tuple_delete] := "ArrayTuple"!"delete"
    with ffunction "Tuple_copy" reserving 11 [Tuple_copy] := "ArrayTuple"!"copy"
    with ffunction "Tuple_get" reserving 0 [Tuple_get] := "ArrayTuple"!"get"
    with ffunction "Tuple_set" reserving 0 [Tuple_set] := "ArrayTuple"!"set"
  }}.

Ltac peel := repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.

Lemma is_heap_eat : forall w v,
  is_heap heap_empty
  ===> is_heap (WordMap.remove w (heap_upd heap_empty w v)).
Proof.
  intros; apply is_heap_Equal.
  apply Properties.F.Equal_mapsto_iff; intuition.
  apply Properties.F.empty_mapsto_iff in H; tauto.
  apply Properties.F.remove_mapsto_iff in H; intuition.
  apply Properties.F.add_mapsto_iff in H1; intuition.
Qed.

Lemma get_rval : forall specs st P Q (R : Prop) S T Z,
  (R -> interp specs (![P * Q * S * T] st ---> Z)%PropX)
  -> interp specs (![P * ((Q * [|R|]) * S) * T] st ---> Z)%PropX.
Proof.
  intros.
  apply Imply_trans with (![[|R|] * (P * Q * S * T)]st)%PropX.
  assert (P * (Q * [|R|] * S) * T ===> [|R|] * (P * Q * S * T)).
  sepLemma.
  rewrite sepFormula_eq.
  apply H0.
  apply Imply_trans with ([|R|] /\ ![P * Q * S * T]st)%PropX.
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

Lemma get_rval' : forall specs st P (Q : Prop) R S Z,
  (Q -> interp specs (![P * R * S ] st ---> Z)%PropX)
  -> interp specs (![P * ([|Q|] * R) * S] st ---> Z)%PropX.
Proof.
  intros.
  apply Imply_trans with (![[|Q|] * (P * R * S)]st)%PropX.
  assert (P * ([|Q|] * R) * S ===> [|Q|] * (P * R * S)).
  sepLemma.
  rewrite sepFormula_eq.
  apply H0.
  apply Imply_trans with ([|Q|] /\ ![P * R * S]st)%PropX.
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

Lemma contra2 : forall len len',
  (natToW len < $2 -> False)
  -> len' < natToW 2
  -> len = wordToNat len'
  -> False.
Proof.
  intros; subst.
  pre_nomega.
  unfold natToW in H.
  rewrite natToWord_wordToNat in H.
  change (wordToNat (natToW 2)) with 2 in *.
  change (wordToNat (natToWord 32 2)) with 2 in *.
  omega.
Qed.

Hint Immediate contra2.

Require Import Bedrock.Platform.Cito.SemanticsFacts5.
Require Import Bedrock.Platform.Cito.LayoutHintsUtil.

Lemma readd_Tuple : forall c rv rv',
  tuple rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (Tuple rv') (heap_upd heap_empty c (Tuple rv))).
Proof.
  intros.
  unfold is_heap at 2.
  assert (List.In (c, Tuple rv') (heap_elements (WordMap.add c (Tuple rv') (heap_upd heap_empty c (Tuple rv))))).
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


Lemma get_rval'' : forall specs st P (Q : Prop) R S T Z,
  (Q -> interp specs (![P * R * S * T ] st ---> Z)%PropX)
  -> interp specs (![P * (([|Q|] * R) * S) * T] st ---> Z)%PropX.
Proof.
  intros.
  apply Imply_trans with (![[|Q|] * (P * R * S * T)]st)%PropX.
  assert (P * (([|Q|] * R) * S) * T===> [|Q|] * (P * R * S * T)).
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


Theorem ok0 : moduleOk m0.
Proof.
  vcgen.


  (* ArrayTuple *)

  (* new *)

  do_abort ("len" :: nil).
  do_abort ("len" :: nil).
  do_abort ("len" :: nil).

  do_delegate1 ("len" :: nil) hints.
  descend; step auto_ext.
  peel.
  apply get_rval; intro.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("len" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  do_delegate2 ("len" :: nil).

  (* delete *)

  do_abort ("self" :: "len" :: nil).
  do_abort ("self" :: "len" :: nil).
  do_abort ("self" :: "len" :: nil).

  do_delegate1 ("self" :: "len" :: nil) hints.
  descend; step auto_ext.
  peel.
  apply get_rval'; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "len" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply is_heap_eat ] ].
  do_delegate2 ("self" :: "len" :: nil).

  (* copy *)

  do_abort ("self" :: "len" :: nil).
  do_abort ("self" :: "len" :: nil).
  do_abort ("self" :: "len" :: nil).
  do_delegate1 ("self" :: "len" :: nil) hints.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("self" :: "len" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuple ] ].
  do_delegate2 ("self" :: "len" :: nil).

  (* get *)

  do_abort ("self" :: "pos" :: nil).
  do_abort ("self" :: "pos" :: nil).
  do_abort ("self" :: "pos" :: nil).

  do_delegate1 ("self" :: "pos" :: nil) hints.
  descend; step auto_ext.
  peel.
  apply get_rval''; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "pos" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuple ] ].
  do_delegate2 ("self" :: "pos" :: nil).

  (* set *)

  do_abort ("self" :: "pos" :: "val" :: nil).
  do_abort ("self" :: "pos" :: "val" :: nil).
  do_abort ("self" :: "pos" :: "val" :: nil).

  do_delegate1 ("self" :: "pos" :: "val" :: nil) hints.
  descend; step auto_ext.
  peel.
  apply get_rval''; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "pos" :: "val" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuple ] ].
  do_delegate2 ("self" :: "pos" :: "val" :: nil).


  Grab Existential Variables.
  exact 0.
  exact 0.
  exact 0.
Qed.
