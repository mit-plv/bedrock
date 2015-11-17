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
                            "ArrayTuple"!"set" @ [ArrayTupleF.setS],

                            "TupleList"!"new" @ [TupleListF.newS],
                            "TupleList"!"delete" @ [TupleListF.deleteS],
                            "TupleList"!"copy" @ [TupleListF.copyS],
                            "TupleList"!"pop" @ [TupleListF.popS],
                            "TupleList"!"empty" @ [TupleListF.emptyS],
                            "TupleList"!"push" @ [TupleListF.pushS],
                            "TupleList"!"rev" @ [TupleListF.revS],
                            "TupleList"!"length" @ [TupleListF.lengthS],

                            "Tuples0"!"new" @ [Tuples0F.newS],
                            "Tuples0"!"insert" @ [Tuples0F.insertS],
                            "Tuples0"!"enumerate" @ [Tuples0F.enumerateS],

                            "Tuples1"!"new" @ [Tuples1F.newS],
                            "Tuples1"!"insert" @ [Tuples1F.insertS],
                            "Tuples1"!"find" @ [Tuples1F.findS],
                            "Tuples1"!"enumerate" @ [Tuples1F.enumerateS] ]]
  fmodule "ADT" {{
    ffunction "Tuple_new" reserving 7 [Tuple_new] := "ArrayTuple"!"new"
    with ffunction "Tuple_delete" reserving 6 [Tuple_delete] := "ArrayTuple"!"delete"
    with ffunction "Tuple_copy" reserving 11 [Tuple_copy] := "ArrayTuple"!"copy"
    with ffunction "Tuple_get" reserving 0 [Tuple_get] := "ArrayTuple"!"get"
    with ffunction "Tuple_set" reserving 0 [Tuple_set] := "ArrayTuple"!"set"

    with ffunction "List_new" reserving 8 [List_new] := "TupleList"!"new"
    with ffunction "List_delete" reserving 6 [List_delete] := "TupleList"!"delete"
    with ffunction "List_copy" reserving 18 [List_copy] := "TupleList"!"copy"
    with ffunction "List_pop" reserving 8 [List_pop] := "TupleList"!"pop"
    with ffunction "List_empty" reserving 0 [List_empty] := "TupleList"!"empty"
    with ffunction "List_push" reserving 8 [List_push] := "TupleList"!"push"
    with ffunction "List_rev" reserving 2 [List_rev] := "TupleList"!"rev"
    with ffunction "List_length" reserving 1 [List_length] := "TupleList"!"length"

    with ffunction "Tuples0_new" reserving 11 [Tuples0_new] := "Tuples0"!"new"
    with ffunction "Tuples0_insert" reserving 12 [Tuples0_insert] := "Tuples0"!"insert"
    with ffunction "Tuples0_enumerate" reserving 22 [Tuples0_enumerate] := "Tuples0"!"enumerate"

    with ffunction "Tuples1_new" reserving 7 [Tuples1_new] := "Tuples1"!"new"
    with ffunction "Tuples1_insert" reserving 21 [Tuples1_insert] := "Tuples1"!"insert"
    with ffunction "Tuples1_find" reserving 34 [Tuples1_find] := "Tuples1"!"find"
    with ffunction "Tuples1_enumerate" reserving 34 [Tuples1_enumerate] := "Tuples1"!"enumerate"
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

Lemma readd_List : forall c rv rv',
  lseq rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (List rv') (heap_upd heap_empty c (List rv))).
Proof.
  intros.
  unfold is_heap at 2.
  assert (List.In (c, List rv') (heap_elements (WordMap.add c (List rv') (heap_upd heap_empty c (List rv))))).
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

Lemma readd_Tuples0 : forall c len rv rv',
  tuples0 len rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (Tuples0 len rv') (heap_upd heap_empty c (Tuples0 len rv))).
Proof.
  intros.
  unfold is_heap at 2.
  assert (List.In (c, Tuples0 len rv') (heap_elements (WordMap.add c (Tuples0 len rv') (heap_upd heap_empty c (Tuples0 len rv))))).
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

Lemma readd_Tuples1 : forall c len key rv rv',
  tuples1 len key rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (Tuples1 len key rv') (heap_upd heap_empty c (Tuples1 len key rv))).
Proof.
  intros.
  unfold is_heap at 2.
  assert (List.In (c, Tuples1 len key rv') (heap_elements (WordMap.add c (Tuples1 len key rv') (heap_upd heap_empty c (Tuples1 len key rv))))).
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

Lemma readd_List' : forall c rv rv' c' ov,
  c <> c'
  -> lseq rv' c * is_heap heap_empty
  ===> is_heap
      (WordMap.remove c'
         (WordMap.add c (List rv')
            (WordMap.add c' ov
               (WordMap.add c (List rv)
                  heap_empty)))).
Proof.
  intros.
  unfold is_heap at 2.
  match goal with
  | [ |- context[Bags.starL _ ?x] ] => assert (List.In (c, List rv') x)
  end.
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.remove_2; auto.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H0; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H0; intuition idtac.
  eapply Himp_trans; [ | apply H1 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H3 in H2; intuition.
  apply In_InA' in H5.
  apply WordMap.elements_2 in H5.
  apply Properties.F.remove_mapsto_iff in H5; intuition.
  apply Properties.F.add_mapsto_iff in H6; intuition.
  apply Properties.F.add_mapsto_iff in H7; intuition.
  apply Properties.F.add_mapsto_iff in H8; intuition.
  apply Properties.F.empty_mapsto_iff in H9; tauto.
Qed.

Theorem insert_bounded : forall ts idx t,
  TuplesF.minFreshIndex ts idx
  -> TuplesF.insert ts t (TuplesF.insertAt ts idx t).
Proof.
  unfold TuplesF.insert, TuplesF.insertAt, TuplesF.UnConstrFreshIdx.
  destruct 1.
  exists idx.
  intuition.
Qed.

Hint Immediate insert_bounded.

Lemma really_zero : forall (st : state) (r : reg),
  Regs st r = $0
  -> SCA ((let (Regs, _) := st in Regs) r) = @SCAZero ADTValue.
Proof.
  intros.
  unfold SCAZero.
  f_equal.
  auto.
Qed.

Hint Immediate really_zero.

Lemma readd_Tuples0' : forall c rv rv' c' ov len,
  c <> c'
  -> tuples0 len rv' c * is_heap heap_empty
  ===> is_heap
      (WordMap.remove c'
         (WordMap.add c (Tuples0 len rv')
            (WordMap.add c' ov
               (WordMap.add c (Tuples0 len rv)
                  heap_empty)))).
Proof.
  intros.
  unfold is_heap at 2.
  match goal with
  | [ |- context[Bags.starL _ ?x] ] => assert (List.In (c, Tuples0 len rv') x)
  end.
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.remove_2; auto.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H0; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H0; intuition idtac.
  eapply Himp_trans; [ | apply H1 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H3 in H2; intuition.
  apply In_InA' in H5.
  apply WordMap.elements_2 in H5.
  apply Properties.F.remove_mapsto_iff in H5; intuition.
  apply Properties.F.add_mapsto_iff in H6; intuition.
  apply Properties.F.add_mapsto_iff in H7; intuition.
  apply Properties.F.add_mapsto_iff in H8; intuition.
  apply Properties.F.empty_mapsto_iff in H9; tauto.
Qed.

Lemma readd_Tuples1' : forall c rv rv' c' ov len key,
  c <> c'
  -> tuples1 len key rv' c * is_heap heap_empty
  ===> is_heap
      (WordMap.remove c'
         (WordMap.add c (Tuples1 len key rv')
            (WordMap.add c' ov
               (WordMap.add c (Tuples1 len key rv)
                  heap_empty)))).
Proof.
  intros.
  unfold is_heap at 2.
  match goal with
  | [ |- context[Bags.starL _ ?x] ] => assert (List.In (c, Tuples1 len key rv') x)
  end.
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.remove_2; auto.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H0; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H0; intuition idtac.
  eapply Himp_trans; [ | apply H1 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H3 in H2; intuition.
  apply In_InA' in H5.
  apply WordMap.elements_2 in H5.
  apply Properties.F.remove_mapsto_iff in H5; intuition.
  apply Properties.F.add_mapsto_iff in H6; intuition.
  apply Properties.F.add_mapsto_iff in H7; intuition.
  apply Properties.F.add_mapsto_iff in H8; intuition.
  apply Properties.F.empty_mapsto_iff in H9; tauto.
Qed.

Lemma get_rval''' : forall specs st P (Q : Prop) R S Z,
  (Q -> interp specs (![P * R * S ] st ---> Z)%PropX)
  -> interp specs (![((P * [|Q|]) * R) * S] st ---> Z)%PropX.
Proof.
  intros.
  apply Imply_trans with (![[|Q|] * (P * R * S)]st)%PropX.
  assert (((P * [|Q|]) * R) * S ===> [|Q|] * (P * R * S)).
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

Lemma get_rval'''' : forall specs st P (Q : Prop) S Z,
  (Q -> interp specs (![P * S ] st ---> Z)%PropX)
  -> interp specs (![(P * [|Q|]) * S] st ---> Z)%PropX.
Proof.
  intros.
  apply Imply_trans with (![[|Q|] * (P * S)]st)%PropX.
  assert ((P * [|Q|])* S ===> [|Q|] * (P * S)).
  sepLemma.
  rewrite sepFormula_eq.
  apply H0.
  apply Imply_trans with ([|Q|] /\ ![P * S]st)%PropX.
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


  (* TupleList *)

  (* new *)

  do_abort (@nil string).
  do_abort (@nil string).
  do_abort (@nil string).

  do_delegate1 (@nil string) hints.
  do 2 (descend; step auto_ext).
  2: returnAdt.
  simpl.
  make_toArray (@nil string).
  step auto_ext.
  etransitivity; [ | apply himp_star_frame; [ apply (@is_state_in x4) | reflexivity ] ].
  unfolder.
  do_delegate2 (@nil string).

  (* delete *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step auto_ext.
  peel.
  apply get_rval'; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply is_heap_eat ] ].
  do_delegate2 ("self" :: nil).

  (* copy *)

  do_abort ("self" :: "len" :: nil).
  do_abort ("self" :: "len" :: nil).
  do_abort ("self" :: "len" :: nil).

  do_delegate1 ("self" :: "len" :: nil) hints.
  descend; step auto_ext.
  peel.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("self" :: "len" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_List ] ].
  do_delegate2 ("self" :: "len" :: nil).

  (* pop *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  peel.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_List ] ].
  do_delegate2 ("self" :: nil).

  (* empty *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  peel.
  apply get_rval''; intro.
  step auto_ext.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_List ] ].
  do_delegate2 ("self" :: nil).

  (* push *)

  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).

  do_delegate1 ("self" :: "tup" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl.
  descend; step auto_ext.
  descend; step auto_ext.
  simpl.
  peel.
  apply get_rval''; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "tup" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_List' ] ].
  do_delegate2 ("self" :: "tup" :: nil).
  congruence.

  (* rev *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step hints.
  simpl.
  peel.
  apply get_rval''; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_List ] ].
  do_delegate2 ("self" :: nil).

  (* length *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step hints.
  peel.
  apply get_rval''; intro.
  step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_List ] ].
  do_delegate2 ("self" :: nil).


  (* Tuples0 *)

  (* new *)

  do_abort ("len" :: nil).
  do_abort ("len" :: nil).
  do_abort ("len" :: nil).

  do_delegate1 ("len" :: nil) hints.
  descend; step auto_ext.
  peel.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("len" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  do_delegate2 ("len" :: nil).

  (* insert *)

  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).

  do_delegate1 ("self" :: "tup" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl; step hints.
  peel.
  apply get_rval''; intro.
  descend; step hints.
  descend; step hints.
  2: returnScalar; eauto 7.
  simpl.
  make_toArray ("self" :: "tup" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples0' ] ].
  do_delegate2 ("self" :: "tup" :: nil).
  congruence.

  (* enumerate *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  peel.
  apply get_rval'''; intro.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt; eauto 7.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples0 ] ].
  do_delegate2 ("self" :: nil).


  (* Tuples1 *)

  (* new *)

  do_abort ("len" :: "key" :: nil).
  do_abort ("len" :: "key" :: nil).
  do_abort ("len" :: "key" :: nil).

  do_delegate1 ("len" :: "key" :: nil) hints.
  descend; step auto_ext.
  peel.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("len" :: "key" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  do_delegate2 ("len" :: "key" :: nil).

  (* insert *)

  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).

  do_delegate1 ("self" :: "tup" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl; step hints.
  peel.
  apply get_rval''; intro.
  descend; step hints.
  descend; step hints.
  2: returnScalar; eauto 8.
  simpl.
  make_toArray ("self" :: "tup" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples1' ] ].
  do_delegate2 ("self" :: "tup" :: nil).
  congruence.

  (* find *)

  do_abort ("self" :: "k" :: nil).
  do_abort ("self" :: "k" :: nil).
  do_abort ("self" :: "k" :: nil).

  do_delegate1 ("self" :: "k" :: nil) hints.
  peel.
  apply get_rval''''; intro.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt; eauto 8.
  simpl.
  make_toArray ("self" :: "k" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples1 ] ].
  do_delegate2 ("self" :: "k" :: nil).

  (* enumerate *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  peel.
  apply get_rval''''; intro.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt; eauto 8.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples1 ] ].
  do_delegate2 ("self" :: nil).


  (* Grabby time *)
  Grab Existential Variables.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
Qed.

Definition m1 := link ArrayTupleF.m m0.
Definition m2 := link TupleListF.m m1.
Definition m3 := link Tuples0F.m m2.
Definition m4 := link Tuples1F.m m3.
Definition m := link Malloc.m m4.

Theorem ok1 : moduleOk m1.
Proof.
  link ArrayTupleF.ok ok0.
Qed.

Theorem ok2 : moduleOk m2.
Proof.
  link TupleListF.ok ok1.
Qed.

Theorem ok3 : moduleOk m3.
Proof.
  link Tuples0F.ok ok2.
Qed.

Theorem ok4 : moduleOk m4.
Proof.
  link Tuples1F.ok ok3.
Qed.

Theorem ok : moduleOk m.
Proof.
  link Malloc.ok ok4.
Qed.
