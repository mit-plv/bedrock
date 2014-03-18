Set Implicit Arguments.

Require Import ExampleADT.
Import ExampleADT.ExampleADT.
Require Import WordMap.
Require Import RepInv MakeADT.

Require Import AutoSep.

Require Import SimpleCell ArraySeq FiniteSet ListSet.
Require Import ExampleRepInv.

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

Lemma readd : forall c rv rv',
  cell rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (Cell rv') (heap_upd heap_empty c (Cell rv))).
  intros.
  unfold is_heap at 2.
  assert (List.In (c, Cell rv') (heap_elements (WordMap.add c (Cell rv') (heap_upd heap_empty c (Cell rv))))).
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

Lemma readd_Arr : forall c rv rv',
  arr rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (Arr rv') (heap_upd heap_empty c (Arr rv))).
  intros.
  unfold is_heap at 2.
  assert (List.In (c, Arr rv') (heap_elements (WordMap.add c (Arr rv') (heap_upd heap_empty c (Arr rv))))).
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

Lemma readd_FSet : forall c rv rv',
  lset rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (FSet rv') (heap_upd heap_empty c (FSet rv))).
  intros.
  unfold is_heap at 2.
  assert (List.In (c, FSet rv') (heap_elements (WordMap.add c (FSet rv') (heap_upd heap_empty c (FSet rv))))).
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

Lemma get_rval' : forall specs st P (Q : Prop) R S T Z,
  (Q -> interp specs (![P * R * S * T] st ---> Z)%PropX)
  -> interp specs (![P * ((R * [|Q|]) * S) * T] st ---> Z)%PropX.
  intros.
  apply Imply_trans with (![[|Q|] * (P * R * S * T)]st)%PropX.
  assert (P * (R * [|Q|] * S) * T ===> [|Q|] * (P * R * S * T)).
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
    PostCond := fun args ret => exists n r, args = (inr (Cell n), None) :: nil /\ ret = inl r
  |}.

Definition SimpleCell_readSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => exists n, args = inr (Cell n) :: nil;
    PostCond := fun args ret => exists n, ret = inl n /\ args = (inr (Cell n), Some (Cell n)) :: nil
  |}.

Definition SimpleCell_writeSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => exists n n', args = inr (Cell n) :: inl n' :: nil;
    PostCond := fun args ret => exists n n' r, args = (inr (Cell n), Some (Cell n')) :: (inl n', None) :: nil
      /\ ret = inl r
  |}.

Definition ArraySeq_newSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => exists len, args = inl len :: nil /\ goodSize (2 + wordToNat len);
    PostCond := fun args ret => exists len ws, args = (inl len, None) :: nil /\ ret = inr (Arr ws)
      /\ length ws = wordToNat len
  |}.

Definition ArraySeq_deleteSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => exists ws, args = inr (Arr ws) :: nil;
    PostCond := fun args ret => exists ws r, args = (inr (Arr ws), None) :: nil /\ ret = inl r
  |}.

Definition ArraySeq_readSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => exists ws n, args = inr (Arr ws) :: inl n :: nil
      /\ n < natToW (length ws);
    PostCond := fun args ret => exists ws n, ret = inl (Array.sel ws n)
      /\ args = (inr (Arr ws), Some (Arr ws)) :: (inl n, None) :: nil
  |}.

Definition ArraySeq_writeSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => exists ws n v, args = inr (Arr ws) :: inl n :: inl v :: nil
      /\ n < natToW (length ws);
    PostCond := fun args ret => exists ws n v r, args = (inr (Arr ws), Some (Arr (Array.upd ws n v)))
      :: (inl n, None) :: (inl v, None) :: nil /\ ret = inl r
  |}.

Definition ListSet_newSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => args = nil;
    PostCond := fun args ret => args = nil /\ ret = inr (FSet WordSet.empty)
  |}.

Definition ListSet_deleteSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => exists s, args = inr (FSet s) :: nil;
    PostCond := fun args ret => exists s r, args = (inr (FSet s), None) :: nil /\ ret = inl r
  |}.

Definition ListSet_memSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => exists s n, args = inr (FSet s) :: inl n :: nil;
    PostCond := fun args ret => exists s n, ret = inl (WordSet.mem n s : W)
      /\ args = (inr (FSet s), Some (FSet s)) :: (inl n, None) :: nil
  |}.

Definition ListSet_addSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => exists s n, args = inr (FSet s) :: inl n :: nil;
    PostCond := fun args ret => exists s n r, args = (inr (FSet s), Some (FSet (WordSet.add n s)))
      :: (inl n, None) :: nil /\ ret = inl r
  |}.

Definition ListSet_sizeSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => exists s, args = inr (FSet s) :: nil;
    PostCond := fun args ret => exists s, ret = inl (WordSet.cardinal s : W)
      /\ args = (inr (FSet s), Some (FSet s)) :: nil
  |}.

Definition m0 := bimport [[ "sys"!"abort" @ [abortS],
                            "SimpleCell"!"new" @ [SimpleCell.newS],
                            "SimpleCell"!"delete" @ [SimpleCell.deleteS],
                            "SimpleCell"!"read" @ [SimpleCell.readS],
                            "SimpleCell"!"write" @ [SimpleCell.writeS],
                            "ArraySeq"!"new" @ [ArraySeq.newS],
                            "ArraySeq"!"delete" @ [ArraySeq.deleteS],
                            "ArraySeq"!"read" @ [ArraySeq.readS],
                            "ArraySeq"!"write" @ [ArraySeq.writeS],
                            "ListSet"!"new" @ [ListSet.newS],
                            "ListSet"!"delete" @ [ListSet.deleteS],
                            "ListSet"!"mem" @ [ListSet.memS],
                            "ListSet"!"add" @ [ListSet.addS],
                            "ListSet"!"size" @ [ListSet.sizeS] ]]
  fmodule "ADT" {{
    ffunction "SimpleCell_new" reserving 8 [SimpleCell_newSpec] := "SimpleCell"!"new"
    with ffunction "SimpleCell_delete" reserving 6 [SimpleCell_deleteSpec] := "SimpleCell"!"delete"
    with ffunction "SimpleCell_read" reserving 0 [SimpleCell_readSpec] := "SimpleCell"!"read"
    with ffunction "SimpleCell_write" reserving 0 [SimpleCell_writeSpec] := "SimpleCell"!"write"
    with ffunction "ArraySeq_new" reserving 8 [ArraySeq_newSpec] := "ArraySeq"!"new"
    with ffunction "ArraySeq_delete" reserving 7 [ArraySeq_deleteSpec] := "ArraySeq"!"delete"
    with ffunction "ArraySeq_read" reserving 0 [ArraySeq_readSpec] := "ArraySeq"!"read"
    with ffunction "ArraySeq_write" reserving 0 [ArraySeq_writeSpec] := "ArraySeq"!"write"
    with ffunction "ListSet_new" reserving 8 [ListSet_newSpec] := "ListSet"!"new"
    with ffunction "ListSet_delete" reserving 7 [ListSet_deleteSpec] := "ListSet"!"delete"
    with ffunction "ListSet_mem" reserving 1 [ListSet_memSpec] := "ListSet"!"mem"
    with ffunction "ListSet_add" reserving 9 [ListSet_addSpec] := "ListSet"!"add"
    with ffunction "ListSet_size" reserving 1 [ListSet_sizeSpec] := "ListSet"!"size"
  }}.

Theorem ok0 : moduleOk m0.
  vcgen.


  (* SimpleCell *)

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
  do 2 (descend; step auto_ext).
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply is_heap_eat ] ].
  do_delegate2 ("self" :: nil).

  (* read *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step auto_ext.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval; intro; subst.
  step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd ] ].
  do_delegate2 ("self" :: nil).

  (* write *)

  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).

  do_delegate1 ("self" :: "n" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl.
  descend; step auto_ext.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "n" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd ] ].
  do_delegate2 ("self" :: "n" :: nil).


  (* ArraySeq *)

  (* new *)

  do_abort ("len" :: nil).
  do_abort ("len" :: nil).
  do_abort ("len" :: nil).

  do_delegate1 ("len" :: nil) hints.
  descend; step auto_ext.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval'; intro.
  step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("len" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  do_delegate2 ("len" :: nil).

  (* delete *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  do 2 (descend; step auto_ext).
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply is_heap_eat ] ].
  do_delegate2 ("self" :: nil).

  (* read *)

  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).

  do_delegate1 ("self" :: "n" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  descend; step hints.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval; intro; subst.
  step auto_ext.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "n" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.

  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Arr ] ].
  do_delegate2 ("self" :: "n" :: nil).

  (* write *)

  do_abort ("self" :: "n" :: "v" :: nil).
  do_abort ("self" :: "n" :: "v" :: nil).
  do_abort ("self" :: "n" :: "v" :: nil).

  do_delegate1 ("self" :: "n" :: "v" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl.
  descend; step auto_ext.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnScalar; eauto 10.
  simpl.
  make_toArray ("self" :: "n" :: "v" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Arr ] ].
  do_delegate2 ("self" :: "n" :: "v" :: nil).


  (* ListSet *)

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
  do 2 (descend; step auto_ext).
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply is_heap_eat ] ].
  do_delegate2 ("self" :: nil).

  (* mem *)

  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).

  do_delegate1 ("self" :: "n" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl.
  descend; step auto_ext.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval; intro.
  step auto_ext.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "n" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_FSet ] ].
  do_delegate2 ("self" :: "n" :: nil).

  (* add *)

  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).

  do_delegate1 ("self" :: "n" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl.
  descend; step auto_ext.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "n" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_FSet ] ].
  do_delegate2 ("self" :: "n" :: nil).

  (* size *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step hints.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval; intro.
  step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_FSet ] ].
  do_delegate2 ("self" :: nil).


  Grab Existential Variables.
  exact 0.
  exact 0.
  exact 0.
Qed.

Definition m1 := link SimpleCell.m m0.
Definition m2 := link ArraySeq.m m1.
Definition m3 := link ListSet.m m2.
Definition m := link Malloc.m m3.

Theorem ok1 : moduleOk m1.
  link SimpleCell.ok ok0.
Qed.

Theorem ok2 : moduleOk m2.
  link ArraySeq.ok ok1.
Qed.

Theorem ok3 : moduleOk m3.
  link ListSet.ok ok2.
Qed.

Theorem ok : moduleOk m.
  link Malloc.ok ok3.
Qed.
