Set Implicit Arguments.

Require Import MakeWrapper ExampleADT ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.

Require Import Notations4.
Module Import Notations4Make := Make ExampleADT.

Require Import Arith.
Import ProgramLogicMake.
Open Scope nat.

Require Import ExampleImpl.

Require Import FiniteSet.
Require Import WordMap.
Import WordMap.

Infix "==" := Equal.
Infix "=s=" := WordSet.Equal (at level 60).

Definition singleton_map elt k v := @add elt k v (empty _).

Infix "-->" := (@singleton_map _) (at level 40).

Require Import WordMapFacts.

Definition AllDisjoint elt := ForallOrdPairs (@Disjoint elt).

Definition equal_disj_update_all elt h' hs := (h' == @update_all elt hs) /\ AllDisjoint hs.

Notation "h === x ** .. ** y" := (equal_disj_update_all h (cons x .. (cons y nil) ..)) (at level 60).

Require MSetProperties.
Module WordSetFacts := MSetProperties.Properties WordSet.

Notation to_set := WordSetFacts.of_list.

Definition wnat (w : W) := wordToNat w.
Coercion wnat : W >-> nat.

Notation " [[ ]] " := nil.
Notation " [[ x , .. , y ]] " := (cons x .. (cons y nil) ..).

Definition count_body := (
    "set" <-- DCall "ADT"!"ListSet_new"();;
    "i" <- 0;;
    [BEFORE (V, h) AFTER (V', h') exists arr fset,
       (h' === h ** (V "arr" --> Arr arr) ** (V "set" --> FSet fset)) /\ 
       V "len" = length arr /\
       fset =s= to_set (firstn (V "i") arr)
    ]
    While ("i" < "len") {
      "e" <-- DCall "ADT"!"ArraySeq_read" ("arr", "i");;
      DCall "ADT"!"ListSet_add"("set", "e");;
      "i" <- "i" + 1
    };;
    "ret" <-- DCall "ADT"!"ListSet_size"("set");;
    DCall "ADT"!"ListSet_delete"("set")
)%stmtex.

Definition main_body := (
    "arr" <-- DCall "ADT"!"ArraySeq_new"(3);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ length arr = 3 ];;
    DCall "ADT"!"ArraySeq_write"("arr", 0, 10);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ length arr = 3 /\ nth_error arr 0 = Some $10 ];;
    DCall "ADT"!"ArraySeq_write"("arr", 1, 20);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ exists w, arr = [[$10, $20, w]] ];;
    DCall "ADT"!"ArraySeq_write"("arr", 2, 10);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ arr = [[$10, $20, $10]] ];;
    "ret" <-- DCall "count"!"count" ("arr", 3);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ V' "ret" = 2 ];;
    DCall "ADT"!"ArraySeq_delete"("arr");;
    Assert [ BEFORE(V, h) AFTER(V', h') 
      h' == h /\ V' "ret" = 2 ]
)%stmtex.

Definition m := cmodule "count" {{
  cfunction "count"("arr", "len")
    count_body
  end with
  cfunction "main"()
    main_body
  end
}}.

Lemma good : IsGoodModule m.
  good_module.
Qed.

Definition gm := to_good_module good.

Import LinkSpecMake2.

Notation "name @ [ p ]" := (name%stmtex, p) (only parsing).

Definition modules := [[ gm ]].

Require Import GLabelMapFacts.

Definition imports := 
  of_list 
    [[ 
        "ADT"!"ArraySeq_new" @ [ArraySeq_newSpec],
        "ADT"!"ArraySeq_write" @ [ArraySeq_writeSpec],
        "ADT"!"ArraySeq_read" @ [ArraySeq_readSpec],
        "ADT"!"ArraySeq_delete" @ [ArraySeq_deleteSpec],
        "ADT"!"ListSet_new" @ [ListSet_newSpec],
        "ADT"!"ListSet_add" @ [ListSet_addSpec],
        (* "ADT"!"ListSet_size" @ [ListSet_sizeSpec], *)
        "ADT"!"ListSet_delete" @ [ListSet_deleteSpec]
    ]].

Definition main_spec_Bedrock := func_spec modules imports ("count"!"main")%stmtex f.

Notation extra_stack := 40.

Definition topS := SPEC reserving (4 + extra_stack)
  PREonly[_] mallocHeap 0.

Definition top := bimport [[ ("count"!"main", main_spec_Bedrock), "sys"!"printInt" @ [printIntS],
                             "sys"!"abort" @ [abortS] ]]
  bmodule "top" {{
    bfunction "top"("R") [topS]
      "R" <-- Call "count"!"count"(extra_stack)
      [PREonly[_, R] [| R = 2 |] ];;

      Call "sys"!"printInt"("R")
      [PREonly[_] Emp ];;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Definition dummy_gf : GoodFunction.
  refine (to_good_function (cfunction "dummy"() "ret" <- 0 end)%Citofuncs _).
  good_module.
Defined.    

Definition count := nth 0 (Functions gm) dummy_gf.
Definition main := nth 1 (Functions gm) dummy_gf.

Import Semantics.
Import SemanticsMake.

Import WordSet.

Definition unique_count ls := cardinal (fold_right add empty ls).

Definition count_spec : ForeignFuncSpec :=
  {|
    PreCond := fun args => exists arr len, args = inr (Arr arr) :: inl len :: nil /\ len = length arr;
    PostCond := fun args ret => exists arr len, args = (inr (Arr arr), Some (Arr arr)) :: (inl len, None) :: nil /\ ret = inl (unique_count arr : W)
  |}.

Require Import GLabelMap.
Import GLabelMap.GLabelMap.

Definition make_specs modules imports := fold_right (fun m acc => fold_right (fun (f : GoodFunction) acc => add (GName m, FName f) (Internal f) acc) acc (Functions m)) (map Foreign imports) modules.

Definition specs := add ("count", "count") (Foreign count_spec) (make_specs modules imports).

Import LinkSpecMake.
Require Import LinkSpecFacts.
Module Import LinkSpecFactsMake := Make ExampleADT.
Import Notations4Make.

Lemma specs_good : specs_equal specs modules imports.
(*  split; intros.

  unfold imports_exports_mapsto, specs in *.
  eapply find_mapsto_iff in H.
  eapply add_mapsto_iff in H.
  openhyp.
  subst; simpl in *.
  left; descend; eauto.
  unfold spec_op, gm; simpl; eauto.

  eapply map_mapsto_iff in H0.
  openhyp.
  subst; simpl in *.
  right; descend; eauto.
  eapply find_mapsto_iff; eauto.

  unfold imports_exports_mapsto, specs in *.
  eapply find_mapsto_iff.
  eapply add_mapsto_iff.
  openhyp.
  subst; simpl in *.
  openhyp.
  2 : intuition.
  subst.
  left.
  unfold spec_op, gm, to_good_module in *; simpl in *.
  openhyp.
  2 : intuition.
  subst; simpl in *.
  eauto.

  subst; simpl in *.
  right; descend; eauto.
  Require Import GeneralTactics2.
  nintro.
  subst; simpl in *.
  compute in H0.
  intuition.
  eapply map_mapsto_iff.
  descend; eauto.
  eapply find_mapsto_iff; eauto.*)
  admit.
Qed.

Require Import WordFacts2 WordFacts5.
Require Import WordMapFacts.

Definition empty_precond : assert := fun _ v0 v => v0 = v.

Import ProgramLogicMake.SemanticsMake.

Ltac destruct_state :=
  repeat match goal with
           | [ x : State |- _ ] => destruct x; simpl in *
         end.

Lemma vcs_good : and_all (vc main_body empty_precond) specs.
  unfold empty_precond, main_body; simpl; unfold imply_close, and_lift; simpl.

  repeat match goal with
           | |- _ /\ _ => split
         end.

  intros.
  subst.
  unfold SafeDCall.
  simpl.
  intros.
  Import TransitMake.
  unfold TransitSafe.
  descend.
  instantiate (1 := [[ ($3, _) ]]).
  eauto.
  repeat econstructor.
  instantiate (1 := inl $3).
  repeat econstructor.
  repeat econstructor.
  descend; eauto.

  intros.
  destruct_state.
  openhyp.
  subst.
  unfold RunsToDCall in *.
  simpl in *.
  openhyp.
  unfold TransitTo in *.
  openhyp.
  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  eapply triples_intro in H3; try eassumption.
  subst; simpl in *.
  Import SemanticsMake.
  unfold good_inputs, Semantics.good_inputs in *.
  openhyp.
  unfold Semantics.word_adt_match in *.
  inversion_Forall; simpl in *.
  subst.
  unfold store_out, Semantics.store_out in *; simpl in *.
  descend; eauto.
  Import WordMap.
  Require Import GeneralTactics2.

  Lemma empty_mapsto_elim : forall P elt k v, MapsTo k v (empty elt) -> P.
    intros.
    eapply empty_mapsto_iff in H; intuition.
  Qed.
  Hint Extern 0 => (eapply empty_mapsto_elim; eassumption).
  Lemma empty_in_elim : forall P elt k, In k (empty elt) -> P.
    intros.
    eapply empty_in_iff in H; intuition.
  Qed.
  Hint Extern 0 => (eapply empty_in_elim; eassumption).
  Lemma singleton_mapsto_iff : forall elt k v k' v', @MapsTo elt k' v' (k --> v) <-> k' = k /\ v' = v.
    split; intros.
    eapply add_mapsto_iff in H; openhyp; eauto.
    openhyp; eapply add_mapsto_iff; eauto.
  Qed.
  Lemma singleton_in_iff : forall elt k k' v, @In elt k' (k --> v) <-> k' = k.
    split; intros.
    eapply add_in_iff in H; openhyp; eauto.
    openhyp; eapply add_in_iff; eauto.
  Qed.
  Lemma update_add : forall elt k v h, @update elt h (k --> v) == add k v h.
    intros.
    unfold Equal; intros.
    eapply option_univalence.
    split; intros.

    eapply find_mapsto_iff in H.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff in H.
    openhyp.
    eapply singleton_mapsto_iff in H.
    openhyp; subst.
    eapply add_mapsto_iff; eauto.
    eapply add_mapsto_iff.
    right.
    split.
    not_not.
    subst.
    eapply singleton_in_iff; eauto.
    eauto.

    eapply find_mapsto_iff in H.
    eapply find_mapsto_iff.
    eapply add_mapsto_iff in H.
    openhyp.
    subst.
    eapply update_mapsto_iff.
    left.
    eapply singleton_mapsto_iff; eauto.
    eapply update_mapsto_iff.
    right.
    split.
    eauto.
    not_not.
    eapply singleton_in_iff in H1; eauto.
  Qed.
  Lemma singleton_disj : forall elt k v h, ~ @In elt k h <-> Disjoint h (k --> v).
    unfold Disjoint; split; intros.
    not_not; openhyp.
    eapply singleton_in_iff in H0; subst; eauto.
    nintro.
    specialize (H k).
    contradict H.
    split.
    eauto.
    eapply singleton_in_iff; eauto.
  Qed.
  Lemma separated_star : forall h k v, separated h k (Some v) -> add k v h === h ** k --> v.
    intros.
    unfold separated, Semantics.separated in *.
    openhyp.
    intuition.
    split.
    unfold update_all.
    simpl.
    rewrite update_add.
    rewrite update_empty_1.
    reflexivity.
    repeat econstructor.
    eapply singleton_disj; eauto.
  Qed.
  eapply separated_star; eauto.

  intros.
  unfold SafeDCall.
  simpl.
  intros.
  destruct_state.
  openhyp.
  destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in *; rewrite update_add in *.
  unfold TransitSafe.
  descend.
  Require Import BedrockTactics.
  sel_upd_simpl.
  Lemma map_fst_combine : forall A B (a : list A) (b : list B), length a = length b -> a = List.map fst (List.combine a b).
    induction a; destruct b; simpl; intuition.
    f_equal; eauto.
  Qed.
  eapply map_fst_combine.
  instantiate (1 := [[ _, _, _ ]]); eauto.
  split.
  unfold Semantics.word_adt_match.
  repeat econstructor; simpl.
  eauto.
  instantiate (1 := inr (Arr x)); simpl in *.
  rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
  instantiate (1 := inl $0); simpl in *.
  eauto.
  instantiate (1 := inl $10); simpl in *.
  eauto.
  simpl.
  unfold Semantics.disjoint_ptrs.
  NoDup.
  descend; eauto.
  rewrite H0.
  eauto.

  (*here*)

  split.
  intros.
  openhyp.
  destruct_state.
  unfold RunsToDCall in *.
  simpl in *.
  openhyp.
  unfold TransitTo in *.
  openhyp.
  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  eapply triples_intro in H4; try eassumption.
  subst; simpl in *.
  unfold good_inputs, Semantics.good_inputs in *.
  openhyp.
  unfold Semantics.word_adt_match in *.
  inversion_Forall; simpl in *.
  subst; simpl in *.
  unfold store_out, Semantics.store_out in *; simpl in *.
  destruct H.
  split.
  rewrite H.
  eapply map_add_same_key.
  eauto.

  split.
  intros.
  unfold SafeDCall.
  simpl.
  intros.
  destruct_state.
  unfold TransitSafe.
  descend.
  sel_upd_simpl.
  instantiate (1 := [[ (sel v0 "c", inr (Cell 42)) ]]).
  eauto.
  split.
  unfold Semantics.word_adt_match.
  repeat econstructor.
  simpl.
  destruct H.
  rewrite H.
  eapply find_mapsto_iff.
  eapply add_mapsto_iff.
  eauto.
  NoDup.
  descend; eauto.

  split.
  intros.
  openhyp.
  destruct_state.
  unfold RunsToDCall in *.
  simpl in *.
  openhyp.
  unfold TransitTo in *.
  openhyp.
  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  eapply triples_intro in H8; try eassumption.
  subst; simpl in *.
  unfold good_inputs, Semantics.good_inputs in *.
  openhyp.
  unfold Semantics.word_adt_match in *.
  inversion_Forall; simpl in *.
  unfold store_out, Semantics.store_out in *; simpl in *.
  destruct H.
  rewrite H in H7.
  eapply find_mapsto_iff in H7.
  eapply add_mapsto_iff in H7.
  sel_upd_simpl.
  openhyp; intuition.
  injection H6; intros; subst.
  split.
  rewrite H.
  eapply map_add_same_key.
  eauto.

  split.
  intros.
  unfold SafeDCall.
  simpl.
  intros.
  destruct_state.
  unfold TransitSafe.
  descend.
  sel_upd_simpl.
  instantiate (1 := [[ (sel v0 "c", inr (Cell 42)) ]]).
  eauto.
  split.
  unfold Semantics.word_adt_match.
  repeat econstructor.
  simpl.
  openhyp.
  destruct H.
  rewrite H.
  eapply find_mapsto_iff.
  eapply add_mapsto_iff.
  eauto.
  NoDup.
  descend; eauto.

  split.
  intros.
  openhyp.
  destruct_state.
  unfold RunsToDCall in *.
  simpl in *.
  openhyp.
  unfold TransitTo in *.
  openhyp.
  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  eapply triples_intro in H5; try eassumption.
  subst; simpl in *.
  unfold store_out, Semantics.store_out in *; simpl in *.
  destruct H.
  split.
  rewrite H.
  eapply add_remove; eauto.
  eauto.

  eauto.
Qed.

Local Hint Immediate vcs_good.

Hint Resolve specs_good.

Lemma body_runsto : forall stn fs v v', stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = value /\ snd v' == snd v.
  cito_runsto f empty_precond vcs_good; eauto.
  eapply specs_equal_agree; eauto.
Qed.

Lemma body_safe : forall stn fs v, stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  cito_safe f empty_precond vcs_good; eauto.
  eapply specs_equal_agree; eauto.
Qed.

Require Import Inv.
Module Import InvMake := Make ExampleADT.
Module Import InvMake2 := Make ExampleRepInv.
Import Made.

Theorem top_ok : moduleOk top.
  vcgen.

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.

  post.
  call_cito 40 (@nil string).
  hiding ltac:(evaluate auto_ext).
  unfold name_marker.
  hiding ltac:(step auto_ext).
  unfold spec_without_funcs_ok.
  post.
  descend.
  eapply CompileExprs.change_hyp.
  Focus 2.
  apply (@is_state_in''' (upd x2 "extra_stack" 40)).
  autorewrite with sepFormula.
  clear H7 H8.
  hiding ltac:(step auto_ext).
  apply body_safe; eauto.
  hiding ltac:(step auto_ext).
  repeat ((apply existsL; intro) || (apply injL; intro) || apply andL); reduce.
  apply swap; apply injL; intro.
  openhyp.
  Import LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.
  match goal with
    | [ x : State |- _ ] => destruct x; simpl in *
  end.
  apply body_runsto in H9; simpl in H9; intuition subst.
  eapply replace_imp.
  change 40 with (wordToNat (sel (upd x2 "extra_stack" 40) "extra_stack")).
  apply is_state_out'''''.
  NoDup.
  NoDup.
  NoDup.
  eauto.
  
  hiding ltac:(step auto_ext).
  hiding ltac:(step auto_ext).

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
Qed.

Definition all := link top (link_with_adts [[gm]] imports).

Theorem all_ok : moduleOk all.
  link0 top_ok.
Qed.
