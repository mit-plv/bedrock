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

Definition DirectCall x f args := (LabelEx "_f" f ;; CallEx x "_f" args)%stmtex.

Notation "'DCall' f ()" := (DirectCall None f nil)
  (no associativity, at level 95, f at level 0) : stmtex_scope.

Notation "'DCall' f ( x1 , .. , xN )" := (DirectCall None f (@cons Expr x1 (.. (@cons Expr xN nil) ..))%expr)
  (no associativity, at level 95, f at level 0) : stmtex_scope.
 
Notation "x <-- 'DCall' f ()" := (DirectCall (Some x) f nil)
  (no associativity, at level 95, f at level 0) : stmtex_scope.

Notation "x <-- 'DCall' f ( x1 , .. , xN )" := (DirectCall (Some x) f (@cons Expr x1 (.. (@cons Expr xN nil) ..))%expr) (no associativity, at level 95, f at level 0) : stmtex_scope.

Notation "a ! b" := (a, b) (only parsing) : stmtex_scope.

Notation value := 42.

Require Import WordMap.

Infix "==" := WordMap.Equal.
Notation addw := WordMap.add.
Notation Inw := WordMap.In.

Notation "'Assert' [ p ]" := (AssertEx p%stmtex_inv) : stmtex_scope.

Definition disj_add elt h' k v h := h' == @addw elt k v h /\ ~ Inw k h.

Notation "h1 === k --> v ** h" := (disj_add h1 k v h) (at level 60).

Definition body := (
  "c" <-- DCall "ADT"!"SimpleCell_new" ();;
  Assert [
    BEFORE(V, h)
    AFTER(V', h')
    h' === (V' "c") --> (Cell 0) ** h ];;
  DCall "ADT"!"SimpleCell_write"("c", value);;
  Assert [
    BEFORE(V, h)
    AFTER(V', h')
    h' === (V' "c") --> (Cell value) ** h];;
  "ret" <-- DCall "ADT"!"SimpleCell_read"("c");;
  Assert [
    BEFORE(V, h)
    AFTER(V', h')
    h' === (V' "c") --> (Cell value) ** h /\ V' "ret" = value];;
  DCall "ADT"!"SimpleCell_delete"("c");;
  Assert [
    BEFORE(V, h)
    AFTER(V', h')
    h' == h /\ V' "ret" = value]
  )%stmtex.

Definition f := (
  cfunction "use_cell"()
    body            
  end
)%Citofuncs.

Definition m := cmodule "use_cell" {{
  f
}}.

Lemma good : IsGoodModule m.
  good_module.
Qed.

Definition gm := to_good_module good.

Import LinkSpecMake2.

Notation " [[ ]] " := nil.
Notation " [[ x , .. , y ]] " := (cons x .. (cons y nil) ..).

Notation "name @ [ p ]" := (name%stmtex, p) (only parsing).

Definition modules := [[ gm ]].
Definition imports := of_list [[ 
                                  "ADT"!"SimpleCell_new" @ [SimpleCell_newSpec],
                                  "ADT"!"SimpleCell_write" @ [SimpleCell_writeSpec],
                                  "ADT"!"SimpleCell_read" @ [SimpleCell_readSpec],
                                  "ADT"!"SimpleCell_delete" @ [SimpleCell_deleteSpec]
                              ]].

Definition fspec := func_spec modules imports ("use_cell"!"use_cell")%stmtex f.

Notation extra_stack := 100.

Definition topS := SPEC reserving (4 + extra_stack)
  PREonly[_] mallocHeap 0.

Notation input := 5.

Definition top := bimport [[ ("use_cell"!"use_cell", fspec), "sys"!"printInt" @ [printIntS],
                             "sys"!"abort" @ [abortS] ]]
  bmodule "top" {{
    bfunction "top"("R") [topS]
      "R" <-- Call "use_cell"!"use_cell"(extra_stack)
      [PREonly[_, R] [| R = value |] ];;

      Call "sys"!"printInt"("R")
      [PREonly[_] Emp ];;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Definition empty_precond : assert := fun _ v0 v => v0 = v.

Require Import WordFacts2 WordFacts5.
Import LinkSpecMake.

Lemma sel_upd_eq' : forall vs nm v nm', nm = nm' -> (upd vs nm v) nm' = v.
  intros; eapply sel_upd_eq; eauto.
Qed.

Lemma sel_upd_ne' : forall vs nm v nm', nm <> nm' -> (upd vs nm v) nm' = sel vs nm'.
  intros; eapply sel_upd_ne; eauto.
Qed.

Ltac sel_upd_simpl :=
  repeat 
    match goal with
      | H : _ |- _ => rewrite sel_upd_eq in H by reflexivity
      | H : _ |- _ => rewrite sel_upd_ne in H by discriminate
      | |- _ => rewrite sel_upd_eq by reflexivity
      | |- _ => rewrite sel_upd_ne by discriminate
      | H : _ |- _ => rewrite sel_upd_eq' in H by reflexivity
      | H : _ |- _ => rewrite sel_upd_ne' in H by discriminate
      | |- _ => rewrite sel_upd_eq' by reflexivity
      | |- _ => rewrite sel_upd_ne' by discriminate
    end.

Lemma vcs_good : forall stn fs, stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> and_all (vc body empty_precond) (from_bedrock_label_map (Labels stn), fs stn).
  unfold empty_precond.
  Ltac cito_vcs body := unfold body; simpl;
    unfold imply_close, and_lift, interp; simpl(* ; *)
      (* firstorder cito'; auto *).

  cito_vcs body.
  intros; descend; intros; openhyp.
  cito'.
  econstructor.
  unfold from_bedrock_label_map, stn_good_to_use in *; simpl in *.
  eapply H.
  right; eapply mem_in_iff; reflexivity.

  Ltac inversion_RunsTo :=
    change ProgramLogicMake.SemanticsMake.RunsTo with RunsTo in *;
    match goal with
      | H : RunsTo _ _ _ _ |- _ => inversion H; unfold_all; subst;simpl in *; clear H
    end.

  Ltac cito' :=
    repeat (subst; simpl; selify; autorewrite with sepFormula in *; repeat inversion_RunsTo;
      repeat match goal with
               | [ H : _ |- _ ] => rewrite H
             end).

  cito'.
  eapply SafeCallForeign; simpl.
  unfold from_bedrock_label_map in *.
  eapply H0.
  descend.
  eauto.
  right.
  descend.
  eauto.
  reflexivity.
  instantiate (1 := nil).
  eauto.
  Require Import Semantics.
  unfold good_inputs; descend; unfold disjoint_ptrs; simpl; eauto.
  simpl; eauto.

  subst.
  inversion H3; unfold_all; subst; simpl in *; clear H3.
  unfold from_bedrock_label_map in *.

  assert (fs0 stn w = Some (Foreign SimpleCell_newSpec)).
  eapply H0.
  descend.
  eauto.
  right.
  descend.
  eauto.
  reflexivity.

  inversion H2; unfold_all; subst; simpl in *; clear H2.
  sel_upd_simpl; rewrite H1 in H6; intuition.
  sel_upd_simpl; rewrite H1 in H6; injection H6; intros; subst.

  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  assert (triples = nil) by (destruct triples; simpl in *; intuition).
  subst; simpl in *.
  split.
  reflexivity.
  unfold separated in *.
  openhyp; intuition.

  econstructor.
  eapply H.
  right; eapply mem_in_iff; reflexivity.
  
  inversion H2; unfold_all; subst; simpl in *; clear H2.
  unfold from_bedrock_label_map in *.

  eapply SafeCallForeign; simpl in *.
  sel_upd_simpl.
  eapply H0.
  descend.
  eauto.
  right.
  descend.
  eauto.
  reflexivity.

  sel_upd_simpl.
  instantiate (1 := [[ (sel (fst x) "c", inr (Cell 0)), ($42, inl ($42)) ]]).
  eauto.
  unfold good_inputs.
  split.
  unfold word_adt_match.
  econstructor.
  simpl.
  destruct H1.
  rewrite H1.
  Require Import WordMapFacts.
  eapply find_mapsto_iff.
  eapply add_mapsto_iff.
  eauto.
  econstructor.
  simpl.
  eauto.
  econstructor.
  unfold disjoint_ptrs.
  simpl.
  NoDup.
  simpl.
  descend; eauto.

  inversion H3; unfold_all; subst; simpl in *; clear H3.
  unfold from_bedrock_label_map in *.

  assert (fs0 stn w = Some (Foreign SimpleCell_writeSpec)).
  eapply H0.
  descend.
  eauto.
  right.
  descend.
  eauto.
  reflexivity.

  inversion H2; unfold_all; subst; simpl in *; clear H2.
  sel_upd_simpl; rewrite H3 in H7; intuition.
  sel_upd_simpl; rewrite H3 in H7; injection H7; intros; subst.

  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  Import SemanticsMake.
  Fixpoint make_triples_2 words (in_outs : list (ArgIn * ArgOut)) :=
    match words, in_outs with
      | p :: ps, o :: os => {| Word := p; ADTIn := fst o; ADTOut := snd o |} :: make_triples_2 ps os
      | _, _ => nil
    end.

  Lemma triples_intro : forall triples words in_outs, words = List.map (@Word _) triples -> List.map (fun x => (ADTIn x, ADTOut x)) triples = in_outs -> triples = make_triples_2 words in_outs.
    induction triples; destruct words; destruct in_outs; simpl in *; intuition.
    f_equal; intuition.
    destruct a; destruct p; simpl in *.
    injection H; injection H0; intros; subst.
    eauto.
  Qed.

  Import Semantics.
  eapply triples_intro in H2; try eassumption.
  subst; simpl in *.
  unfold good_inputs in *.
  openhyp.
  unfold word_adt_match in *.
  Ltac inversion_Forall :=
    repeat match goal with
             | H : List.Forall _ _ |- _ => inversion H; subst; clear H
           end.
  inversion_Forall; simpl in *.
  subst; simpl in *.
  unfold store_out; simpl.
  destruct H1.
  split.
  rewrite H1.
  Lemma map_add_same_key : forall elt m k v1 v2, @addw elt k v2 (addw k v1 m) == addw k v2 m.
    unfold WordMap.Equal; intros.
    repeat rewrite add_o.
    destruct (UWFacts.WFacts.P.F.eq_dec k y); intuition.
  Qed.
  eapply map_add_same_key.
  eauto.

  Require Import GLabelMapFacts.
  econstructor.
  eapply H.
  right; eapply mem_in_iff; reflexivity.

  inversion H2; unfold_all; subst; simpl in *; clear H2.
  unfold from_bedrock_label_map in *.

  eapply SafeCallForeign; simpl in *.
  sel_upd_simpl.
  eapply H0.
  descend.
  eauto.
  right.
  descend.
  eauto.
  reflexivity.

  sel_upd_simpl.
  instantiate (1 := [[ (sel (fst x) "c", inr (Cell 42)) ]]).
  eauto.
  unfold good_inputs.
  split.
  unfold word_adt_match.
  econstructor.
  simpl.
  destruct H1.
  rewrite H1.
  Require Import WordMapFacts.
  eapply find_mapsto_iff.
  eapply add_mapsto_iff.
  eauto.
  econstructor.
  unfold disjoint_ptrs.
  simpl.
  NoDup.
  simpl.
  descend; eauto.

  inversion H3; unfold_all; subst; simpl in *; clear H3.
  unfold from_bedrock_label_map in *.

  assert (fs0 stn w = Some (Foreign SimpleCell_readSpec)).
  eapply H0.
  descend.
  eauto.
  right.
  descend.
  eauto.
  reflexivity.

  inversion H2; unfold_all; subst; simpl in *; clear H2.
  sel_upd_simpl; rewrite H3 in H7; intuition.
  sel_upd_simpl; rewrite H3 in H7; injection H7; intros; subst.

  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  eapply triples_intro in H4; try eassumption.
  subst; simpl in *.
  unfold good_inputs in *.
  openhyp.
  unfold word_adt_match in *.
  inversion_Forall; simpl in *.
  destruct H1.
  rewrite H1 in H11.
  Import WordMapFacts.
  eapply find_mapsto_iff in H11.
  eapply add_mapsto_iff in H11.
  openhyp; intuition.
  injection H10; intros; subst.
  subst; simpl in *.
  split.
  unfold store_out; simpl.
  rewrite H1.
  eapply map_add_same_key.
  eauto.

  Require Import GLabelMapFacts.
  econstructor.
  eapply H.
  right; eapply mem_in_iff; reflexivity.

  inversion H2; unfold_all; subst; simpl in *; clear H2.
  unfold from_bedrock_label_map in *.

  eapply SafeCallForeign; simpl in *.
  sel_upd_simpl.
  eapply H0.
  descend.
  eauto.
  right.
  descend.
  eauto.
  reflexivity.

  sel_upd_simpl.
  instantiate (1 := [[ (sel (fst x) "c", inr (Cell 42)) ]]).
  eauto.
  unfold good_inputs.
  split.
  unfold word_adt_match.
  econstructor.
  simpl.
  destruct H1.
  rewrite H1.
  Require Import WordMapFacts.
  eapply find_mapsto_iff.
  eapply add_mapsto_iff.
  eauto.
  econstructor.
  unfold disjoint_ptrs.
  simpl.
  NoDup.
  simpl.
  descend; eauto.

  inversion H3; unfold_all; subst; simpl in *; clear H3.
  unfold from_bedrock_label_map in *.

  assert (fs0 stn w = Some (Foreign SimpleCell_deleteSpec)).
  eapply H0.
  descend.
  eauto.
  right.
  descend.
  eauto.
  reflexivity.

  inversion H2; unfold_all; subst; simpl in *; clear H2.
  sel_upd_simpl; rewrite H3 in H8; intuition.
  sel_upd_simpl; rewrite H3 in H8; injection H8; intros; subst.

  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  eapply triples_intro in H2; try eassumption.
  subst; simpl in *.
  split.
  unfold store_out; simpl.
  destruct H1.
  rewrite H1.
  Lemma add_remove : forall elt m k v, ~ @Inw elt k m -> WordMap.remove k (addw k v m) == m.
    unfold WordMap.Equal; intros.
    rewrite remove_o.
    rewrite add_o.
    destruct (UWFacts.WFacts.P.F.eq_dec k y); intuition.
    subst.
    symmetry; eapply not_find_in_iff; eauto.
  Qed.
  eapply add_remove; eauto.
  eauto.
  eauto.
Qed.

Local Hint Immediate vcs_good.

Lemma body_safe : forall stn fs v, stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  Ltac cito_safe f body pre := intros;
    unfold f, body, Body, Core; eapply sound_safe with (p := pre); [ reflexivity | eauto | .. ];
      simpl in *; try unfold pre in *; unfold imply_close, and_lift, interp in *; simpl in *;
        auto; openhyp; subst; simpl in *; intuition auto.

  cito_safe f body empty_precond.
Qed.

Lemma body_runsto : forall stn fs v v', stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = value /\ snd v' == snd v.
  Ltac cito_runsto f pre := intros;
    match goal with
      | [ H : _ |- _ ] => unfold f, Body, Core in H;
        eapply sound_runsto' with (p := pre) (s := Body f) in H;
          simpl in *; try unfold pre in *; unfold imply_close, and_lift, interp in *; simpl in *;
            auto; openhyp; subst; simpl in *; intuition auto; unfold and_lift in *; openhyp
    end.

  cito_runsto f empty_precond.
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
  call_cito 100 (@nil string).
  hiding ltac:(evaluate auto_ext).
  unfold name_marker.
  hiding ltac:(step auto_ext).
  unfold spec_without_funcs_ok.
  post.
  descend.
  eapply CompileExprs.change_hyp.
  Focus 2.
  apply (@is_state_in''' (upd x2 "extra_stack" 100)).
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
  change 100 with (wordToNat (sel (upd x2 "extra_stack" 100) "extra_stack")).
  Theorem is_state_out''''' : forall vs h sp rp F e_stack e_stack' args,
                               NoDup args
                               -> ~List.In "rp" args
                               -> ~List.In "extra_stack" args
                               -> h == heap_empty
                               -> (is_state sp rp e_stack e_stack' args
                                            (vs, h) nil * mallocHeap 0) * F
                                                                                     ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp
                                                                                                  * [| sel vs' "extra_stack" = e_stack|]
                                                                                                  * mallocHeap 0 * F.
    Opaque mult.
    intros.
    unfold is_state.
    unfold is_heap.
    simpl.
    set (InvMake.SemanticsMake.heap_elements _).
    unfold InvMake.SemanticsMake.heap_elements in l.
    assert (l = nil).
    Import WordMapFacts.
    assert (WordMap.cardinal h = 0).
    rewrite H2.
    reflexivity.
    rewrite WordMap.cardinal_1 in H3.
    subst l.
    Lemma length_nil : forall A ls, @length A ls = 0 -> ls = nil.
      destruct ls; simpl in *; intuition.
    Qed.
    eapply length_nil; eauto.
    subst l.
    rewrite H3.
    replace (_ * array _ _ * _ * _ * _)%Sep with (is_state sp0 rp e_stack e_stack' args (vs, heap_empty) [[]]).
    Focus 2.
    unfold is_state.
    unfold is_heap.
    sepLemma.
    clear H2 H3.
    eapply is_state_out''''; eauto.
    Transparent mult.
  Qed.

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

Import LinkMake.

Definition link_with_adts modules imports := result modules imports opt_good.

Definition all := link top (link_with_adts [[gm]] imports).

Theorem all_ok : moduleOk all.

  Require Import LinkFacts.
  Module Import LinkFactsMake := Make ExampleADT.

  Ltac impl_ok :=
    match goal with
      | |- moduleOk (link_with_adts ?Modules ?Imports ) =>
        let H := fresh in
        assert (GoodToLink_bool Modules Imports = true); 
          [ unfold GoodToLink_bool; simpl |
            eapply GoodToLink_bool_sound in H; openhyp; simpl in *; eapply result_ok; simpl in * ]
          ; eauto
    end.

  Import LinkModuleImplsMake.

  Ltac link0 ok1 :=
    eapply linkOk; [ eapply ok1 | impl_ok
      | reflexivity
      | simpl; unfold CompileModuleMake.mod_name; unfold impl_module_name;
        simpl; unfold StubsMake.StubMake.bimports_diff_bexports;
          simpl; unfold StubsMake.StubMake.LinkSpecMake2.func_impl_export;
            simpl; unfold StubsMake.StubMake.LinkSpecMake2.impl_label;
              unfold impl_module_name; simpl; unfold CompileModuleMake.imports; simpl;
                link_simp; eauto ..
                   ].

  link0 top_ok.
Qed.
