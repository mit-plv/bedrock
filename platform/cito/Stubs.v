Set Implicit Arguments.

Require Import ADT.
Require Import RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import AutoSep.
  Require Import StructuredModule.
  Require Import StructuredModuleFacts.
  Require Import GoodModule.
  Require Import GoodFunction.
  Require Import ConvertLabel.
  Require Import NameDecoration.
  Require Import Wrap.
  Require Import GeneralTactics.

  Require Import Stub.
  Module Import StubMake := Make E M.
  Require Import CompileFuncSpec.
  Import CompileFuncSpecMake.
  Require Import Inv.
  Import InvMake.
  Require Import Semantics.
  Import SemanticsMake.
  Import InvMake2.

  Require Import FMapFacts1.
  Require LabelMap.
  Module BLM := LabelMap.LabelMap.
  Module Import BLMF := WFacts_fun LabelMap.LabelKey BLM.
  Require Import Label.
  Module LM := LabelMap.
  Module Label_as_UDT := Key'.
  Module Import LMF := WFacts_fun Label_as_UDT LM.
  Module Import LMFU := UWFacts_fun Label_as_UDT LM.
  Require Import ListFacts2.
  Module LF := ListFacts2.
  Module Import LFL := Make Label_as_UDT.

  Module Import SS := StringSet.StringSet.
  Module Import SSF := StringSet.StringFacts.

  Import LM.
  Import P.
  Import F.

  Section TopSection.

    (* modules to be exported *)
    Variable modules : list GoodModule.

    Hypothesis NoDupModuleNames : List.NoDup (module_names modules).

    (* imported specs *)
    Variable imports : t ForeignFuncSpec.

    Hypothesis NoSelfImport : LF.Disjoint (module_names modules) (imported_module_names imports).

    Hypotheses ImportsGoodModuleName : forall l, In l imports -> IsGoodModuleName (fst l).

    Definition empty_module_name := "__empty_module".

    Definition empty_module := @StructuredModule.bmodule_ nil empty_module_name nil.

    Fixpoint link_all ls := 
      match ls with
        | nil => empty_module
        | x :: xs => link x (link_all xs)
      end.

    Definition to_set ls := List.fold_left (fun s e => SS.add e s) ls SS.empty.

    Definition to_bl_pair elt (p : label * elt) := (fst p : Labels.label, snd p).

    Definition to_blm elt m := BLMF.to_map (List.map (@to_bl_pair _) (@elements elt m)).

    Definition Equal2 elt (m1 : BLM.t elt) (m2 : t elt) := BLM.Equal m1 (to_blm m2).

    Definition get_module_Exports (module : GoodModule) := 
      to_map 
        (List.map 
           (fun (f : GoodFunction) =>
              ((MName module, FName f), spec_without_funcs_ok_fs modules imports f))
           (Functions module)).

    Definition update_all elt maps := List.fold_left (fun acc m => update acc m) maps (@empty elt).

    Definition total_imports := update (update_all (List.map get_module_Exports modules)) (map StubMake.foreign_spec imports).

    Definition do_make_module := make_module modules imports.

    Lemma link_all_ok : 
      forall (ms : list GoodModule), 
        let module_names := List.map MName ms in
        let linked := link_all (List.map do_make_module ms) in
        let linked_module_names := to_set (empty_module_name :: module_names) in
        let linked_exports := update_all (List.map get_module_Exports ms) in
        let linked_imports := P.diff total_imports linked_exports in
        incl ms modules ->
        List.NoDup module_names ->
        moduleOk linked /\
        SS.Equal (Modules linked) linked_module_names /\
        Equal2 (Exports linked) linked_exports /\
        Equal2 (Imports linked) linked_imports.
      Proof.
        induction ms; simpl; intros.
        descend.
        vcgen.
        Import ListNotations.
        Lemma to_set_singleton : forall e, SS.Equal (to_set [e]) (singleton e).
          intros.
          unfold to_set.
          simpl.
          unfold SS.Equal.
          split; intros.
          eapply singleton_iff.
          eapply add_iff in H.
          openhyp.
          eauto.
          eapply empty_iff in H.
          intuition.
          eapply singleton_iff in H.
          eapply add_iff; eauto.
        Qed.
        symmetry; eapply to_set_singleton.
        unfold update_all; simpl.
        Lemma Equal2_empty : forall elt, Equal2 (BLM.empty elt) (empty elt).
          admit.
        Qed.
        eapply Equal2_empty.
        Lemma Equal2_importsMap : forall ls, NoDupKey ls -> Equal2 (importsMap ls) (to_map ls).
          admit.
        Qed.

        Lemma Equal2_Equal : forall elt ls1 ls2 ls2', @Equal2 elt ls1 ls2 -> Equal ls2' ls2 -> Equal2 ls1 ls2'.
          admit.
        Qed.

        eapply Equal2_Equal.
        eapply Equal2_importsMap.
        Require Import SetoidList.
        Hint Constructors NoDupA.
        Hint Unfold NoDupKey.

        eauto.
        Infix "==" := Equal.
        Notation empty := (@empty _).

        Lemma to_map_empty : forall elt, @to_map elt [] == empty.
          admit.
        Qed.
        
        rewrite to_map_empty.
        unfold update_all; simpl.
        Lemma diff_empty : forall elt m, @diff elt m empty == empty.
          admit.
        Qed.
        eapply diff_empty.

        descend.
        eapply linkOk.
        eapply make_module_ok; eauto.
        intuition.
        eapply IHms.
        eapply incl_tran.
        2 : eauto.
        intuition.
        inversion H0; subst; eauto.
(*here*)
        admit.
        unfold Imports, make_module, bmodule_.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
    Qed.

    Definition ms := List.map do_make_module modules.

    Definition m := link_all ms.

    Theorem ok : moduleOk m.
      unfold m.
      unfold ms.
      eapply link_all_ok; intuition.
    Qed.

  End TopSection.

End Make.
