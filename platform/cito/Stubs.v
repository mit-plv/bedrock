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
  Require Import FMapFacts3.

  Require Import ConvertLabelMap.
  Import Notations.
  Open Scope clm_scope.

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

  Module Import SS := StringSet.StringSet.
  Module Import SSF := StringSet.StringFacts.
  Module SSK := StringSet.StringKey.
  Require Import FSetFacts1.
  Module SSK_as_UDT := Make_UDT SSK.
  Module Import SSUF := UWFacts_fun SSK_as_UDT SS.

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
    
    Definition get_module_Exports (module : GoodModule) := 
      to_map 
        (List.map 
           (fun (f : GoodFunction) =>
              ((MName module, FName f), spec_without_funcs_ok_fs modules imports f))
           (Functions module)).

    Definition total_imports := update (update_all (List.map get_module_Exports modules)) (map StubMake.foreign_spec imports).

    Definition do_make_module := make_module modules imports.

    (* make_module interface *)

    Lemma make_module_Imports : forall m, List.In m modules -> Imports (do_make_module m) === diff total_imports (get_module_Exports m).
      admit.
    Qed.

    Lemma make_module_Exports : forall m, List.In m modules -> Exports (do_make_module m) === get_module_Exports m.
      admit.
    Qed.

    Lemma make_module_Modules : forall m, List.In m modules -> SS.Equal (Modules (do_make_module m)) (singleton (MName m)).
      admit.
    Qed.

    Lemma GoodModule_Name_neq_empty_module_name : forall m : GoodModule, MName m <> empty_module_name.
      admit.
    Qed.

    (* some reinterpretation of Bedrock facilities *)

    Lemma importsMap_of_list : forall ls, NoDupKey ls -> importsMap ls === of_list ls.
      admit.
    Qed.

    Lemma importsOk_Compat : forall m1 m2, importsOk m1 m2 <-> BLMFU3.Compat m1 m2.
      admit.
    Qed.

    Lemma XCAP_union_update : forall elt m1 m2, BLM.Equal (@XCAP.union elt m1 m2) (BLMF.P.update m2 m1).
      admit.
    Qed.

    Lemma XCAP_diff_diff : forall elt m1 m2, @BLM.Equal elt (XCAP.diff m1 m2) (BLMF.P.diff m1 m2).
      admit.
    Qed.

    (* main lemmas *)
    Lemma compat_imports_exports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (diff total_imports (get_module_Exports m)) (update_all (List.map get_module_Exports ms)).
      admit.
    Qed.

    Lemma compat_exports_imports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (get_module_Exports m) (diff total_imports (update_all (List.map get_module_Exports ms))).
      admit.
    Qed.

    Lemma compat_imports_imports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (diff total_imports (get_module_Exports m)) (diff total_imports (update_all (List.map get_module_Exports ms))).
      admit.
    Qed.

    Lemma Disjoint_exports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Disjoint (get_module_Exports m) (update_all (List.map get_module_Exports ms)).
      admit.
    Qed.

    Require Import SetoidList.
    Hint Constructors NoDupA.
    Hint Unfold NoDupKey.

    Ltac incl_tran_cons := eapply incl_tran; [ | eassumption ]; intuition.

    Require Import SetFacts.
    
    Notation to_set := SSUF.of_list.
    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap.

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
        Exports linked === linked_exports /\
        Imports linked === linked_imports.
    Proof.
      Opaque make_module.
      induction ms; simpl; intros.
      descend.
      vcgen.
      symmetry; eapply of_list_singleton.
      unfold update_all; simpl.
      eapply to_blm_empty.
      rewrite importsMap_of_list.
      Existing Instance to_blm_Equal_m_Proper.
      rewrite of_list_empty.
      rewrite diff_empty.
      reflexivity.
      eauto.
      simpl in *.
      destruct IHms.
      incl_tran_cons.
      inversion H0; subst; eauto.
      openhyp.

      descend.
      eapply linkOk; eauto.
      eapply make_module_ok; eauto.
      intuition.
      eapply inter_is_empty_iff.
      rewrite H2.
      rewrite of_list_cons.
      eapply Disjoint_union.
      split.
      eapply Disjoint_singletons.
      eapply GoodModule_Name_neq_empty_module_name.
      inversion H0; subst.
      eapply Disjoint_singleton.
      not_not.
      eapply of_list_spec; eauto.
      eapply importsOk_Compat.
      Existing Instance BLMFU3.Compat_m_Proper.
      rewrite H3.
      rewrite make_module_Imports by intuition.
      eapply to_blm_Compat.
      eapply compat_imports_exports; eauto.
      eapply importsOk_Compat.
      rewrite H4.
      rewrite make_module_Exports by intuition.
      eapply to_blm_Compat.
      Existing Instance CompatReflSym_Symmetric.
      symmetry.
      eapply compat_exports_imports; eauto.
      eapply importsOk_Compat.
      rewrite H4.
      rewrite make_module_Imports by intuition.
      eapply to_blm_Compat.
      eapply compat_imports_imports; eauto.
      
      rewrite H2.
      rewrite make_module_Modules by intuition.
      repeat rewrite of_list_cons.
      eapply Equal_Subset_iff; split; subset_solver.
      rewrite XCAP_union_update.
      rewrite update_all_cons.
      rewrite Disjoint_update_sym.
      rewrite to_blm_update.
      eapply BLMF.P.update_m; eauto.
      eapply make_module_Exports; intuition.
      eapply Disjoint_exports; eauto.
      rewrite XCAP_union_update.
      repeat rewrite XCAP_diff_diff.
      rewrite H4.
      rewrite H3.
      rewrite make_module_Imports by intuition.
      rewrite make_module_Exports by intuition.
      repeat rewrite <- to_blm_diff.
      rewrite <- to_blm_update.
      eapply to_blm_Equal.
      change ConvertLabelMap.LMF.P.update with update in *.
      change ConvertLabelMap.LMF.P.diff with diff in *.
      rewrite update_all_cons.
      rewrite diff_update.
      rewrite diff_diff_sym.
      rewrite update_same; reflexivity.
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
