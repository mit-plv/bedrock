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
  Require Import GeneralTactics2.
  Require Import StringFacts2.

  Require Import LinkModuleImpls.
  Module Import LinkModuleImplsMake := Make E M.
  Require Import Stubs.
  Module Import StubsMake := Make E M.
  Require Import Stub.
  Import StubMake.
  Require Import CompileFuncSpec.
  Import CompileFuncSpecMake.
  Require Import Inv.
  Import InvMake.
  Require Import Semantics.
  Import SemanticsMake.
  Import InvMake2.
  Require Import GoodOptimizer.
  Module Import GoodOptimizerMake := Make E.

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

  Require Import ListFacts3.

  Module Import SS := StringSet.StringSet.
  Module Import SSF := StringSet.StringFacts.
  Module SSK := StringSet.StringKey.
  Require Import FSetFacts1.
  Module SSK_as_UDT := Make_UDT SSK.
  Module Import SSUF := UWFacts_fun SSK_as_UDT SS.

  Import LM.
  Import LMF.P.
  Import F.

  Section TopSection.

    (* modules to be linked *)
    Variable modules : list GoodModule.

    Hypothesis ModulesNotEmpty : modules <> nil.

    Hypothesis NoDupModuleNames : List.NoDup (module_names modules).

    (* imported specs *)
    Variable imports : t ForeignFuncSpec.

    Hypothesis NoSelfImport : LF.Disjoint (module_names modules) (imported_module_names imports).

    Hypotheses ImportsGoodModuleName : forall l, In l imports -> IsGoodModuleName (fst l).

    (* optimizer *)

    Variable optimizer : Optimizer.

    Hypothesis IsGoodOptimizer : GoodOptimizer optimizer.

    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap.
    Notation to_set := SSUF.P.of_list.

    Hint Extern 1 => reflexivity.

    Require Import Setoid.
    Existing Instance to_blm_Equal_m_Proper.
    Existing Instance CompatReflSym_Symmetric.
    Existing Instance CompatReflSym_Reflexive.
    Existing Instance Compat_m_Proper.
    Existing Instance Disjoint_m_Symmetric.
    Existing Instance BLMFU3.Compat_m_Proper.

    Lemma total_impls_Equal_total_exports : total_impls modules == LinkModuleImplsMake.total_exports modules.
      eauto.
    Qed.

    Lemma Disjoint_MNames_impl_MNames : SSUF.Disjoint (to_set (List.map impl_MName modules)) (to_set (List.map MName modules)).
      unfold SSUF.Disjoint.
      intros.
      nintro.
      openhyp.
      eapply of_list_spec in H.
      eapply of_list_spec in H0.
      eapply in_map_iff in H; openhyp; subst.
      eapply in_map_iff in H0; openhyp; subst.
      unfold impl_MName in *.
      eapply IsGoodModuleName_not_impl_module_name.
      eapply GoodModule_GoodName.
      eexists; eauto.
    Qed.

    Lemma final_imports_Compat_total_exports : Compat (final_imports modules imports) (LinkModuleImplsMake.total_exports modules).
      unfold final_imports.
      rewrite <- total_impls_Equal_total_exports.
      symmetry.
      eapply Compat_update.
      eapply Disjoint_Compat.
      symmetry.
      eapply foreign_imports_Disjoint_total_impls; eauto.
      eauto.
    Qed.

    Lemma final_imports_diff_total_exports : final_imports modules imports - LinkModuleImplsMake.total_exports modules == foreign_imports imports.
      unfold final_imports.
      rewrite <- total_impls_Equal_total_exports.
      rewrite <- update_diff_same.
      rewrite diff_same.
      rewrite update_empty_2.
      eapply Disjoint_diff_no_effect.
      eapply foreign_imports_Disjoint_total_impls; eauto.
    Qed.

    Definition impls := LinkModuleImplsMake.m modules IsGoodOptimizer.

    Definition stubs := StubsMake.m modules imports.

    Definition output := link impls stubs.

    (* Interface *)

    Theorem output_ok : moduleOk output.
      unfold output.
      eapply linkOk.
      eapply LinkModuleImplsMake.module_ok; eauto.
      eapply StubsMake.module_ok; eauto.
      eapply inter_is_empty_iff.
      unfold impls.
      rewrite LinkModuleImplsMake.module_module_names; eauto.
      unfold stubs.
      rewrite StubsMake.module_module_names; eauto.
      unfold module_names.
      eapply Disjoint_MNames_impl_MNames.
      eapply importsOk_Compat.
      unfold impls.
      rewrite LinkModuleImplsMake.module_imports; eauto.
      unfold stubs.
      rewrite StubsMake.module_exports; eauto.
      eapply to_blm_Compat.
      symmetry.
      eapply Compat_empty.
      eapply importsOk_Compat.
      unfold impls.
      rewrite LinkModuleImplsMake.module_exports; eauto.
      unfold stubs.
      rewrite StubsMake.module_imports; eauto.
      eapply to_blm_Compat.
      eapply final_imports_Compat_total_exports.
      eapply importsOk_Compat.
      unfold impls.
      rewrite LinkModuleImplsMake.module_imports; eauto.
      unfold stubs.
      rewrite StubsMake.module_imports; eauto.
      eapply to_blm_Compat.
      symmetry.
      eapply Compat_empty.
    Qed.

    Theorem output_imports : Imports output === foreign_imports imports.
      simpl.
      rewrite XCAP_union_update.
      repeat rewrite XCAP_diff_diff.
      unfold impls.
      rewrite LinkModuleImplsMake.module_imports; eauto.
      rewrite LinkModuleImplsMake.module_exports; eauto.
      unfold stubs.
      rewrite StubsMake.module_imports; eauto.
      rewrite StubsMake.module_exports; eauto.
      repeat rewrite <- to_blm_diff.
      rewrite <- to_blm_update.
      eapply to_blm_Equal.
      change ConvertLabelMap.LMF.P.update with update in *.
      change ConvertLabelMap.LMF.P.diff with diff in *.
      repeat rewrite empty_diff.
      rewrite update_empty_2.
      eapply final_imports_diff_total_exports.
    Qed.

    Theorem output_exports : Exports output === total_exports modules imports + LinkModuleImplsMake.total_exports modules.
      simpl.
      rewrite XCAP_union_update.
      unfold impls.
      rewrite LinkModuleImplsMake.module_exports; eauto.
      unfold stubs.
      rewrite StubsMake.module_exports; eauto.
      rewrite <- to_blm_update.
      eapply to_blm_Equal.
      eauto.
    Qed.

    Theorem output_module_names : SS.Equal (Modules output) (union (to_set (List.map impl_MName modules)) (to_set (List.map MName modules))).
      simpl.
      unfold impls.
      rewrite LinkModuleImplsMake.module_module_names; eauto.
      unfold stubs.
      rewrite StubsMake.module_module_names; eauto.
    Qed.

  End TopSection.

End Make.