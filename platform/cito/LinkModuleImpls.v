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
  Require Import StringFacts.

  Require Import CompileModule.
  Module Import CompileModuleMake := Make E M.
  Require Import CompileFuncSpec.
  Import CompileFuncMake.
  Import CompileFuncImplMake.
  Import CompileFuncSpecMake.
  Require Import Inv.
  Import InvMake.
  Require Import Semantics.
  Import SemanticsMake.
  Import InvMake2.
  Require Import GoodOptimizer.
  Import GoodOptimizerMake.

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
  Import P.
  Import F.

  Section TopSection.

    (* modules to be linked *)
    Variable modules : list GoodModule.

    Hypothesis ModulesNotEmpty : modules <> nil.

    Definition FName := SyntaxFunc.Name.

    Definition MName := GoodModule.Name.

    Hypothesis NoDupModuleNames : List.NoDup (List.map MName modules).

    Variable optimizer : Optimizer.

    Hypothesis IsGoodOptimizer : GoodOptimizer optimizer.

    (* Since modules <> nil, dummy will never be used. *)
    Definition dummy := @StructuredModule.bmodule_ nil "" nil.

    Definition link_all ls := fold_right_2 link dummy ls.

    Definition compile m := CompileModuleMake.compile m IsGoodOptimizer.

    Definition impl_label mod_name f_name : label := (impl_module_name mod_name, f_name).

    Definition Func_to_import m (f : GoodFunction) := (impl_label (MName m) (FName f), CompileFuncSpecMake.spec f).

    Definition get_module_Exports (module : GoodModule) := 
      to_map 
        (List.map 
           (Func_to_import module)
           (Functions module)).

    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap.
    Notation to_set := SSUF.of_list.

    Hint Extern 1 => reflexivity.

    Definition impl_MName m := impl_module_name (MName m).

    Existing Instance to_blm_Equal_m_Proper.
    Existing Instance CompatReflSym_Symmetric.
    Existing Instance CompatReflSym_Reflexive.
    Existing Instance Compat_m_Proper.
    Existing Instance Disjoint_m_Symmetric.
    Existing Instance BLMFU3.Compat_m_Proper.

    Require Import SetoidList.
    Hint Constructors NoDupA.
    Hint Unfold NoDupKey.

    Lemma compile_module_Imports : forall m, Imports (compile m) === {}.
        intros.
        unfold compile, CompileModuleMake.compile.
        unfold compiled_funcs, bmodule_, Imports.
        unfold imports.
        rewrite importsMap_of_list.
        eapply to_blm_Equal.
        eauto.
        econstructor.
    Qed.

    Lemma compile_module_Exports : forall m, Exports (compile m) === get_module_Exports m.
        intros.
        unfold compile, CompileModuleMake.compile.
        unfold compiled_funcs, bmodule_; simpl.
        rewrite exps_spec.
        eapply to_blm_Equal.
        rewrite map_map.
        unfold func_to_import, compile_func; simpl in *.
        unfold mod_name.
        reflexivity.
    Qed.

    Lemma compile_module_Modules : forall m, SS.Equal (Modules (compile m)) (singleton (impl_MName m)).
      intros.
      unfold compile, CompileModuleMake.compile; simpl.
      unfold mod_name.
      unfold impl_MName.
      eauto.
    Qed.

    Ltac incl_tran_cons := eapply incl_tran; [ | eassumption ]; intuition.

    Require Import SetFacts.

    Lemma In_exports_module_name : forall k m, In k (get_module_Exports m) -> fst k = impl_MName m.
      unfold get_module_Exports.
      intros.
      eapply In_to_map in H.
      unfold InKey in *.
      rewrite map_map in H.
      simpl in *.
      eapply in_map_iff in H.
      openhyp.
      subst.
      eauto.
    Qed.

    Lemma impl_MName_neq_Disjoint : forall m1 m2, impl_MName m1 <> impl_MName m2 -> Disjoint (get_module_Exports m1) (get_module_Exports m2).
      unfold Disjoint.
      intros.
      not_not.
      openhyp.
      eapply In_exports_module_name in H.
      eapply In_exports_module_name in H0.
      congruence.
    Qed.

    Lemma Disjoint_exports_many_exports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map impl_MName (m :: ms)) -> Disjoint (get_module_Exports m) (update_all (List.map get_module_Exports ms)).
      induction ms; simpl; intros.
      rewrite update_all_nil.
      eapply Disjoint_empty.
      rewrite update_all_cons.
      eapply Disjoint_update.
      eapply NoDup_cons_cons in H0.
      eapply impl_MName_neq_Disjoint; eauto.
      eapply IHms.
      incl_tran_cons.
      simpl.
      inversion H0; subst.
      inversion H4; subst.
      econstructor; eauto.
      intuition.
    Qed.

    Lemma NoDup_MName_NoDup_impl_Name : forall ms, List.NoDup (List.map MName ms) -> List.NoDup (List.map impl_MName modules).
      intros.
      unfold impl_MName.
      rewrite <- map_map.
      eapply Injection_NoDup; eauto.
      unfold IsInjection.
      intros.
      not_not.
      unfold impl_module_name in *.
      eapply append_inj_2; eauto.
    Qed.

    Lemma link_all_ok : 
      forall (ms : list GoodModule), 
        let linked := link_all (List.map compile ms) in
        let module_names := List.map impl_MName ms in
        let linked_module_names := to_set module_names in
        let linked_exports := update_all (List.map get_module_Exports ms) in
        let linked_imports := {} in
        ms <> nil ->
        incl ms modules ->
        List.NoDup module_names ->
        moduleOk linked /\
        SS.Equal (Modules linked) linked_module_names /\
        Exports linked === linked_exports /\
        Imports linked === linked_imports.
    Proof.
      Opaque CompileModuleMake.compile.
      unfold link_all.
      induction ms; simpl; intros.
      intuition.
      destruct ms; simpl in *.

      descend.
      eapply CompileModuleMake.compileOk.
      rewrite of_list_singleton.
      rewrite compile_module_Modules.
      eauto.
      rewrite compile_module_Exports.
      rewrite update_all_single.
      eauto.
      rewrite compile_module_Imports.
      eauto.

      simpl in *.
      destruct IHms.
      intuition.
      incl_tran_cons.
      inversion H1; subst; eauto.
      openhyp.

      descend.
      eapply linkOk.
      eapply CompileModuleMake.compileOk.
      eapply H2.

      eapply inter_is_empty_iff.
      rewrite H3.
      rewrite of_list_cons.
      rewrite compile_module_Modules.
      eapply Disjoint_union.
      split.
      eapply Disjoint_singletons.
      eapply NoDup_cons_cons.
      eauto.
      eapply Disjoint_singleton.
      inversion H1; subst.
      not_not.
      eapply of_list_spec in H6.
      intuition.

      eapply importsOk_Compat.
      rewrite H4.
      rewrite compile_module_Imports.
      eapply to_blm_Compat.
      symmetry.
      eapply Compat_empty.
      eapply importsOk_Compat.
      rewrite H5.
      rewrite compile_module_Exports.
      eapply to_blm_Compat.
      symmetry.
      eapply Compat_empty.
      eapply importsOk_Compat.
      rewrite H5.
      rewrite compile_module_Imports.
      eapply to_blm_Compat.
      eapply Compat_empty.
      
      rewrite H3.
      rewrite compile_module_Modules.
      repeat rewrite of_list_cons.
      eapply Equal_Subset_iff; split; subset_solver.
      rewrite XCAP_union_update.
      rewrite H4.
      repeat rewrite update_all_cons.
      set (_ + update_all _).
      rewrite Disjoint_update_sym.
      rewrite to_blm_update.
      eapply BLMF.P.update_m; eauto.
      eapply compile_module_Exports.
      unfold t0; clear t0.
      rewrite <- update_all_cons.
      eapply Disjoint_exports_many_exports with (ms := g :: ms); eauto.
      rewrite XCAP_union_update.
      repeat rewrite XCAP_diff_diff.
      rewrite H5.
      rewrite H4.
      rewrite compile_module_Imports.
      rewrite compile_module_Exports.
      repeat rewrite <- to_blm_diff.
      rewrite <- to_blm_update.
      eapply to_blm_Equal.
      change ConvertLabelMap.LMF.P.update with update in *.
      change ConvertLabelMap.LMF.P.diff with diff in *.
      repeat rewrite empty_diff; eauto.
    Qed.

    Definition ms := List.map compile modules.

    Definition m := link_all ms.

    (* Interface *)

    Theorem module_ok : moduleOk m.
      unfold m.
      unfold ms.
      eapply link_all_ok; intuition.
      eapply NoDup_MName_NoDup_impl_Name; eauto.
    Qed.

    Theorem module_imports : Imports m === {}.
      edestruct link_all_ok; eauto.
      intuition.
      eapply NoDup_MName_NoDup_impl_Name; eauto.
      openhyp.
      eauto.
    Qed.

    Definition total_exports := update_all (List.map get_module_Exports modules).

    Theorem module_exports : Exports m === total_exports.
      edestruct link_all_ok; eauto.
      intuition.
      eapply NoDup_MName_NoDup_impl_Name; eauto.
      openhyp.
      unfold m.
      rewrite H1.
      eapply to_blm_Equal.
      eauto.
    Qed.

    Theorem module_module_names : SS.Equal (Modules m) (to_set (List.map impl_MName modules)).
      edestruct link_all_ok; eauto.
      intuition.
      eapply NoDup_MName_NoDup_impl_Name; eauto.
      openhyp.
      unfold m.
      rewrite H0.
      eauto.
    Qed.

  End TopSection.

End Make.
