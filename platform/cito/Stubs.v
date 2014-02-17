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

    Definition get_module_impl_Imports (module : GoodModule) := 
      to_map 
        (List.map 
           (Func_to_import module)
           (Functions module)).

    Definition foreign_imports := map StubMake.foreign_spec imports.

    Definition total_exports := update_all (List.map get_module_Exports modules).

    Definition total_impls := update_all (List.map get_module_impl_Imports modules).

    Definition final_imports := update total_impls foreign_imports.

    (* Definition final_imports := map StubMake.foreign_spec imports. *)

    Definition total_imports := update total_exports final_imports.

    Definition do_make_module := make_module modules imports.

    Require Import SetoidList.
    Hint Constructors NoDupA.
    Hint Unfold NoDupKey.

    Ltac incl_tran_cons := eapply incl_tran; [ | eassumption ]; intuition.

    Require Import SetFacts.
    
    Notation to_set := SSUF.of_list.
    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap.

    Existing Instance to_blm_Equal_m_Proper.
    Existing Instance BLMFU3.Compat_m_Proper.
    Existing Instance CompatReflSym_Symmetric.
    Existing Instance CompatReflSym_Reflexive.
    Existing Instance Compat_m_Proper.

    (* some reinterpretation of Bedrock facilities *)

    Lemma importsMap_of_list : forall ls, NoDupKey ls -> importsMap ls === of_list ls.
      admit.
    Qed.

    Lemma exps_spec :
      forall mn (fns : list (function mn)),
        let fns' := List.map (@func_to_import _) fns in
        exps fns === of_list fns'.
      admit.
    Qed.

    Lemma importsOk_Compat : forall m1 m2, importsOk m1 m2 <-> BLMFU3.Compat m1 m2.
      admit.
    Qed.

    Lemma XCAP_union_update : forall elt m1 m2, BLM.Equal (@XCAP.union elt m1 m2) (BLMF.P.update m2 m1).
      unfold XCAP.union.
      unfold BLMF.P.update.
      intros.
      reflexivity.
    Qed.

    Lemma XCAP_diff_diff : forall elt m1 m2, @BLM.Equal elt (XCAP.diff m1 m2) (BLMF.P.diff m1 m2).
      intros.
      unfold BLM.Equal.
      intros.
      eapply option_univalence.
      split; intros.
      eapply BLM.find_2 in H.
      eapply MapsTo_diff in H.
      Focus 2.
      instantiate (1 := empty_module).
      instantiate (1 := empty_module).
      unfold empty_module in *.
      simpl.
      unfold importsMap.
      simpl.
      rewrite BLM.fold_1.
      simpl.
      eauto.
      openhyp.
      eapply BLM.find_1.
      eapply BLMF.P.diff_mapsto_iff.
      eauto.
      eapply BLM.find_2 in H.
      eapply BLMF.P.diff_mapsto_iff in H.
      openhyp.
      eapply BLM.find_1.
      eapply MapsTo_diffr; eauto.
      eapply BLM.elements_3w.
    Qed.

    (* make_module interface *)

    Lemma bexports_Equal_exports : forall m, List.In m modules -> of_list (bexports modules imports m) == get_module_Exports m.
      intros.
      unfold bexports.
      unfold stubs.
      unfold make_stub.
      rewrite map_map.
      unfold func_to_import.
      simpl.
      unfold get_module_Exports.
      reflexivity.
    Qed.
(*
    Lemma bimports_Equal_total_imports : forall m, List.In m modules -> of_list (bimports modules imports m) == total_imports.
(*      intros.
      unfold bimports.
      unfold bimports_base.
      repeat rewrite of_list_app.
      unfold total_imports.
      unfold final_imports.

      Lemma bimports_base_Equal_update_all : of_list (bimports_base modules imports) == update_all (List.map get_module_Exports modules).
        admit.
      Qed.
      rewrite bimports_base_Equal_update_all.
      Lemma imports_Equal_final_imports : of_list (List.map (Func_to_import m) (Functions m)) == final_imports.
*)
      admit.
    Qed.
*)

    Definition module_imports m := total_exports + foreign_imports + get_module_impl_Imports m - get_module_Exports m.

    Lemma make_module_Imports : forall m, List.In m modules -> Imports (do_make_module m) === module_imports m.
(*      intros.
      unfold do_make_module, make_module, bmodule_, Imports.
      rewrite importsMap_of_list.
      eapply to_blm_Equal.
      unfold bimports_diff_bexports.
      rewrite of_list_diff.
      rewrite bimports_Equal_total_imports by eauto.
      rewrite bexports_Equal_exports by eauto.
      reflexivity.
      eapply NoDupKey_bimports; eauto.
      eapply NoDupKey_bexports; eauto.
      eapply diff_NoDupKey.
      eapply NoDupKey_bimports; eauto.*)
      admit.
    Qed.

    Lemma make_module_Exports : forall m, List.In m modules -> Exports (do_make_module m) === get_module_Exports m.
      intros.
      unfold do_make_module, make_module, bmodule_, Imports; simpl.
      rewrite exps_spec.
      eapply to_blm_Equal.
      unfold stubs.
      unfold make_stub.
      rewrite map_map.
      unfold func_to_import.
      simpl.
      unfold get_module_Exports.
      reflexivity.
    Qed.

    Lemma make_module_Modules : forall m, List.In m modules -> SS.Equal (Modules (do_make_module m)) (singleton (MName m)).
      intros.
      unfold do_make_module, make_module, bmodule_, Modules.
      reflexivity.
    Qed.

    Lemma GoodModule_Name_neq_empty_module_name : forall m : GoodModule, MName m <> empty_module_name.
      intros.
      destruct m; simpl in *.
      unfold IsGoodModuleName in *.
      unfold empty_module_name.
      intuition.
      subst.
      simpl in *.
      intuition.
    Qed.



    Lemma MapsTo_exports_module_name : forall m k v, MapsTo k v (get_module_Exports m) -> fst k = MName m.
      unfold get_module_Exports.
      intros.
      eapply MapsTo_In in H.
      eapply In_to_map in H.
      unfold InKey in *.
      rewrite map_map in H.
      simpl in *.
      eapply in_map_iff in H.
      openhyp.
      subst.
      eauto.
    Qed.

    Lemma MName_neq_Disjoint : forall m1 m2, MName m1 <> MName m2 -> Disjoint (get_module_Exports m1) (get_module_Exports m2).
      unfold Disjoint.
      intros.
      not_not.
      openhyp.
      eapply In_MapsTo in H.
      eapply In_MapsTo in H0.
      openhyp.
      eapply MapsTo_exports_module_name in H.
      eapply MapsTo_exports_module_name in H0.
      congruence.
    Qed.

    Lemma NoDup_cons_cons : forall A (x y : A) ls, List.NoDup (x :: y :: ls) -> x <> y.
      intros.
      inversion H.
      not_not.
      subst.
      intuition.
    Qed.

    Lemma NoDup_cons_elim : forall A ls (e : A), List.NoDup (e :: ls) -> forall e', List.In e' ls -> e' <> e.
      induction ls; simpl; intuition.
      subst.
      eapply NoDup_cons_cons in H.
      intuition.
      subst.
      inversion H; subst.
      intuition.
    Qed.

    Lemma Disjoint_exports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Disjoint (get_module_Exports m) (update_all (List.map get_module_Exports ms)).
      induction ms; simpl; intros.
      unfold update_all; simpl.
      eapply Disjoint_empty.
      rewrite update_all_cons.
      eapply Disjoint_update.
      eapply NoDup_cons_cons in H0.
      eapply MName_neq_Disjoint; eauto.
      eapply IHms.
      incl_tran_cons.
      simpl.
      inversion H0; subst.
      inversion H4; subst.
      econstructor; eauto.
      intuition.
    Qed.

    Lemma total_imports_Compat_exports' : forall ms m, List.In m ms -> incl ms modules -> List.NoDup (List.map MName ms) -> Compat (get_module_Exports m) (update_all (List.map get_module_Exports ms)).
      induction ms; simpl; intros.
      intuition.
      openhyp.
      subst.
      rewrite update_all_cons.
      eapply Compat_update.
      econstructor.
      eapply Disjoint_Compat.
      eapply Disjoint_exports; eauto.
      rewrite update_all_cons.
      eapply Compat_update.
      eapply Disjoint_Compat.
      eapply MName_neq_Disjoint.
      eapply NoDup_cons_elim in H1; eauto.
      eapply in_map; eauto.
      eapply IHms; eauto.
      incl_tran_cons.
      inversion H1; subst; eauto.
    Qed.

    Lemma Disjoint_exports_final_imports : forall m, List.In m modules -> Disjoint (get_module_Exports m) final_imports.
      intros.
      unfold imported_module_names in *.
      unfold final_imports.
      unfold Disjoint.
      intros.
      unfold LF.Disjoint in *.
      specialize (NoSelfImport (fst k)).
      not_not.
      openhyp.
      eapply In_MapsTo in H0.
      openhyp.
      eapply MapsTo_exports_module_name in H0.
      rewrite H0 in *.
      unfold module_names.
      split.
      eapply in_map; eauto.
      eapply map_4 in H1.
      eapply In_MapsTo in H1.
      openhyp.
      eapply in_map_iff.
      exists (k, x0).
      split.
      eauto.
      eapply InA_eqke_In.
      eapply elements_1; eauto.
    Qed.

    Lemma total_imports_Compat_exports : forall m, List.In m modules -> Compat total_imports (get_module_Exports m).
      unfold total_imports.
      symmetry.
      eapply Compat_update.
      eapply total_imports_Compat_exports'; eauto.
      intuition.
      eapply Disjoint_Compat.
      eapply Disjoint_exports_final_imports; eauto.
    Qed.

    Lemma total_imports_Compat_many_exports : forall ms, incl ms modules -> Compat total_imports (update_all (List.map get_module_Exports ms)).
      intros.
      eapply Compat_update_all.
      eapply Forall_forall.
      intros.
      eapply in_map_iff in H0.
      openhyp.
      subst.
      eapply total_imports_Compat_exports.
      intuition.
    Qed.

    Lemma compat_imports_exports : forall ms m, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (diff total_imports (get_module_Exports m)) (update_all (List.map get_module_Exports ms)).
      intros.
      eapply Compat_diff.
      eapply total_imports_Compat_many_exports.
      incl_tran_cons.
    Qed.

    Lemma compat_exports_imports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (get_module_Exports m) (diff total_imports (update_all (List.map get_module_Exports ms))).
      intros.
      symmetry.
      eapply Compat_diff.
      eapply total_imports_Compat_exports.
      intuition.
    Qed.

    Lemma compat_imports_imports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (diff total_imports (get_module_Exports m)) (diff total_imports (update_all (List.map get_module_Exports ms))).
      intros.
      eapply Compat_diff.
      symmetry.
      eapply Compat_diff.
      reflexivity.
    Qed.

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
      rewrite H3.
      rewrite make_module_Imports by intuition.
      eapply to_blm_Compat.
      eapply compat_imports_exports; eauto.
      eapply importsOk_Compat.
      rewrite H4.
      rewrite make_module_Exports by intuition.
      eapply to_blm_Compat.
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
