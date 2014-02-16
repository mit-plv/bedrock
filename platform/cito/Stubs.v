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
    
    Require Import SetUtil.

    Definition to_bl_pair elt (p : label * elt) := (fst p : Labels.label, snd p).

    Definition to_blm elt m := BLMF.to_map (List.map (@to_bl_pair _) (@elements elt m)).

    Infix "==" := Equal.
    Notation "{}" := (@empty _).

    Notation "m1 === m2" := (BLM.Equal m1 (to_blm m2)) (at level 70).

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
        Exports linked === linked_exports /\
        Imports linked === linked_imports.
      Proof.
        Opaque make_module.
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
        Lemma Equal2_empty : forall elt, BLM.empty elt === {}.
          admit.
        Qed.
        eapply Equal2_empty.
        Lemma Equal2_importsMap : forall ls, NoDupKey ls -> importsMap ls === to_map ls.
          admit.
        Qed.

        Lemma Equal2_Equal : forall elt ls1 ls2 ls2', ls1 === ls2 -> @Equal elt ls2' ls2 -> ls1 === ls2'.
          admit.
        Qed.

        eapply Equal2_Equal.
        eapply Equal2_importsMap.
        Require Import SetoidList.
        Hint Constructors NoDupA.
        Hint Unfold NoDupKey.

        eauto.
        Lemma to_map_empty : forall elt, @to_map elt [] == {}.
          admit.
        Qed.
        
        rewrite to_map_empty.
        unfold update_all; simpl.
        Lemma diff_empty : forall elt m, @diff elt m {} == {}.
          admit.
        Qed.
        eapply diff_empty.

        Ltac incl_tran_cons := eapply incl_tran; [ | eassumption ]; intuition.
        simpl in *.
        destruct IHms.
        incl_tran_cons.
        inversion H0; subst; eauto.
        openhyp.

        descend.
        eapply linkOk; eauto.
        eapply make_module_ok; eauto.
        intuition.
        Lemma inter_is_empty_iff : forall s1 s2, SS.is_empty (inter s1 s2) = true <-> disjoint s1 s2.
          admit.
        Qed.
        simpl.
        eapply inter_is_empty_iff.
        Add Morphism disjoint with signature SS.Equal ==> SS.Equal ==> iff as disjoint_m.
          admit.
        Qed.
        rewrite H2.
        Lemma to_set_cons : forall e ls, SS.Equal (to_set (e :: ls)) (union (singleton e) (to_set ls)).
          admit.
        Qed.
        rewrite to_set_cons.
        Lemma disjoint_union : forall s1 s2 s3, disjoint s1 (union s2 s3) <-> (disjoint s1 s2 /\ disjoint s1 s3).
          admit.
        Qed.
        eapply disjoint_union.
        split.
        Lemma disjoint_singletons : forall e1 e2, disjoint (singleton e1) (singleton e2) <-> e1 <> e2.
          admit.
        Qed.
        eapply disjoint_singletons.
        Lemma GoodModule_Name_neq_empty_module_name : forall m : GoodModule, MName m <> empty_module_name.
          admit.
        Qed.
        eapply GoodModule_Name_neq_empty_module_name.
        inversion H0; subst.
        Lemma disjoint_singleton : forall e s, disjoint (singleton e) s <-> ~ SS.In e s.
          admit.
        Qed.
        eapply disjoint_singleton.
        not_not.
        Lemma to_set_spec : forall e ls, SS.In e (to_set ls) <-> List.In e ls.
          admit.
        Qed.
        eapply to_set_spec; eauto.
        Definition BLM_Compat elt m1 m2 := forall k, @BLM.In elt k m1 -> BLM.In k m2 -> BLM.find k m1 = BLM.find k m2.
        Lemma importsOk_BLM_Compat : forall m1 m2, importsOk m1 m2 <-> BLM_Compat m1 m2.
          admit.
        Qed.
        eapply importsOk_BLM_Compat.
        Add Parametric Morphism elt : (@BLM_Compat elt)
            with signature BLM.Equal ==> BLM.Equal ==> iff as BLM_Compat_m.
          admit.
        Qed.
        rewrite H3.
        Lemma make_module_Imports : forall m, List.In m modules -> Imports (do_make_module m) === diff total_imports (get_module_Exports m).
          admit.
        Qed.
        rewrite make_module_Imports by intuition.
        Definition Compat elt m1 m2 := forall k, @In elt k m1 -> In k m2 -> find k m1 = find k m2.
        Lemma BLM_Compat_Compat : forall elt m1 m2, @BLM_Compat elt (to_blm m1) (to_blm m2) <-> Compat m1 m2.
          admit.
        Qed.
        eapply BLM_Compat_Compat.
        Lemma compat_imports_exports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (diff total_imports (get_module_Exports m)) (update_all (List.map get_module_Exports ms)).
          admit.
        Qed.
        eapply compat_imports_exports; eauto.
        eapply importsOk_BLM_Compat.
        rewrite H4.
        Lemma make_module_Exports : forall m, List.In m modules -> Exports (do_make_module m) === get_module_Exports m.
          admit.
        Qed.
        rewrite make_module_Exports by intuition.
        eapply BLM_Compat_Compat.
        Lemma Compat_sym : forall elt m1 m2, @Compat elt m1 m2 -> Compat m2 m1.
          admit.
        Qed.
        Lemma Compat_refl : forall elt m, @Compat elt m m.
          admit.
        Qed.
        Add Parametric Relation (elt : Type) : (t elt) (@Compat elt)
            reflexivity proved by (@Compat_refl elt)
            symmetry proved by (@Compat_sym elt)
              as CompatReflSym.

        symmetry.
        Lemma compat_exports_imports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (get_module_Exports m) (diff total_imports (update_all (List.map get_module_Exports ms))).
          admit.
        Qed.
        eapply compat_exports_imports; eauto.
        eapply importsOk_BLM_Compat.
        rewrite H4.
        rewrite make_module_Imports by intuition.
        eapply BLM_Compat_Compat.
        Lemma compat_imports_imports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (diff total_imports (get_module_Exports m)) (diff total_imports (update_all (List.map get_module_Exports ms))).
          admit.
        Qed.
        eapply compat_imports_imports; eauto.
        
        rewrite H2.
        Lemma make_module_Modules : forall m, List.In m modules -> SS.Equal (Modules (do_make_module m)) (singleton (MName m)).
          admit.
        Qed.
        rewrite make_module_Modules by intuition.
        repeat rewrite to_set_cons.
        Require Import SetFacts.
        Lemma Equal_Subset_iff : forall s1 s2, SS.Equal s1 s2 <-> (SS.Subset s1 s2 /\ SS.Subset s2 s1).
          admit.
        Qed.
        eapply Equal_Subset_iff; split; subset_solver.
        Lemma union_update : forall elt m1 m2, BLM.Equal (@XCAP.union elt m1 m2) (BLMF.P.update m2 m1).
          admit.
        Qed.
        rewrite union_update.
        Lemma update_all_cons : forall elt m ms, @update_all elt (m :: ms) == update m (update_all ms).
          admit.
        Qed.
        Add Parametric Morphism elt : (@to_blm elt)
            with signature Equal ==> BLM.Equal as Equal_m.
          admit.
        Qed.
        rewrite update_all_cons.
        Lemma Disjoint_update_sym : forall elt m1 m2, @Disjoint elt m1 m2 -> update m1 m2 == update m2 m1.
          admit.
        Qed.
        rewrite Disjoint_update_sym.
        Lemma to_blm_update : forall elt m1 m2, @BLM.Equal elt (to_blm (update m1 m2)) (BLMF.P.update (to_blm m1) (to_blm m2)).
          admit.
        Qed.
        rewrite to_blm_update.
        eapply BLMF.P.update_m; eauto.
        eapply make_module_Exports; intuition.
        Lemma Disjoint_exports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Disjoint (get_module_Exports m) (update_all (List.map get_module_Exports ms)).
          admit.
        Qed.
        eapply Disjoint_exports; eauto.
        rewrite union_update.
        Lemma XCAP_diff_diff : forall elt m1 m2, @BLM.Equal elt (XCAP.diff m1 m2) (BLMF.P.diff m1 m2).
          admit.
        Qed.
        repeat rewrite XCAP_diff_diff.
        rewrite H4.
        rewrite H3.
        rewrite make_module_Imports by intuition.
        rewrite make_module_Exports by intuition.
        Lemma to_blm_diff : forall elt m1 m2, @BLM.Equal elt (to_blm (diff m1 m2)) (BLMF.P.diff (to_blm m1) (to_blm m2)).
          admit.
        Qed.
        repeat rewrite <- to_blm_diff.
        rewrite <- to_blm_update.
        Lemma to_blm_spec : forall elt m1 m2, @BLM.Equal elt (to_blm m1) (to_blm m2) <-> m1 == m2.
          admit.
        Qed.
        eapply to_blm_spec.
        Infix "-" := diff.
        Infix "+" := update.
        rewrite update_all_cons.
        Lemma diff_update : forall elt (m1 m2 m3 : t elt), m1 - (m2 + m3) == m1 - m2 - m3.
          admit.
        Qed.
        rewrite diff_update.
        Lemma diff_diff_sym : forall elt (m1 m2 m3 : t elt), m1 - m2 - m3 == m1 - m3 - m2.
          admit.
        Qed.
        rewrite diff_diff_sym.
        Lemma update_same : forall elt (m1 m2 : t elt), m1 == m2 -> m1 + m2 == m1.
          admit.
        Qed.
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
