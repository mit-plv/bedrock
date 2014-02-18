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
    
    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap.

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

    Definition total_exports := update_all (List.map get_module_Exports modules).

    Definition foreign_imports := map StubMake.foreign_spec imports.

    Definition get_module_Imports m := total_exports + foreign_imports + get_module_impl_Imports m - get_module_Exports m.

    Definition total_impls := update_all (List.map get_module_impl_Imports modules).

    Definition final_imports := update total_impls foreign_imports.

    Definition total_imports := update total_exports final_imports.

    Definition do_make_module := make_module modules imports.

    Require Import SetoidList.
    Hint Constructors NoDupA.
    Hint Unfold NoDupKey.

    Ltac incl_tran_cons := eapply incl_tran; [ | eassumption ]; intuition.

    Require Import SetFacts.
    
    Notation to_set := SSUF.of_list.

    Existing Instance to_blm_Equal_m_Proper.
    Existing Instance BLMFU3.Compat_m_Proper.
    Existing Instance CompatReflSym_Symmetric.
    Existing Instance CompatReflSym_Reflexive.
    Existing Instance Compat_m_Proper.

    Lemma Disjoint_diff_update_comm : forall elt m1 m2 m3, @Disjoint elt m2 m3 -> m1 - m2 + m3 = m1 + m3 - m2.
      admit.
    Qed.

    Lemma update_diff_same : forall elt (m1 m2 m3 : t elt), m1 - m3 + (m2 - m3) = m1 + m2 - m3.
      admit.
    Qed.

    Lemma Compat_update_sym : forall elt m1 m2, @Compat elt m1 m2 -> m1 + m2 = m2 + m1.
      admit.
    Qed.

    Lemma Disjoint_diff : forall elt m1 m2 m3, @Disjoint elt m1 m2 -> Disjoint m1 (m2 - m3).
      admit.
    Qed.

    Lemma Disjoint_after_diff : forall elt m1 m2, @Disjoint elt (m1 - m2) m2.
      admit.
    Qed.

    Add Parametric Relation elt : (t elt) (@Disjoint elt)
        symmetry proved by (@Disjoint_sym elt)
          as Disjoint_m.

    Lemma to_blm_spec : forall elt (k : label) m, @BLM.find elt (k : Labels.label) (to_blm m) = find k m.
      admit.
    Qed.

    Lemma to_blm_no_local : forall elt s1 s2 m, @BLM.find elt (s1, Local s2) (to_blm m) = None.
      admit.
    Qed.

    Lemma app_all_update_all : forall elt lsls, @NoDupKey elt (app_all lsls) -> of_list (app_all lsls) == update_all (List.map (@of_list _) lsls).
      admit.
    Qed.

    Lemma map_update_all_comm : forall elt B (f : elt -> B) ms, map f (update_all ms) == update_all (List.map (map f) ms).
      admit.
    Qed.

    Lemma update_all_Equal : forall elt ms1 ms2, List.Forall2 Equal ms1 ms2 -> @update_all elt ms1 == update_all ms2.
      admit.
    Qed.

    Lemma Forall2_map : forall A B (f1 f2 : A -> B) R ls, pointwise_relation _ R f1 f2 -> Forall2 R (List.map f1 ls) (List.map f2 ls).
      admit.
    Qed.

    Lemma map_of_list : forall elt B (f : elt -> B) ls, map f (of_list ls) == of_list (List.map (fun p => (fst p, f (snd p))) ls).
      admit.
    Qed.

    (* some reinterpretation of Bedrock facilities *)

    Lemma importsMap_of_list : forall ls, NoDupKey ls -> importsMap ls === of_list ls.
      intros.
      unfold BLM.Equal.
      intros.
      change ConvertLabelMap.BLM.find with LabelMap.LabelMap.find in *.
      destruct y.
      destruct l.
      specialize importsMap_spec; intros.
      unfold to_bedrock_label in *.
      erewrite H0 with (k := (s, s0)); eauto.
      change StructuredModuleFacts.LMF.find_list with find_list in *.
      unfold find_list.
      rewrite <- of_list_1b; eauto.
      symmetry.
      rewrite <- to_blm_spec; eauto.
      specialize importsMapGlobal; intros.
      unfold importsGlobal in *.
      eapply option_univalence.
      split; intros.
      eapply BLM.find_2 in H1.
      eapply H0 in H1.
      openhyp.
      simpl in *.
      discriminate.
      rewrite to_blm_no_local in H1.
      discriminate.
    Qed.

    Lemma to_blm_add : forall elt (k : label) v m, @BLM.Equal elt (to_blm (add k v m)) (BLM.add (k : Labels.label) v (to_blm m)).
      admit.
    Qed.

    Lemma exps_spec :
      forall mn (fns : list (function mn)),
        let fns' := List.map (@func_to_import _) fns in
        exps fns === of_list fns'.
      induction fns; simpl; intros.
      eapply to_blm_empty.
      simpl in *.
      destruct a; simpl in *.
      destruct p; simpl in *.
      unfold uncurry; simpl in *.
      rewrite IHfns.
      rewrite to_blm_add.
      eapply BLMF.P.F.add_m; eauto.
      reflexivity.
    Qed.

    Lemma importsOk_Compat_left : forall m1 m2, importsOk m1 m2 -> BLMFU3.Compat m1 m2.
      intros.
      unfold BLMFU3.Compat.
      intros.
      eapply BLMFU3.In_MapsTo in H0.
      openhyp.
      eapply BLMFU3.In_MapsTo in H1.
      openhyp.
      assert (x = x0).
      eapply use_importsOk; eauto.
      eapply BLM.find_1; eauto.
      subst.
      eapply BLM.find_1 in H1.
      eapply BLM.find_1 in H0.
      congruence.
    Qed.

    Lemma importsOk_f_Proper : 
      forall m,
        Proper (Logic.eq ==> Logic.eq ==> iff ==> iff)
               (fun (l : LabelMap.LabelMap.key) (pre : assert) (P : Prop) =>
                  match LabelMap.LabelMap.find (elt:=assert) l m with
                    | Some pre' => pre = pre' /\ P
                    | None => P
                  end).
      intros.
      unfold Proper.
      unfold respectful.
      intros.
      subst.
      destruct (BLM.find y m); intuition.
    Qed.

    Lemma importsOk_f_transpose_neqkey :
      forall m,
        BLMF.P.transpose_neqkey 
          iff
          (fun (l : LabelMap.LabelMap.key) (pre : assert) (P : Prop) =>
             match LabelMap.LabelMap.find (elt:=assert) l m with
               | Some pre' => pre = pre' /\ P
               | None => P
             end).
      unfold BLMF.P.transpose_neqkey.
      intros.
      destruct (BLM.find k m); destruct (BLM.find k' m); intuition.
    Qed.

    Add Morphism importsOk
        with signature BLM.Equal ==> Logic.eq ==> iff as importsOk_m.
      intros.
      unfold importsOk.
      eapply BLMF.P.fold_Equal; eauto.
      intuition.
      eapply importsOk_f_Proper.
      eapply importsOk_f_transpose_neqkey.
    Qed.

    Lemma Compat_add_not_In : forall elt k (v : elt) m1 m2, BLMFU3.Compat (BLM.add k v m1) m2 -> ~ BLM.In k m1 -> BLMFU3.Compat m1 m2.
      intros.
      unfold BLMFU3.Compat in *.
      intros.
      erewrite <- H; eauto.
      rewrite BLMF.P.F.add_neq_o; eauto.
      not_not.
      subst; eauto.
      eapply BLMF.P.F.add_in_iff; eauto.
    Qed.

    Lemma Compat_eq : forall elt k (v1 v2 : elt) m1 m2, BLMFU3.Compat m1 m2 -> BLM.find k m1 = Some v1 -> BLM.find k m2 = Some v2 -> v1 = v2.
      intros.
      unfold BLMFU3.Compat in *.
      erewrite H in H0.
      congruence.
      eapply BLM.find_2 in H0.
      eapply BLMF.MapsTo_In; eauto.
      eapply BLM.find_2 in H1.
      eapply BLMF.MapsTo_In; eauto.
    Qed.

    Lemma importsOk_Compat_right : forall m1 m2, BLMFU3.Compat m1 m2 -> importsOk m1 m2.
      induction m1 using BLMF.P.map_induction_bis.
      intros.
      rewrite <- H in H0.
      rewrite <- H.
      eauto.
      intros.
      unfold importsOk.
      rewrite BLM.fold_1.
      simpl.
      eauto.
      intros.
      unfold importsOk.
      rewrite BLMF.P.fold_add; eauto.
      destruct (option_dec (BLM.find (elt:=assert) x m2)).
      destruct s.
      rewrite e0.
      split.
      eapply Compat_eq; eauto.
      eapply BLM.find_1.
      eapply BLMF.P.F.add_mapsto_iff.
      eauto.
      eapply IHm1.
      eapply Compat_add_not_In; eauto.
      rewrite e0.
      eapply IHm1.
      eapply Compat_add_not_In; eauto.
      intuition.
      eapply importsOk_f_Proper.
      eapply importsOk_f_transpose_neqkey.
    Qed.

    Lemma importsOk_Compat : forall m1 m2, importsOk m1 m2 <-> BLMFU3.Compat m1 m2.
      split; intros.
      eapply importsOk_Compat_left; eauto.
      eapply importsOk_Compat_right; eauto.
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



    Lemma In_exports_module_name : forall k m, In k (get_module_Exports m) -> fst k = MName m.
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

    Lemma MName_neq_Disjoint : forall m1 m2, MName m1 <> MName m2 -> Disjoint (get_module_Exports m1) (get_module_Exports m2).
      unfold Disjoint.
      intros.
      not_not.
      openhyp.
      eapply In_exports_module_name in H.
      eapply In_exports_module_name in H0.
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

    Lemma Compat_exports_many_exports : forall ms m, List.In m ms -> incl ms modules -> List.NoDup (List.map MName ms) -> Compat (get_module_Exports m) (update_all (List.map get_module_Exports ms)).
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

    Lemma Disjoint_exports_foreign_imports : forall m, List.In m modules -> Disjoint (get_module_Exports m) foreign_imports.
      intros.
      unfold imported_module_names in *.
      unfold foreign_imports.
      unfold Disjoint.
      intros.
      unfold LF.Disjoint in *.
      specialize (NoSelfImport (fst k)).
      not_not.
      openhyp.
      eapply In_exports_module_name in H0.
      rewrite H0 in *.
      unfold module_names.
      split.
      eapply in_map; eauto.
      eapply map_4 in H1.
      eapply In_MapsTo in H1.
      openhyp.
      eapply in_map_iff.
      exists (k, x).
      split.
      eauto.
      eapply InA_eqke_In.
      eapply elements_1; eauto.
    Qed.

    Lemma Compat_exports_foreign_imports : forall m, List.In m modules -> Compat (get_module_Exports m) foreign_imports.
      intros.
      eapply Disjoint_Compat.
      eapply Disjoint_exports_foreign_imports; eauto.
    Qed.

    Lemma Compat_exports_impl_imports : forall m1 m2, List.In m1 modules -> List.In m2 modules -> Compat (get_module_Exports m1) (get_module_impl_Imports m2).
      intros.
      eapply Disjoint_Compat.
      unfold get_module_impl_Imports.
      unfold Disjoint.
      intros.
      intuition.
      eapply In_exports_module_name in H2.
      eapply In_to_map in H3.
      unfold InKey in *.
      unfold Func_to_import in *.
      rewrite map_map in H3.
      simpl in *.
      eapply in_map_iff in H3.
      openhyp.
      subst.
      unfold impl_label in *.
      simpl in *.
      eapply IsGoodModuleName_not_impl_module_name.
      eapply GoodModule_GoodName.
      eexists; eauto.
    Qed.

    Lemma Compat_impl_imports_foreign_imports : forall m, List.In m modules -> Compat (get_module_impl_Imports m) foreign_imports.
      intros.
      eapply Disjoint_Compat.
      unfold get_module_impl_Imports.
      unfold Disjoint.
      intros.
      intuition.
      unfold foreign_imports in *.
      eapply map_4 in H2.
      eapply In_to_map in H1.
      unfold InKey in *.
      unfold Func_to_import in *.
      rewrite map_map in H1.
      simpl in *.
      eapply in_map_iff in H1.
      openhyp.
      subst.
      unfold impl_label in *.
      eapply IsGoodModuleName_not_impl_module_name.
      eapply ImportsGoodModuleName.
      eauto.
      eexists.
      simpl.
      eauto.
    Qed.

    Lemma In_impl_imports_module_name : forall k m, In k (get_module_impl_Imports m) -> fst k = impl_module_name (MName m).
      unfold get_module_impl_Imports.
      intros.
      eapply In_to_map in H.
      unfold InKey in *.
      rewrite map_map in H.
      unfold Func_to_import in *.
      unfold impl_label in *.
      simpl in *.
      eapply in_map_iff in H.
      openhyp.
      subst.
      eauto.
    Qed.

    Lemma append_inj_2 : forall a b c, (a ++ b = a ++ c -> b = c)%string.
      induction a; simpl; intuition.
    Qed.

    Lemma impl_module_name_is_injection : forall s1 s2, impl_module_name s1 = impl_module_name s2 -> s1 = s2.
      intros.
      unfold impl_module_name in *.
      eapply append_inj_2; eauto.
    Qed.

    Lemma Compat_impl_imports_impl_imports : forall m1 m2, List.In m1 modules -> List.In m2 modules -> MName m1 <> MName m2 -> Compat (get_module_impl_Imports m1) (get_module_impl_Imports m2).
      intros.
      eapply Disjoint_Compat.
      unfold Disjoint.
      intros.
      not_not.
      openhyp.
      eapply In_impl_imports_module_name in H1.
      eapply In_impl_imports_module_name in H2.
      rewrite H1 in H2.
      eapply impl_module_name_is_injection; eauto.
    Qed.

    Lemma Disjoint_exports_imports : forall m, List.In m modules -> Disjoint (get_module_Exports m) (get_module_Imports m).
      intros.
      unfold get_module_Imports.
      symmetry.
      eapply Disjoint_after_diff.
    Qed.

    Lemma Compat_exports_total_exports : forall m, List.In m modules -> Compat (get_module_Exports m) total_exports.
      intros.
      unfold total_exports.
      eapply Compat_exports_many_exports; eauto.
      intuition.
    Qed.

    Lemma Compat_many_exports_total_exports : forall ms, incl ms modules -> Compat (update_all (List.map get_module_Exports ms)) total_exports.
      intros.
      symmetry.
      eapply Compat_update_all.
      eapply Forall_forall.
      intros.
      eapply in_map_iff in H0.
      openhyp.
      subst.
      symmetry.
      eapply Compat_exports_total_exports; eauto.
    Qed.

    Lemma Compat_many_exports_foreign_imports : forall ms, incl ms modules -> Compat (update_all (List.map get_module_Exports ms)) foreign_imports.
      intros.
      symmetry.
      eapply Compat_update_all.
      eapply Forall_forall.
      intros.
      eapply in_map_iff in H0.
      openhyp.
      subst.
      symmetry.
      eapply Compat_exports_foreign_imports; eauto.
    Qed.

    Lemma Compat_many_exports_impl_imports : forall ms m, incl (m :: ms) modules -> Compat (update_all (List.map get_module_Exports ms)) (get_module_impl_Imports m).
      intros.
      symmetry.
      eapply Compat_update_all.
      eapply Forall_forall.
      intros.
      eapply in_map_iff in H0.
      openhyp.
      subst.
      symmetry.
      eapply Compat_exports_impl_imports; intuition.
    Qed.

    Lemma Compat_exports_imports : forall m1 m2, List.In m1 modules -> List.In m2 modules -> MName m1 <> MName m2 -> Compat (get_module_Exports m1) (get_module_Imports m2).
      intros.
      unfold get_module_Imports.
      symmetry.
      eapply Compat_diff.
      symmetry.
      repeat eapply Compat_update.
      eapply Compat_exports_total_exports; eauto.
      eapply Compat_exports_foreign_imports; eauto.
      eapply Compat_exports_impl_imports; eauto.
    Qed.

    Lemma Compat_total_exports_foreign_imports : Compat total_exports foreign_imports.
      unfold total_exports.
      eapply Compat_many_exports_foreign_imports; intuition.
    Qed.

    Lemma Compat_total_exports_impl_imports : forall m, List.In m modules -> Compat total_exports (get_module_impl_Imports m).
      intros.
      unfold total_exports.
      eapply Compat_many_exports_impl_imports; intuition.
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

    Lemma Equal_get_module_Exports : forall m, map (spec_without_funcs_ok_fs modules imports) (of_list (get_module_exports m)) == get_module_Exports m.
      intros.
      unfold get_module_Exports.
      unfold to_map.
      unfold get_module_exports.
      rewrite map_of_list.
      rewrite map_map.
      simpl.
      reflexivity.
    Qed.

    Lemma exports_Equal_total_exports : map (spec_without_funcs_ok_fs modules imports) (exports modules) == total_exports.
      unfold exports.
      unfold total_exports.
      change StubMake.LMF.to_map with to_map in *.
      unfold to_map.
      rewrite app_all_update_all.
      rewrite map_update_all_comm.
      rewrite map_map.
      rewrite map_map.
      eapply update_all_Equal.
      eapply Forall2_map.
      unfold pointwise_relation.
      eapply Equal_get_module_Exports.
      eapply NoDupKey_app_all; eauto.
    Qed.

    Lemma bimports_base_Equal_update : of_list (bimports_base modules imports) == total_exports + foreign_imports.
      intros.
      rewrite Compat_update_sym by (eapply Compat_total_exports_foreign_imports).
      unfold bimports_base.
      rewrite of_list_app.
      rewrite of_list_3.
      rewrite of_list_3.
      rewrite exports_Equal_total_exports.
      reflexivity.
      eapply NoDupKey_bimports_base; eauto.
    Qed.

    Lemma bimports_Equal_update_update : forall m, List.In m modules -> of_list (bimports modules imports m) == total_exports + foreign_imports + get_module_impl_Imports m.
      intros.
      unfold bimports.
      rewrite of_list_app.
      rewrite bimports_base_Equal_update.
      reflexivity.
      eapply NoDupKey_bimports; eauto.
    Qed.

    Lemma make_module_Imports : forall m, List.In m modules -> Imports (do_make_module m) === get_module_Imports m.
      intros.
      unfold do_make_module, make_module, bmodule_, Imports.
      rewrite importsMap_of_list.
      eapply to_blm_Equal.
      unfold bimports_diff_bexports.
      rewrite of_list_diff.
      unfold get_module_Imports.
      rewrite bimports_Equal_update_update by eauto.
      rewrite bexports_Equal_exports by eauto.
      reflexivity.
      eapply NoDupKey_bimports; eauto.
      eapply NoDupKey_bexports; eauto.
      eapply diff_NoDupKey.
      eapply NoDupKey_bimports; eauto.
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

    Lemma Compat_imports_imports : forall m1 m2, List.In m1 modules -> List.In m2 modules -> MName m1 <> MName m2 -> Compat (get_module_Imports m1) (get_module_Imports m2).
      intros.
      unfold get_module_Imports.
      eapply Compat_diff.
      symmetry.
      eapply Compat_diff.
      repeat eapply Compat_update; symmetry; repeat eapply Compat_update.
      reflexivity.
      eapply Compat_total_exports_foreign_imports.
      eapply Compat_total_exports_impl_imports; eauto.
      symmetry; eapply Compat_total_exports_foreign_imports.
      reflexivity.
      symmetry; eapply Compat_impl_imports_foreign_imports; eauto.
      symmetry; eapply Compat_total_exports_impl_imports; eauto.
      eapply Compat_impl_imports_foreign_imports; eauto.
      eapply Compat_impl_imports_impl_imports; eauto.
    Qed.

    (* main lemmas *)

    Lemma compat_imports_exports : forall ms m, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (get_module_Imports m) (update_all (List.map get_module_Exports ms)).
      intros.
      unfold get_module_Imports.
      eapply Compat_diff.
      symmetry.
      repeat eapply Compat_update.
      eapply Compat_many_exports_total_exports.
      incl_tran_cons.
      inversion H0; subst; eauto.
      eapply Compat_many_exports_foreign_imports.
      incl_tran_cons.
      inversion H0; subst; eauto.
      eapply Compat_many_exports_impl_imports; eauto.
    Qed.

    Lemma compat_exports_imports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (get_module_Exports m) (update_all (List.map get_module_Imports ms) - update_all (List.map get_module_Exports ms)).
      intros.
      symmetry.
      eapply Compat_diff.
      symmetry.
      eapply Compat_update_all.
      eapply Forall_forall.
      intros.
      eapply in_map_iff in H1.
      openhyp.
      subst.
      eapply Compat_exports_imports.
      intuition.
      intuition.
      simpl in *.
      eapply NoDup_cons_elim in H0; eauto.
      eapply in_map; eauto.
    Qed.

    Lemma compat_imports_many_imports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (get_module_Imports m) (update_all (List.map get_module_Imports ms)).
      intros.
      eapply Compat_update_all.
      eapply Forall_forall.
      intros.
      eapply in_map_iff in H1.
      openhyp.
      subst.
      eapply Compat_imports_imports.
      intuition.
      intuition.
      simpl in *.
      eapply NoDup_cons_elim in H0; eauto.
      eapply in_map; eauto.
    Qed.

    Lemma compat_imports_imports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (get_module_Imports m) (update_all (List.map get_module_Imports ms) - update_all (List.map get_module_Exports ms)).
      intros.
      symmetry.
      eapply Compat_diff.
      symmetry.
      eapply compat_imports_many_imports; eauto.
    Qed.

    Lemma combine_imports_exports : 
      forall a ms, 
        incl (a :: ms) modules -> 
        List.NoDup (List.map MName (a :: ms)) -> 
        update_all (List.map get_module_Imports ms) -
        update_all (List.map get_module_Exports ms) - get_module_Exports a +
        (get_module_Imports a - update_all (List.map get_module_Exports ms)) ==
        get_module_Imports a + 
        update_all (List.map get_module_Imports ms) -
        (get_module_Exports a + update_all (List.map get_module_Exports ms)).
      intros.
      rewrite Disjoint_diff_update_comm.
      rewrite update_diff_same.
      rewrite Compat_update_sym.
      rewrite diff_update.
      rewrite diff_diff_sym.
      reflexivity.
      symmetry.
      eapply compat_imports_many_imports; eauto.
      eapply Disjoint_diff.
      eapply Disjoint_exports_imports.
      intuition.
    Qed.

    Lemma link_all_ok : 
      forall (ms : list GoodModule), 
        let linked := link_all (List.map do_make_module ms) in
        let module_names := List.map MName ms in
        let linked_module_names := to_set (empty_module_name :: module_names) in
        let linked_exports := update_all (List.map get_module_Exports ms) in
        let linked_imports := update_all (List.map get_module_Imports ms) - linked_exports  in
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
      eapply to_blm_Equal.
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
      repeat rewrite update_all_cons.
      eapply combine_imports_exports; eauto.
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
