Set Implicit Arguments.

Require Import ADT.
Require Import RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import CompileFuncSpec.
  Module Import CompileFuncSpecMake := Make E M.
  Require Import Inv.
  Import InvMake.
  Require Import Semantics.
  Import SemanticsMake.
  Import InvMake2.

  Require Import FMapFacts1.
  Require Import LabelMap.
  Module Import BLMF := WFacts_fun LabelKey LabelMap.
  Require Import Label.
  Module Import LMF := WFacts_fun Key' LabelMap.
  Module Import LMFU := UWFacts_fun Key' LabelMap.
  Require Import ListFacts2.
  Module Import LFL := Make Key'.

  Require Import AutoSep.
  Require Import StructuredModule.
  Require Import StructuredModuleFacts.
  Require Import GoodModule.
  Require Import GoodFunction.
  Require Import ConvertLabel.
  Require Import NameDecoration.
  Require Import Wrap.
  Require Import GeneralTactics.

  Section TopSection.

    (* modules to be exported *)
    Variable modules : list GoodModule.

    Definition FName := SyntaxFunc.Name.

    Definition MName := GoodModule.Name.

    Definition module_names := map MName modules.

    Hypothesis NoDupModuleNames : NoDup module_names.

    (* imported specs *)
    Variable imports : LabelMap.t ForeignFuncSpec.

    Definition imported_module_names := map (fun x => fst (fst x)) (LabelMap.elements imports).

    Hypothesis NoSelfImport : Disjoint module_names imported_module_names.

    Hypotheses ImportsGoodModuleName : forall l, LabelMap.In l imports -> IsGoodModuleName (fst l).

    Definition to_internal_func_spec (f : GoodFunction) : InternalFuncSpec :=
      {|
        Semantics.Fun := f;
        Semantics.NoDupArgVars := proj1 (IsGoodFunc f)
      |}.

    Coercion to_internal_func_spec : GoodFunction >-> InternalFuncSpec.

    Definition get_module_exports (module : GoodModule) := 
      List.map 
        (fun (f : GoodFunction) =>
           ((MName module, FName f), f : InternalFuncSpec)
        ) (Functions module).

    Definition exports :=
      to_map
        (flatten 
           (List.map get_module_exports modules)).

    Definition accessible_labels := keys imports ++ keys exports.

    Section fs.

      Variable stn : settings.

      Definition labels (lbl : label) : option W := Labels stn lbl.

      Definition is_label_map_to_word lbl p :=
        match labels lbl with
          | Some p' => 
            if weq p p' then
              true
            else
              false
          | None => false
        end.

      Definition is_label_map_to_word' A p (x : label * A) := is_label_map_to_word (fst x) p.

      Definition find_by_word A m (p : W) : option A :=
        match find (is_label_map_to_word' p) m with
          | Some (_, a) => Some a
          | None => None
        end.

      Definition is_export := find_by_word (LabelMap.elements exports).

      Definition is_import := find_by_word (LabelMap.elements imports).

      Definition fs (p : W) : option Callee :=
        match is_export p with
          | Some spec => Some (Internal spec)
          | None => 
            match is_import p with
              | Some spec => Some (Foreign spec)
              | None => None
            end
        end.

    End fs.

    Definition foreign_spec spec : assert := 
      st ~> ExX, foreign_spec _ spec st.

    Definition spec_without_funcs_ok_fs (spec : InternalFuncSpec) := spec_without_funcs_ok spec fs.

    Definition bimports_base : list import := 
      LabelMap.elements 
        (LabelMap.map foreign_spec imports) ++ 
        LabelMap.elements 
        (LabelMap.map spec_without_funcs_ok_fs exports).
    
    Section module.

      Variable m : GoodModule.

      Hypothesis in_modules : In m modules.

      Section f.

        Variable f : GoodFunction.

        Section body.
          
          Variable im : LabelMap.LabelMap.t assert.

          Variable im_g : importsGlobal im.

          Definition mod_name := MName m.

          Definition impl_label mod_name f_name : label := (impl_module_name mod_name, f_name).

          Definition tgt := impl_label mod_name (FName f).

          Definition body := 
            @Seq_ _ im_g mod_name
                  (AssertStar_ im mod_name accessible_labels (CompileFuncSpecMake.spec f))
                  (Goto_ im_g mod_name tgt).

        End body.

        Definition make_stub : function (MName m) :=
          (FName f, spec_without_funcs_ok f fs, body).

      End f.

      Definition Func_to_import (f : GoodFunction) := (impl_label (MName m) (FName f), CompileFuncSpecMake.spec f).

      Definition bimports : list import := 
        bimports_base ++ List.map Func_to_import (Functions m).
      
      Definition stubs := map make_stub (Functions m).

      Definition bexports := map (@func_to_import _) stubs.

      Definition diff_map : forall A B, list (A * B) -> list (A * B) -> list (A * B).
        admit.
      Defined.

      Definition bimports_diff_bexports := diff_map bimports bexports.

      Definition make_module := StructuredModule.bmodule_ bimports_diff_bexports stubs.

      Lemma In_exports : forall l, LabelMap.In l exports -> exists m f, In m modules /\ In f (Functions m) /\ l = (MName m, FName f).
        intros.
        unfold exports in *.
        eapply In_to_map in H.
        eapply in_map_iff in H.
        openhyp.
        rewrite <- H in *.
        clear H.
        rename H0 into H.
        eapply In_flatten_elim in H.
        openhyp.
        eapply in_map_iff in H0.
        openhyp.
        rewrite <- H0 in *.
        unfold get_module_exports in *.
        eapply in_map_iff in H.
        openhyp.
        rewrite <- H in *.
        unfold MName; simpl in *.
        descend.
        eauto.
        eauto.
        eauto.
      Qed.

      Lemma NoDup_bimports_base : NoDup (map fst bimports_base).
        unfold bimports_base.
        erewrite map_app.
        eapply NoDup_app.
        eapply NoDupKey_NoDup_fst.
        eapply LabelMap.elements_3w.
        eapply NoDupKey_NoDup_fst.
        eapply LabelMap.elements_3w.
        eapply Disjoint_map with (f := fst).
        eapply Disjoint_symm.
        eapply Disjoint_incl.
        eauto.

        unfold incl.
        unfold module_names in *.
        intros.
        eapply in_map_iff in H.
        openhyp.
        rewrite <- H in *.
        clear H.
        rename H0 into H.
        eapply In_fst_elements_In in H.
        eapply map_4 in H.
        eapply In_exports in H.
        openhyp.
        rewrite H1 in *; simpl in *.
        unfold MName; simpl in *.
        eapply in_map_iff.
        eexists.
        eauto.

        unfold incl.
        intros.
        unfold imported_module_names in *.
        rewrite <- map_map.
        eapply incl_map in H.
        eauto.
        unfold incl.
        intros.
        eapply In_fst_elements_In.
        eapply In_fst_elements_In in H0.
        eapply F.map_in_iff; eauto.
      Qed.

      Lemma impl_label_is_injection : forall mn, IsInjection (impl_label mn).
        unfold IsInjection, impl_label; intuition.
      Qed.

      Lemma IsGoodModuleName_not_impl_module_name : forall s, IsGoodModuleName s -> ~ exists s', impl_module_name s' = s.
        unfold IsGoodModuleName, impl_module_name.
        intros.
        intuition.
        openhyp.
        rewrite <- H0 in *.
        simpl in *.
        intuition.
      Qed.

      Lemma GoodModule_GoodName : forall m : GoodModule, IsGoodModuleName (MName m).
        intros; destruct m0; simpl; eauto.
      Qed.

      Lemma In_bimports_base_fst : forall x, In x bimports_base ->  LabelMap.In (fst x) imports \/ exists m f, In m modules /\ In f (Functions m) /\ fst x = (MName m, FName f).
        intros.
        unfold bimports_base in *.
        eapply in_app_or in H.
        openhyp.
        left.
        destruct x.
        simpl.
        eapply InA_eq_key_elt_List_In in H.
        eapply LabelMap.elements_2 in H.
        eapply F.map_in_iff.
        eexists.
        eauto.
        right.
        destruct x.
        simpl.
        eapply InA_eq_key_elt_List_In in H.
        eapply LabelMap.elements_2 in H.
        eapply MapsTo_In in H.
        eapply map_4 in H.
        eapply In_exports; eauto.
      Qed.

      Lemma bimports_base_good_names : forall x, In x bimports_base -> IsGoodModuleName (fst (fst x)).
        intros.
        eapply In_bimports_base_fst in H.
        openhyp.
        eauto.
        rewrite H1 in *.
        simpl.
        eapply GoodModule_GoodName.
      Qed.

      Lemma NoDup_bimports : NoDupKey bimports.
        eapply NoDupKey_NoDup_fst.
        unfold bimports.
        erewrite map_app.
        eapply NoDup_app.
        eapply NoDup_bimports_base.
        erewrite map_map.
        unfold Func_to_import.
        simpl.
        unfold FName.
        erewrite <- map_map.
        eapply Injection_NoDup.
        eapply impl_label_is_injection.
        eapply NoDupFuncNames.
        unfold Disjoint.
        intuition.
        erewrite map_map in H1.
        unfold Func_to_import in *.
        simpl in *.
        eapply in_map_iff in H1.
        openhyp.
        rewrite <- H in *.
        eapply in_map_iff in H0.
        openhyp.
        eapply f_equal with (f := fst) in H0.
        unfold impl_label in *.
        simpl in *.
        eapply bimports_base_good_names in H2.
        eapply IsGoodModuleName_not_impl_module_name in H2.
        contradict H2.
        eexists.
        symmetry.
        eauto.
      Qed.

      Lemma NoDup_flatten : 
        forall ls : list GoodModule, 
          NoDup (map MName ls) -> 
          NoDup
            (flatten
               (map (fun x0 : GoodModule => map fst (get_module_exports x0)) ls)).
        clear.
        induction ls; simpl; intros.
        econstructor.
        eapply NoDup_app.
        unfold get_module_exports.
        rewrite map_map.
        simpl.
        destruct a; simpl in *.
        unfold FName.
        eauto.
        generalize NoDupFuncNames; intro HH.
        eapply Injection_NoDup with (f := fun s => (Name, s)) in HH.
        rewrite map_map in HH.
        eauto.
        unfold IsInjection; intuition.
        eapply IHls.
        inversion H; subst.
        eauto.
        unfold Disjoint.
        intros.
        intuition.
        eapply in_map_iff in H1.
        openhyp.
        rewrite <- H0 in *.
        clear H0.
        eapply In_flatten_elim in H2.
        openhyp.
        eapply in_map_iff in H2.
        openhyp.
        rewrite <- H2 in *.
        clear H2.
        eapply in_map_iff in H0.
        openhyp.
        destruct x; destruct x2; simpl in *.
        subst.
        unfold get_module_exports in *.
        eapply in_map_iff in H1.
        openhyp.
        injection H0; intros; subst.
        eapply in_map_iff in H2.
        openhyp.
        injection H2; intros; subst.
        rewrite <- H7 in *; clear H7.
        inversion H; subst.
        contradict H8.
        eapply in_map_iff.
        eexists.
        eauto.
      Qed.

      Lemma incl_stubs_bimports : incl bexports bimports.
        unfold incl, bexports, stubs.
        intros.
        rewrite map_map in H.
        unfold func_to_import, make_stub in *.
        simpl in *.
        eapply in_map_iff in H.
        openhyp.
        rewrite <- H in *.
        clear H.
        unfold bimports.
        eapply in_or_app.
        left.
        unfold bimports_base.
        eapply in_or_app.
        right.
        eapply InA_eq_key_elt_List_In.
        eapply LabelMap.elements_1.
        unfold spec_without_funcs_ok_fs.
        eapply LabelMap.find_2.
        erewrite find_map.
        f_equal.
        instantiate (1 := x).
        reflexivity.
        eapply LabelMap.find_1.
        eapply MapsTo_to_map.
        eapply NoDupKey_NoDup_fst.
        rewrite map_flatten.
        rewrite map_map.
        unfold module_names in *.
        eapply NoDup_flatten; eauto.
        eapply In_flatten_intro.
        Focus 2.
        eapply in_map_iff.
        eexists.
        eauto.
        unfold get_module_exports.
        eapply in_map_iff.
        eexists.
        eauto.
      Qed.

      Lemma fs_internal : 
        forall stn p spec, 
          fs stn p = Some (Internal spec) -> 
          exists lbl : label, 
            LabelMap.find lbl exports = Some spec /\ 
            Labels stn lbl = Some p.
      Proof.
        intros.
        unfold fs in *.
        destruct (option_dec (is_export stn p)).
        destruct s.
        rewrite e in H.
        injection H; intros.
        subst.
        unfold is_export in *.
        unfold find_by_word in *.
        destruct (option_dec (find (is_label_map_to_word' stn p) (LabelMap.elements exports))).
        destruct s.
        destruct x.
        rewrite e0 in e.
        injection e; intros.
        subst.
        eapply find_spec in e0.
        openhyp.
        unfold is_label_map_to_word', is_label_map_to_word in *.
        simpl in *.
        destruct (option_dec (labels stn l)).
        destruct s.
        rewrite e0 in H0.
        destruct (weq p x).
        subst.
        unfold labels in *.
        exists l.
        split.
        eapply In_find_Some; eauto.
        eapply InA_eq_key_elt_List_In; intuition.
        intuition.
        intuition.
        rewrite e0 in H0; intuition.
        rewrite e0 in e; intuition.
        rewrite e in H.
        destruct (is_import stn p); intuition.
        discriminate.
      Qed.

      Lemma augment_elim : 
        forall imps specs stn (lbls : list label),
          augment imps specs stn lbls ->
          (forall x, In x lbls -> LabelMap.LabelMap.find (x : Labels.label) imps <> None) ->
          forall l p spec,
            List.In l lbls ->
            Labels stn l = Some p ->
            LabelMap.LabelMap.find (l : Labels.label) imps = Some spec ->
            specs p = Some spec.
      Proof.
        induction lbls; simpl; intros.
        intuition.
        destruct H1.
        subst.
        destruct l.
        unfold to_bedrock_label in *.
        simpl in *.
        rewrite H3 in H.
        openhyp.
        congruence.
        generalize H0; specialize (H0 a); intro.
        eapply ex_up in H0.
        openhyp.
        destruct a.
        unfold to_bedrock_label in *.
        simpl in *.
        rewrite H0 in H.
        openhyp.
        eauto.
        eauto.
      Qed.

      Lemma imports_bimports : forall k v, LabelMap.find k imports = Some v -> find_list k bimports = Some (foreign_spec v).
        unfold bimports, bimports_base.
        intros.
        eapply NoDup_app_find_list.
        eapply NoDup_bimports.
        eapply NoDup_app_find_list.
        eapply NoDupKey_unapp1.
        eapply NoDup_bimports.
        unfold bimports, bimports_base.
        intuition.
        rewrite find_list_elements.
        eapply find_map; eauto.
      Qed.

      Corollary in_imports_in_bimports : forall x, LabelMap.In x imports -> In x (map fst bimports).
      unfold bimports, bimports_base.
      intros.
      erewrite map_app.
      eapply in_or_app.
      left.
      erewrite map_app.
      eapply in_or_app.
      left.
      eapply In_fst_elements_In.
      eapply map_3; eauto.
      Qed.

      Lemma exports_bimports : forall k v, LabelMap.find k exports = Some v -> find_list k bimports = Some (spec_without_funcs_ok v fs).
        unfold bimports, bimports_base.
        intros.
        eapply NoDup_app_find_list.
        eapply NoDup_bimports.
        eapply NoDup_app_find_list_2.
        eapply NoDupKey_unapp1.
        eapply NoDup_bimports.
        unfold bimports, bimports_base.
        intuition.
        rewrite find_list_elements.
        unfold spec_without_funcs_ok_fs.
        erewrite find_map; eauto.
      Qed.

      Corollary in_exports_in_bimports : forall x, LabelMap.In x exports -> In x (map fst bimports).
      unfold bimports, bimports_base.
      intros.
      erewrite map_app.
      eapply in_or_app.
      left.
      erewrite map_app.
      eapply in_or_app.
      right.
      eapply In_fst_elements_In.
      eapply map_3; eauto.
      Qed.

      Definition Equal_map elt ls1 ls2 := forall k, @find_list elt k ls1 = find_list k ls2.

      Lemma NoDup_union : NoDupKey (bimports_diff_bexports ++ bexports).
        admit.
      Qed.

      Lemma Equal_union_bimports : Equal_map (bimports_diff_bexports ++ bexports) bimports.
        admit.
      Qed.

      Definition full_imports := fullImports bimports_diff_bexports stubs.

      Lemma fullImports_eq_bimports : forall (k : label), LabelMap.LabelMap.find (k : Labels.label) full_imports = find_list k bimports.
        intros.
        unfold full_imports in *.
        erewrite fullImports_spec.
        eapply Equal_union_bimports.
        eapply NoDup_union.
      Qed.

      Corollary bimports_fullImports : forall (x : label), In x (map fst bimports) -> LabelMap.LabelMap.find (x : Labels.label) full_imports <> None.
      Proof.
        intros.
        specialize In_find_list_not_None; intros.
        eapply InA_eq_List_In in H.
        eapply H0 in H.
        eapply ex_up in H.
        openhyp.
        rewrite fullImports_eq_bimports.
        intuition.
      Qed.

      Lemma accessible_labels_subset_fullImports :
        forall x : label, 
          In x accessible_labels ->
          LabelMap.LabelMap.find (x : Labels.label) full_imports <> None.
      Proof.
        unfold accessible_labels.
        intros.
        eapply in_app_or in H.
        destruct H.

        unfold keys in *; eapply In_fst_elements_In in H.
        eapply in_imports_in_bimports in H.
        eapply bimports_fullImports; eauto.

        unfold keys in *; eapply In_fst_elements_In in H.
        eapply in_exports_in_bimports in H.
        eapply bimports_fullImports; eauto.
      Qed.

      Lemma exports_accessible_labels : forall l, LabelMap.find l exports <> None -> In l accessible_labels.
        unfold accessible_labels.
        intros.
        eapply in_or_app.
        right.
        unfold keys in *; eapply In_fst_elements_In.
        eapply In_find_not_None; eauto.
      Qed.
      
      Lemma exports_fullImports : forall (l : label) spec, LabelMap.find l exports = Some spec -> LabelMap.LabelMap.find (l : Labels.label) full_imports = Some (spec_without_funcs_ok spec fs).
        intros.
        rewrite fullImports_eq_bimports.
        eapply exports_bimports; eauto.
      Qed.

      Lemma tgt_fullImports : forall f, In f (Functions m) -> LabelMap.LabelMap.find (tgt f : Labels.label) full_imports = Some (CompileFuncSpecMake.spec f).
        intros.
        rewrite fullImports_eq_bimports. 
        unfold bimports, bimports_base.
        eapply NoDup_app_find_list_2.
        eapply NoDup_bimports.
        unfold tgt.
        unfold mod_name.
        eapply In_find_list_Some.
        eapply NoDupKey_unapp2.
        eapply NoDup_bimports.
        unfold bimports, bimports_base.
        intuition.
        unfold Func_to_import in *; simpl in *.
        eapply in_map with (f := fun x => Func_to_import x) in H.
        eapply InA_eq_key_elt_List_In.
        eauto.
      Qed.

      Lemma fs_foreign :
        forall stn p spec, 
          fs stn p = Some (Foreign spec) -> 
          exists lbl : label, 
            LabelMap.find lbl imports = Some spec /\ 
            Labels stn lbl = Some p.
      Proof.
        intros.
        unfold fs in *.
        destruct (option_dec (is_export stn p)).
        destruct s.
        rewrite e in H.
        intuition.
        discriminate.
        rewrite e in H.
        destruct (option_dec (is_import stn p)).
        destruct s.
        rewrite e0 in H.
        injection H; intros; subst.
        unfold is_import in *.
        unfold find_by_word in *.
        destruct (option_dec (find (is_label_map_to_word' stn p) (LabelMap.elements imports))).
        destruct s.
        destruct x.
        rewrite e1 in e0.
        injection e0; intros; subst.
        eapply find_spec in e1.
        openhyp.
        unfold is_label_map_to_word', is_label_map_to_word in *.
        simpl in *.
        destruct (option_dec (labels stn l)).
        destruct s.
        rewrite e1 in H0.
        destruct (weq p x).
        subst.
        unfold labels in *.
        exists l.
        split.
        eapply In_find_Some; eauto.
        eapply InA_eq_key_elt_List_In.
        eauto.
        intuition.
        intuition.
        rewrite e1 in H0; intuition.
        rewrite e1 in e0; intuition.
        rewrite e0 in H.
        intuition.
      Qed.

      Lemma imports_accessible_labels : forall l, LabelMap.find l imports <> None -> In l accessible_labels.
        unfold accessible_labels.
        intros.
        eapply in_or_app.
        left.
        unfold keys in *; eapply In_fst_elements_In.
        eapply In_find_not_None; eauto.
      Qed.
      
      Lemma imports_fullImports : forall (l : label) spec, LabelMap.find l imports = Some spec -> LabelMap.LabelMap.find (l : Labels.label) full_imports = Some (foreign_spec spec).
        intros.
        rewrite fullImports_eq_bimports.
        eapply imports_bimports; eauto.
      Qed.

      Lemma specs_internal :
        forall specs stn p spec,
          augment full_imports specs stn accessible_labels ->
          fs stn p = Some (Internal spec) ->
          specs p = Some (spec_without_funcs_ok spec fs).
      Proof.
        intros.
        eapply fs_internal in H0.
        openhyp.
        eapply augment_elim in H; eauto.
        eapply accessible_labels_subset_fullImports.
        eapply exports_accessible_labels.
        intuition.
        eapply exports_fullImports; eauto.
      Qed.

      Lemma specs_foreign :
        forall specs stn p spec,
          augment full_imports specs stn accessible_labels ->
          fs stn p = Some (Foreign spec) ->
          specs p = Some (foreign_spec spec).
      Proof.
        intros.
        eapply fs_foreign in H0.
        openhyp.
        eapply augment_elim in H; eauto.
        eapply accessible_labels_subset_fullImports.
        eapply imports_accessible_labels.
        intuition.
        eapply imports_fullImports; eauto.
      Qed.

      Lemma fs_funcs_ok : 
        forall specs stn,
          augment full_imports specs stn accessible_labels ->
          interp specs (funcs_ok stn fs).
      Proof.
        unfold funcs_ok.
        post; descend.

        apply injL; intro.
        Opaque internal_spec.
        post; descend.
        erewrite specs_internal; eauto.

        unfold spec_without_funcs_ok at 2.
        step auto_ext.
        Transparent internal_spec.
        step auto_ext.
        rewrite sepFormula_eq; apply Imply_refl.

        apply injL; intro.
        Opaque InvMake2.foreign_spec.
        post; descend.
        instantiate (1 := foreign_spec x0).
        erewrite specs_foreign; eauto.

        unfold foreign_spec.
        step auto_ext.
        Transparent InvMake2.foreign_spec.
        step auto_ext.
        rewrite sepFormula_eq; apply Imply_refl.
      Qed.

      Lemma good_vcs : forall ls, (forall x, In x ls -> In x (Functions m)) -> vcs (makeVcs bimports_diff_bexports stubs (map make_stub ls)).
        induction ls; simpl; eauto.
        Opaque funcs_ok.
        Opaque spec_without_funcs_ok.
        wrap0.
        descend.

        eapply fs_funcs_ok; eauto.

        eauto.

        erewrite tgt_fullImports; eauto.
      Qed.        

      Require Import NameVC.
      Definition fst_2 A B C (x : A * B * C) := fst (fst x).
      Notation fst2 := (@fst_2 _ _ _).

      Lemma NotIn_NameNotInImports : forall imps mn, ~ In mn (map fst2 imps) -> NameNotInImports mn imps.
        clear.
        unfold NameNotInImports.
        induction imps; simpl; intros.
        eauto.
        destruct a; destruct p; simpl in *.
        destruct (string_dec s mn).
        contradict H.
        eauto.
        eapply IHimps.
        intuition.
      Qed.
(*
        Lemma Disjoint_In_not_In : forall A ls1 ls2, @Disjoint A ls1 ls2 -> forall x, In x ls1 -> ~ In x ls2.
          unfold Disjoint; intuition; eapply H; eauto.
        Qed.
        eapply Disjoint_In_not_In.
        eapply Disjoint_symm.
        unfold fst_2.
        rewrite <- map_map.
        eapply Disjoint_map.

        Lemma Disjoint_bimports_bexports_fst2 : Disjoint (map fst2 bimports_diff_bexports*)

      Lemma MapsTo_exports : forall l v, LabelMap.MapsTo l v exports -> exists m f, In m modules /\ In f (Functions m) /\ l = (MName m, FName f) /\ v = f.
        intros.
        unfold exports in *.
        eapply MapsTo_to_map_elim in H.
        eapply In_flatten_elim in H.
        openhyp.
        eapply in_map_iff in H0.
        openhyp.
        rewrite <- H0 in *.
        unfold get_module_exports in *.
        eapply in_map_iff in H.
        openhyp.
        injection H; intros; subst.
        unfold MName; simpl in *.
        descend.
        eauto.
        eauto.
        eauto.
        eauto.
        unfold get_module_exports in *.
        eapply NoDupKey_NoDup_fst.
        rewrite map_flatten.
        rewrite map_map.
        eapply NoDup_flatten; eauto.
      Qed.

      Lemma In_bimports_base : forall x, In x bimports_base ->  LabelMap.In (fst x) imports \/ exists m f, In m modules /\ In f (Functions m) /\ fst x = (MName m, FName f) /\ snd x = spec_without_funcs_ok_fs f.
        intros.
        unfold bimports_base in *.
        eapply in_app_or in H.
        openhyp.
        left.
        destruct x.
        simpl.
        eapply InA_eq_key_elt_List_In in H.
        eapply LabelMap.elements_2 in H.
        eapply F.map_in_iff.
        eexists.
        eauto.
        right.
        destruct x.
        simpl.
        eapply InA_eq_key_elt_List_In in H.
        eapply LabelMap.elements_2 in H.
        eapply F.map_mapsto_iff in H.
        openhyp.
        subst.
        eapply MapsTo_exports in H0.
        openhyp.
        subst.
        descend; eauto.
      Qed.

      Definition InKey elt k (ls : list (label * elt)) := In k (map fst ls).

      Lemma module_name_not_in_diff_bexports : ~ In (MName m) (map fst2 bimports_diff_bexports).
        intuition.
        unfold fst_2 in *.
        rewrite <- map_map in H.
        eapply in_map_iff in H.
        openhyp.
        destruct x; simpl in *.
        subst.
        unfold bimports_diff_bexports in *.
        Lemma In_diff : forall elt ls1 ls2 x, @InKey elt x (diff_map ls1 ls2) -> InKey x ls1 /\ ~ InKey x ls2.
          admit.
        Qed.
        eapply In_diff in H0.
        openhyp.
        contradict H0.
        unfold bimports in *.
        Lemma inkey_app_or : forall elt k ls1 ls2, @InKey elt k (ls1 ++ ls2) <-> InKey k ls1 \/ InKey k ls2.
          admit.
        Qed.
        eapply inkey_app_or in H.
        unfold Func_to_import in *.
        openhyp.
        unfold bimports_base in *.
        eapply inkey_app_or in H.
        openhyp.
        admit.
        eapply In_fst_elements_In in H.
        eapply map_4 in H.
        unfold exports in *.
        eapply In_to_map in H.
        unfold bexports.
        unfold func_to_import.
        unfold stubs.
        unfold make_stub.
        rewrite map_map.
        simpl in *.
        rewrite map_flatten in H.
        unfold get_module_exports in *.
        rewrite map_map in H.
        simpl in *.
        unfold InKey.



        Lemma InKey_bimports_base : forall l, InKey l bimports_base ->  LabelMap.In l imports \/ exists m f, In m modules /\ In f (Functions m) /\ l = (MName m, FName f).
          unfold InKey in *.
          intros.
          eapply in_map_iff in H.
          openhyp.
          subst.
          eapply In_bimports_base_fst in H0.
          openhyp.
          eauto.
          right.
          descend; eauto.
        Qed.
        eapply InKey_bimports_base in H.
        openhyp; simpl in *.
        admit.
        injection H1; intros; subst.
        unfold InKey.
        unfold bexports.
        unfold func_to_import.
        unfold stubs.
        unfold make_stub.
        rewrite map_map.
        rewrite map_map.
        simpl in *.
        eapply in_map_iff.
        descend; eauto.
        admit.
        admit.
      Qed.

      Lemma module_name_not_in_imports : NameNotInImports (MName m) bimports_diff_bexports.
        eapply NotIn_NameNotInImports.
        eapply module_name_not_in_diff_bexports.        
      Qed.

      Lemma no_dup_func_names : NoDupFuncNames stubs.
        eapply NoDup_NoDupFuncNames.
        unfold stubs.
        rewrite map_map.
        unfold make_stub; simpl in *.
        destruct m; simpl in *.
        eauto.
      Qed.
      
      Theorem make_module_ok : XCAP.moduleOk make_module.
        eapply bmoduleOk.
        eapply module_name_not_in_imports.
        eapply no_dup_func_names.
        eapply good_vcs; eauto.
      Qed.

    End module.

    Definition ms := map make_module modules.

    Definition empty_module := @StructuredModule.bmodule_ nil "empty_module" nil.

    Fixpoint link_all ls := 
      match ls with
        | nil => empty_module
        | x :: nil => x
        | x :: xs => link x (link_all xs)
      end.

    Definition m := link_all ms.

    Theorem ok : moduleOk m.
      admit.
    Qed.

  End TopSection.

End Make.
