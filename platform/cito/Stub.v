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
  Require Import FMapFacts3.

  Require Import ConvertLabelMap.
  Import Notations.
  Open Scope clm_scope.

  Require Import Equalities.

  Module Import SS := StringSet.StringSet.
  Module Import SSF := StringSet.StringFacts.
  Module SSK := StringSet.StringKey.
  Require Import FSetFacts1.
  Module SSK_as_UDT := Make_UDT SSK.
  Module Import SSUF := UWFacts_fun SSK_as_UDT SS.

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

(*
  Require Import LabelMap.
  Module Import BLMF := WFacts_fun LabelKey LabelMap.
  Require Import Label.
  Module Import LMF := WFacts_fun Key' LabelMap.
  Module Import LMFU := UWFacts_fun Key' LabelMap.
  Require Import ListFacts2.
  Module Import LFL := Make Key'.
*)

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
        (app_all 
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

    Definition fs_good_to_use : (settings -> W -> option Callee) -> settings -> Prop.
      admit.
    Qed.

    (* Definition name_marker (name : string) : PropX _ _ _ := (Ex s, [| s = name |])%PropX. *)

    Definition func_spec (id : string) f : assert := (st ~> [| id = id /\ fs_good_to_use fs (fst st) |] ---> spec_without_funcs_ok f fs st)%PropX.

    Definition func_spec_Func (f : Func) := func_spec (FName f) f.

    (* Definition func_spec' name (f : InternalFuncSpec) := func_spec name f. *)

    Definition bimports_base : list import := 
      LabelMap.elements 
        (LabelMap.map foreign_spec imports) ++ 
        LabelMap.elements 
        (LabelMap.mapi (fun lbl (spec : InternalFuncSpec) => func_spec (snd lbl) spec) exports).
    
    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap.

    Definition get_module_Exports (module : GoodModule) := 
      to_map 
        (List.map 
           (fun (f : GoodFunction) =>
              ((MName module, FName f), func_spec_Func f))
           (Functions module)).

    Definition impl_label mod_name f_name : label := (impl_module_name mod_name, f_name).

    Definition Func_to_import m (f : GoodFunction) := (impl_label (MName m) (FName f), CompileFuncSpecMake.spec f).

    Definition get_module_impl_Imports (module : GoodModule) := 
      to_map 
        (List.map 
           (Func_to_import module)
           (Functions module)).

    Definition total_exports := update_all (List.map get_module_Exports modules).

    Definition foreign_imports := LM.map foreign_spec imports.

    Definition get_module_Imports m := total_exports + foreign_imports + get_module_impl_Imports m - get_module_Exports m.

    Section module.

      Variable m : GoodModule.

      Hypothesis in_modules : List.In m modules.

      Section f.

        Variable f : GoodFunction.

        Section body.
          
          Variable im : LabelMap.LabelMap.t assert.

          Variable im_g : importsGlobal im.

          Definition mod_name := MName m.

          Definition tgt := impl_label mod_name (FName f).

          Definition body := 
            @Seq_ _ im_g mod_name
                  (AssertStar_ im mod_name accessible_labels (CompileFuncSpecMake.spec f))
                  (Goto_ im_g mod_name tgt).

        End body.

        Definition make_stub : function (MName m) :=
          (FName f, func_spec_Func f, body).

      End f.

      Definition bimports : list import := 
        bimports_base ++ List.map (Func_to_import m) (Functions m).
      
      Definition stubs := map make_stub (Functions m).

      Definition bexports := map (@func_to_import _) stubs.

      Definition bimports_diff_bexports := diff_map bimports bexports.

      Definition make_module := StructuredModule.bmodule_ bimports_diff_bexports stubs.

      Lemma In_exports : forall l, LabelMap.In l exports -> exists m f, List.In m modules /\ List.In f (Functions m) /\ l = (MName m, FName f).
        intros.
        unfold exports in *.
        eapply In_to_map in H.
        unfold InKey in *.
        eapply in_map_iff in H.
        openhyp.
        rewrite <- H in *.
        clear H.
        rename H0 into H.
        eapply In_app_all_elim in H.
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

      Import P.
      Import F.

      Lemma NoDupKey_bimports_base : NoDupKey bimports_base.
        eapply NoDupKey_NoDup_fst.
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
        Lemma mapi_4 :
          forall (elt B : Type) (f : Make.LM.key -> elt -> B) (k : Make.LM.key) (m : Make.LM.t elt),
            Make.LM.In (elt:=B) k (Make.LM.mapi f m) -> Make.LM.In (elt:=elt) k m.
          admit.
        Qed.
        eapply mapi_4 in H.
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
        eapply map_in_iff; eauto.
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

      Lemma In_bimports_base_fst : forall x, List.In x bimports_base ->  LabelMap.In (fst x) imports \/ exists m f, List.In m modules /\ List.In f (Functions m) /\ fst x = (MName m, FName f).
        intros.
        unfold bimports_base in *.
        eapply in_app_or in H.
        openhyp.
        left.
        destruct x.
        simpl.
        eapply InA_eqke_In in H.
        eapply LabelMap.elements_2 in H.
        eapply F.map_in_iff.
        eexists.
        eauto.
        right.
        destruct x.
        simpl.
        eapply InA_eqke_In in H.
        eapply LabelMap.elements_2 in H.
        eapply MapsTo_In in H.
        eapply mapi_4 in H.
        eapply In_exports; eauto.
      Qed.

      Lemma bimports_base_good_names : forall x, List.In x bimports_base -> IsGoodModuleName (fst (fst x)).
        intros.
        eapply In_bimports_base_fst in H.
        openhyp.
        eauto.
        rewrite H1 in *.
        simpl.
        eapply GoodModule_GoodName.
      Qed.

      Lemma NoDupKey_bimports : NoDupKey bimports.
        unfold bimports.
        eapply NoDupKey_app.
        eapply NoDupKey_bimports_base.
        eapply NoDupKey_NoDup_fst.
        erewrite map_map.
        unfold Func_to_import.
        simpl.
        unfold FName.
        erewrite <- map_map.
        eapply Injection_NoDup.
        eapply impl_label_is_injection.
        eapply NoDupFuncNames.
        unfold DisjointKey.
        unfold InKey.
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

      Lemma GoodModule_NoDup_labels : forall a : GoodModule, NoDup (map (fun x : GoodFunction => (MName a, FName x)) (Functions a)).
        destruct a; simpl in *.
        unfold FName.
        eauto.
        generalize NoDupFuncNames; intro HH.
        eapply Injection_NoDup with (f := fun s => (Name, s)) in HH.
        rewrite map_map in HH.
        eauto.
        unfold IsInjection; intuition.
      Qed.

      Lemma NoDupKey_app_all : 
        forall ls : list GoodModule, 
          NoDup (map MName ls) -> 
          NoDupKey (app_all (map get_module_exports ls)).
        clear.
        induction ls; simpl; intros.
        econstructor.
        eapply NoDupKey_app.
        eapply NoDupKey_NoDup_fst.
        unfold get_module_exports.
        rewrite map_map.
        simpl.
        eapply GoodModule_NoDup_labels.
        eapply IHls.
        inversion H; subst.
        eauto.
        unfold DisjointKey.
        unfold InKey.
        intros.
        intuition.
        eapply in_map_iff in H1.
        openhyp.
        subst.
        unfold get_module_exports in H1.
        eapply in_map_iff in H1.
        openhyp.
        subst.
        rewrite map_app_all in H2.
        eapply In_app_all_elim in H2.
        openhyp.
        rewrite map_map in H2.
        simpl in *.
        unfold get_module_exports in H2.
        eapply in_map_iff in H2.
        openhyp.
        subst.
        rewrite map_map in H0.
        simpl in *.
        eapply in_map_iff in H0.
        openhyp.
        injection H0; intros; subst.
        rewrite <- H5 in *.
        eapply in_map with (f := MName) in H3.
        inversion H; subst.
        contradiction.
      Qed.

      Lemma incl_bexports_bimports : incl bexports bimports.
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
        eapply InA_eqke_In.
        eapply LabelMap.elements_1.
        unfold func_spec_Func.
        eapply LabelMap.find_2.
        Lemma find_mapi :
          forall (elt B : Type) (f : Make.LM.key -> elt -> B) (k : Make.LM.key) 
                 (v : elt) (m : Make.LM.t elt),
            Make.LM.find (elt:=elt) k m = Some v ->
            Make.LM.find (elt:=B) k (Make.LM.mapi f m) = Some (f k v).
          admit.
        Qed.
        erewrite find_mapi.
        f_equal.
        instantiate (1 := x).
        reflexivity.
        eapply LabelMap.find_1.
        eapply MapsTo_to_map.
        eapply NoDupKey_app_all; eauto.
        eapply In_app_all_intro.
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
        eapply InA_eqke_In; intuition.
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
          (forall x, List.In x lbls -> LabelMap.LabelMap.find (x : Labels.label) imps <> None) ->
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
        eapply NoDupKey_bimports.
        eapply NoDup_app_find_list.
        eapply NoDupKey_unapp1.
        eapply NoDupKey_bimports.
        unfold bimports, bimports_base.
        intuition.
        rewrite find_list_elements.
        eapply find_map; eauto.
      Qed.

      Corollary in_imports_in_bimports : forall x, LabelMap.In x imports -> List.In x (map fst bimports).
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

      Lemma exports_bimports : forall k v, LabelMap.find k exports = Some v -> find_list k bimports = Some (func_spec (snd k) v).
        unfold bimports, bimports_base.
        intros.
        eapply NoDup_app_find_list.
        eapply NoDupKey_bimports.
        eapply NoDup_app_find_list_2.
        eapply NoDupKey_unapp1.
        eapply NoDupKey_bimports.
        unfold bimports, bimports_base.
        intuition.
        rewrite find_list_elements.
        unfold func_spec_Func.
        erewrite find_mapi; eauto.
      Qed.

      Corollary in_exports_in_bimports : forall x, LabelMap.In x exports -> List.In x (map fst bimports).
      unfold bimports, bimports_base.
      intros.
      erewrite map_app.
      eapply in_or_app.
      left.
      erewrite map_app.
      eapply in_or_app.
      right.
      eapply In_fst_elements_In.
      Lemma mapi_3 :
        forall (elt B : Type) (f : Make.LM.key -> elt -> B) (k : Make.LM.key) (m : Make.LM.t elt),
          Make.LM.In (elt:=elt) k m -> Make.LM.In (elt:=B) k (Make.LM.mapi f m).
        admit.
      Qed.
      eapply mapi_3; eauto.
      Qed.

      Lemma NoDupKey_bexports : NoDupKey bexports.
        unfold bexports.
        unfold stubs.
        rewrite map_map.
        unfold func_to_import.
        unfold make_stub; simpl in *.
        eapply NoDupKey_NoDup_fst.
        rewrite map_map.
        simpl.
        eapply GoodModule_NoDup_labels.
      Qed.
      
      Lemma NoDup_union : NoDupKey (bimports_diff_bexports ++ bexports).
        unfold bimports_diff_bexports.
        eapply NoDupKey_app.
        eapply diff_NoDupKey.
        eapply NoDupKey_bimports.
        eapply NoDupKey_bexports.
        eapply diff_DisjointKey.
      Qed.

      Lemma Equal_union_bimports : Equal_map (bimports_diff_bexports ++ bexports) bimports.
        unfold bimports_diff_bexports.
        eapply diff_union.
        eapply NoDupKey_bimports.
        eapply NoDupKey_bexports.
        eapply incl_bexports_bimports.
      Qed.

      Definition full_imports := fullImports bimports_diff_bexports stubs.

      Lemma fullImports_eq_bimports : forall (k : label), LabelMap.LabelMap.find (k : Labels.label) full_imports = find_list k bimports.
        intros.
        unfold full_imports in *.
        erewrite fullImports_spec.
        eapply Equal_union_bimports.
        eapply NoDup_union.
      Qed.

      Corollary bimports_fullImports : forall (x : label), List.In x (map fst bimports) -> LabelMap.LabelMap.find (x : Labels.label) full_imports <> None.
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
          List.In x accessible_labels ->
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

      Lemma exports_accessible_labels : forall l, LabelMap.find l exports <> None -> List.In l accessible_labels.
        unfold accessible_labels.
        intros.
        eapply in_or_app.
        right.
        unfold keys in *; eapply In_fst_elements_In.
        eapply In_find_not_None; eauto.
      Qed.
      
      Lemma exports_fullImports : forall (l : label) spec, LabelMap.find l exports = Some spec -> LabelMap.LabelMap.find (l : Labels.label) full_imports = Some (func_spec (snd l) spec).
        intros.
        rewrite fullImports_eq_bimports.
        eapply exports_bimports; eauto.
      Qed.

      Lemma tgt_fullImports : forall f, List.In f (Functions m) -> LabelMap.LabelMap.find (tgt f : Labels.label) full_imports = Some (CompileFuncSpecMake.spec f).
        intros.
        rewrite fullImports_eq_bimports. 
        unfold bimports, bimports_base.
        eapply NoDup_app_find_list_2.
        eapply NoDupKey_bimports.
        unfold tgt.
        unfold mod_name.
        eapply In_find_list_Some.
        eapply NoDupKey_unapp2.
        eapply NoDupKey_bimports.
        unfold bimports, bimports_base.
        intuition.
        unfold Func_to_import in *; simpl in *.
        eapply in_map with (f := fun x => Func_to_import m x) in H.
        eapply InA_eqke_In.
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
        eapply InA_eqke_In.
        eauto.
        intuition.
        intuition.
        rewrite e1 in H0; intuition.
        rewrite e1 in e0; intuition.
        rewrite e0 in H.
        intuition.
      Qed.

      Lemma imports_accessible_labels : forall l, LabelMap.find l imports <> None -> List.In l accessible_labels.
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
          exists id, specs p = Some (func_spec id spec).
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
        eapply specs_internal in H; eauto.
        post; descend.
        eauto.

        unfold func_spec.
        unfold spec_without_funcs_ok at 2.
        step auto_ext.
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

      Lemma good_vcs : forall ls, (forall x, List.In x ls -> List.In x (Functions m)) -> vcs (makeVcs bimports_diff_bexports stubs (map make_stub ls)).
        induction ls; simpl; eauto.
        Opaque funcs_ok.
        Opaque spec_without_funcs_ok.
        wrap0.
        descend.

        eapply fs_funcs_ok; eauto.

        eapply Imply_sound.
        eauto.
        step auto_ext.
        simpl in *.
        Lemma augment_fs_good_to_use : forall specs stn, augment (fullImports bimports_diff_bexports stubs) specs stn accessible_labels -> fs_good_to_use fs stn.
          admit.
        Qed.
        eapply augment_fs_good_to_use; eauto.

        erewrite tgt_fullImports; eauto.
      Qed.        

      Lemma InKey_exports_elim : forall A (f : _ -> A) (ms : list GoodModule) m lbl, List.In m ms -> NoDup (map MName ms) -> fst lbl = MName m -> InKey lbl (app_all (map get_module_exports ms)) -> InKey lbl (map (fun x : GoodFunction => (MName m, FName x, f x)) (Functions m)).
        clear.
        induction ms; simpl; intros.
        unfold InKey in *; simpl in *; intuition.
        destruct H.
        subst.
        eapply inkey_app_or in H2.
        destruct H2.
        unfold get_module_exports in *.
        unfold InKey in *.
        rewrite map_map in *.
        simpl in *.
        eauto.
        unfold InKey in H.
        eapply in_map_iff in H.
        openhyp.
        subst.
        eapply In_app_all_elim in H2.
        openhyp.
        eapply in_map_iff in H2.
        openhyp.
        subst.
        unfold get_module_exports in *.
        eapply in_map_iff in H.
        openhyp.
        subst.
        simpl in *.
        rewrite <- H1 in *.
        inversion H0; subst.
        eapply in_map with (f := MName) in H3.
        contradiction.
        eapply inkey_app_or in H2.
        destruct H2.
        unfold InKey in H2.
        eapply in_map_iff in H2.
        openhyp.
        subst.
        unfold get_module_exports in H3.
        eapply in_map_iff in H3.
        openhyp.
        subst.
        simpl in *.
        rewrite H1 in *.
        inversion H0; subst.
        eapply in_map with (f := MName) in H.
        contradiction.
        eapply IHms; eauto.
        inversion H0; subst.
        eauto.
      Qed.

      Require Import StringFacts2.

      Require Import NameVC.

      Lemma module_name_not_in_bimports_diff_bexports : ~ List.In (MName m) (map fst2 bimports_diff_bexports).
        intuition.
        unfold fst_2 in *.
        rewrite <- map_map in H.
        eapply in_map_iff in H.
        openhyp.
        destruct x; simpl in *.
        subst.
        unfold bimports_diff_bexports in *.
        eapply diff_In in H0.
        openhyp.
        contradict H0.
        unfold bimports in *.
        eapply inkey_app_or in H.
        unfold Func_to_import in *.
        openhyp.
        unfold bimports_base in *.
        eapply inkey_app_or in H.
        openhyp.
        eapply In_fst_elements_In in H.
        eapply map_4 in H.
        unfold imported_module_names in *.
        unfold Disjoint in *.
        exfalso.
        eapply NoSelfImport with (e := MName m).
        split.
        unfold module_names.
        eapply in_map; eauto.

        eapply In_fst_elements_In in H.
        eapply in_map with (f := fst) in H.
        simpl in *.
        rewrite map_map in H.
        eauto.

        eapply In_fst_elements_In in H.
        eapply mapi_4 in H.
        unfold exports in *.
        eapply In_to_map in H.
        unfold bexports.
        unfold func_to_import.
        unfold stubs.
        unfold make_stub.
        rewrite map_map.
        simpl in *.
        eapply InKey_exports_elim; eauto.

        unfold InKey in H.
        rewrite map_map in H.
        simpl in *.
        unfold impl_label in *.
        eapply in_map_iff in H.
        openhyp.
        injection H; intros.
        contradict H2.
        eapply prefix_neq.
        intuition.
      Qed.

      Lemma module_name_not_in_imports : NameNotInImports (MName m) bimports_diff_bexports.
        eapply NotIn_NameNotInImports.
        eapply module_name_not_in_bimports_diff_bexports.        
      Qed.

      Lemma no_dup_func_names : NoDupFuncNames stubs.
        eapply NoDup_NoDupFuncNames.
        unfold stubs.
        rewrite map_map.
        unfold make_stub; simpl in *.
        destruct m; simpl in *.
        eauto.
      Qed.
      
      Import LM.

      Require Import GeneralTactics2.

      Existing Instance to_blm_Equal_m_Proper.
      Existing Instance CompatReflSym_Symmetric.
      Existing Instance CompatReflSym_Reflexive.
      Existing Instance Compat_m_Proper.
      Existing Instance Disjoint_m_Symmetric.

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

      Lemma Disjoint_many_exports_foreign_imports : forall ms, incl ms modules -> Disjoint (update_all (List.map get_module_Exports ms)) foreign_imports.
        intros.
        symmetry.
        eapply Disjoint_update_all.
        eapply Forall_forall.
        intros.
        eapply in_map_iff in H0.
        openhyp.
        subst.
        symmetry.
        eapply Disjoint_exports_foreign_imports; eauto.
      Qed.

      Lemma Compat_many_exports_foreign_imports : forall ms, incl ms modules -> Compat (update_all (List.map get_module_Exports ms)) foreign_imports.
        intros.
        eapply Disjoint_Compat.
        eapply Disjoint_many_exports_foreign_imports; eauto.
      Qed.

      Lemma Compat_total_exports_foreign_imports : Compat total_exports foreign_imports.
        unfold total_exports.
        eapply Compat_many_exports_foreign_imports; intuition.
      Qed.

      Require Import ListFacts3.
      Require Import Morphisms.
(*here*)
      Lemma Equal_get_module_Exports : forall m, map spec_without_funcs_ok_fs (of_list (get_module_exports m)) == get_module_Exports m.
        intros.
        unfold get_module_Exports.
        unfold to_map.
        unfold get_module_exports.
        rewrite map_of_list.
        rewrite map_map.
        simpl.
        reflexivity.
      Qed.

      Lemma exports_Equal_total_exports : map spec_without_funcs_ok_fs exports == total_exports.
        unfold exports.
        unfold total_exports.
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

      Lemma bimports_base_Equal_update : of_list bimports_base == total_exports + foreign_imports.
        intros.
        rewrite Compat_update_sym.
        Focus 2.
        eapply Compat_total_exports_foreign_imports.
        unfold bimports_base.
        rewrite of_list_app.
        rewrite of_list_3.
        rewrite of_list_3.
        rewrite exports_Equal_total_exports.
        reflexivity.
        eapply NoDupKey_bimports_base; eauto.
      Qed.

      Lemma bimports_Equal_update_update : of_list bimports == total_exports + foreign_imports + get_module_impl_Imports m.
        intros.
        unfold bimports.
        rewrite of_list_app.
        rewrite bimports_base_Equal_update.
        reflexivity.
        eapply NoDupKey_bimports; eauto.
      Qed.

      Lemma bexports_Equal_exports : of_list bexports == get_module_Exports m.
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

      (* Interface *)

      Theorem make_module_ok : XCAP.moduleOk make_module.
        eapply bmoduleOk.
        eapply module_name_not_in_imports.
        eapply no_dup_func_names.
        eapply good_vcs; eauto.
      Qed.

      Lemma make_module_Imports : Imports make_module === get_module_Imports m.
        intros.
        unfold make_module, bmodule_, Imports.
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

      Lemma make_module_Exports : Exports make_module === get_module_Exports m.
        intros.
        unfold make_module, bmodule_, Imports; simpl.
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

      Lemma make_module_Modules : SS.Equal (Modules make_module) (singleton (MName m)).
        intros.
        unfold make_module, bmodule_, Modules.
        reflexivity.
      Qed.

    End module.

  End TopSection.

End Make.
