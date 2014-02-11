Set Implicit Arguments.

Require Import ADT.
Require Import RepInv.

Definition Disjoint A ls1 ls2 := forall e : A, ~ (List.In e ls1 /\ List.In e ls2).

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

  Require Import AutoSep.
  Require Import StructuredModule.
  Require Import GoodModule.
  Require Import GoodFunction.
  Require Import ConvertLabel.
  Require Import NameDecoration.
  Require Import Sumbool.
  Require Import Wrap.

  Section TopSection.

    Variable modules : list GoodModule.

    Variable imports : LabelMap.t ForeignFuncSpec.

    Definition FName := SyntaxFunc.Name.

    Definition MName := GoodModule.Name.

    Fixpoint flatten A (ls : list (list A)) :=
      match ls with
        | nil => nil
        | x :: xs => x ++ flatten xs
      end.

    Definition to_internal_func_spec (f : GoodFunction) : InternalFuncSpec :=
      {|
        Semantics.Fun := f;
        Semantics.NoDupArgVars := proj1 (IsGoodFunc f)
      |}.

    Coercion to_internal_func_spec : GoodFunction >-> InternalFuncSpec.

    Definition exports :=
      to_map
        (flatten 
           (List.map 
              (fun m =>
                 List.map 
                   (fun (f : GoodFunction) =>
                      ((MName m, FName f), f : InternalFuncSpec)
                   ) (Functions m)
              ) modules)).

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

      Definition make_module := StructuredModule.bmodule_ bimports stubs.

      Definition module_names := map MName modules.
      Definition imported_module_names := map (fun x => fst (fst x)) (LabelMap.elements imports).

      Hypothesis NoDupModuleNames : NoDup module_names.

      Hypothesis NoSelfImport : Disjoint module_names imported_module_names.

      Lemma NoDupKey_NoDup_fst : forall elt ls, @NoDupKey elt ls <-> NoDup (map fst ls).
        admit.
      Qed.

      Lemma NoDup_app : forall A (ls1 ls2 : list A), NoDup ls1 -> NoDup ls2 -> Disjoint ls1 ls2 -> NoDup (ls1 ++ ls2).
        admit.
      Qed.

      Lemma Disjoint_map : forall A B (f : A -> B) ls1 ls2, Disjoint (map f ls1) (map f ls2) -> Disjoint ls1 ls2.
        admit.
      Qed.
      Definition Equal A ls1 ls2 := forall x : A, List.In x ls1 <-> List.In x ls2.
      Lemma Disjoint_incl : forall A (ls1 ls2 ls1' ls2' : list A), Disjoint ls1 ls2 -> List.incl ls1' ls1 -> List.incl ls2' ls2 -> Disjoint ls1' ls2'.
        admit.
      Qed.
      Require Import GeneralTactics.
      Lemma Disjoint_symm : forall A (ls1 ls2 : list A), Disjoint ls1 ls2 -> Disjoint ls2 ls1.
        admit.
      Qed.

      Lemma In_to_map : forall A ls k, @LabelMap.In A k (to_map ls) <-> List.In k (map fst ls).
        admit.
      Qed.
      Lemma In_flatten : forall A lsls (x : A), List.In x (flatten lsls) -> exists ls, List.In x ls /\ List.In ls lsls.
        admit.
      Qed.

      Lemma incl_map : forall A B (f : A -> B) ls1 ls2, incl ls1 ls2 -> incl (map f ls1) (map f ls2).
        admit.
      Qed.

      Lemma In_fst_elements_In : forall A m k, In k (map fst (LabelMap.elements m)) <-> @LabelMap.In A k m.
        split; intros.
        eapply InA_eq_List_In in H.
        eapply In_In_keys in H; eauto.
        eapply InA_eq_List_In.
        specialize In_In_keys; intros; unfold keys in *; eapply H0; eauto.
      Qed.

      Lemma map_4 : forall elt B (f : elt -> B) k m, LabelMap.In k (LabelMap.map f m) -> LabelMap.In k m.
        intros; eapply F.map_in_iff; eauto.
      Qed.

      Lemma In_exports : forall l, LabelMap.In l exports -> exists m f, In m modules /\ In f (Functions m) /\ l = (MName m, FName f).
        intros.
        unfold exports in *.
        eapply In_to_map in H.
        eapply in_map_iff in H.
        openhyp.
        rewrite <- H in *.
        clear H.
        rename H0 into H.
        eapply In_flatten in H.
        openhyp.
        eapply in_map_iff in H0.
        openhyp.
        rewrite <- H0 in *.
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

      Definition IsInjection A B (f : A -> B) := forall x y, x <> y -> f x <> f y.

      Lemma Injection_NoDup : forall A B (f : A -> B) ls, IsInjection f -> NoDup ls -> NoDup (map f ls).
        admit.
      Qed.

      Lemma impl_label_is_injection : forall mn, IsInjection (impl_label mn).
        admit.
      Qed.

      Definition IsGoodModuleName (s : string) := prefix "_" s = false.

      Lemma IsGoodModuleName_not_impl_module_name : forall s, IsGoodModuleName s -> ~ exists s', impl_module_name s' = s.
        admit.
      Qed.


      Hypotheses ImportsGoodModuleName : forall l, LabelMap.In l imports -> IsGoodModuleName (fst l).

      Lemma MapsTo_In : forall elt k v m, LabelMap.MapsTo k v m -> @LabelMap.In elt k m.
        intros; eexists; eauto.
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

      Lemma GoodModule_GoodName : forall m : GoodModule, IsGoodModuleName (MName m).
        admit.
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

      Definition importsMap' (imports : list import) base :=
        List.fold_left 
          (fun m p => 
             let '(modl, f, pre) := p in
             LabelMap.LabelMap.add (modl, Global f) pre m) imports base.

      Lemma find_importsMap_find_list' : 
        forall imps2 imps1 base, 
          NoDupKey (imps1 ++ imps2) -> 
          (forall (k : label), LabelMap.LabelMap.find (k : Labels.label) base = find_list k imps1) ->
          forall (k : label), LabelMap.LabelMap.find (k : Labels.label) (importsMap' imps2 base) = find_list k (imps1 ++ imps2).
        induction imps2; simpl.
        intros.
        rewrite app_nil_r.
        eauto.
        intros.
        rewrite <- DepList.pf_list_simpl.
        eapply IHimps2.
        rewrite DepList.pf_list_simpl.
        eauto.
        destruct a; simpl.
        destruct k0; simpl.
        intros.
        destruct (LabelMap.LabelKey.eq_dec (k0 : Labels.label) (s, Global s0)).
        unfold LabelKey.eq in *.
        erewrite LabelMap.LabelMap.find_1.
        Focus 2.
        eapply LabelMap.LabelMap.add_1.
        eauto.
        destruct k0.
        injection e; intros; subst.
        erewrite In_find_list_Some_left.
        eauto.
        eapply NoDup_incl.
        eauto.
        set (_ ++ _ :: nil) in *.
        rewrite <- DepList.pf_list_simpl.
        unfold l in *.
        intuition.
        eapply InA_eq_key_elt_List_In; intuition.
        unfold LabelKey.eq in *.
        erewrite BLMF.add_4.
        rewrite H0.
        erewrite find_list_neq.
        eauto.
        eapply NoDup_incl.
        eauto.
        intuition.
        intuition.
        destruct k0.
        injection H1; intros; subst; intuition.
        eauto.
      Qed.

      Lemma find_importsMap_find_list : forall imps (k : label), NoDupKey imps -> LabelMap.LabelMap.find (k : Labels.label) (importsMap imps) = find_list k imps.
        intros.
        unfold importsMap.
        erewrite find_importsMap_find_list'.
        erewrite app_nil_l; eauto.
        erewrite app_nil_l; eauto.
        intros.
        unfold find_list.
        eauto.
      Qed.        

      Definition fullImports' impsMap modName (functions : list (function modName)) : LabelMap.LabelMap.t assert :=
        List.fold_left 
          (fun m p => 
             let '(f, pre, _) := p in
             LabelMap.LabelMap.add (modName, Global f) pre m) functions impsMap.

      Definition func_to_import mn (f : function mn) : import:= ((mn, fst (fst f)), snd (fst f)).

      Lemma fullImports_no_effect' : 
        forall mn (fns : list (function mn)) imps impsMap, 
          NoDupKey imps -> 
          incl (map (@func_to_import _) fns) imps -> 
          (forall (k : label), LabelMap.LabelMap.find (k : Labels.label) impsMap = find_list k imps) ->
          forall (k : label), LabelMap.LabelMap.find (k : Labels.label) (fullImports' impsMap fns) = find_list k imps.
      Proof.
        induction fns; simpl; intros.
        eauto.
        unfold fullImports'.
        destruct a.
        destruct p.
        eapply IHfns.
        eauto.
        eapply incl_tran.
        2 : eauto.
        intuition.
        intros.
        destruct (LabelMap.LabelKey.eq_dec (k0 : Labels.label) (mn, Global s)); unfold LabelKey.eq in *.
        erewrite LabelMap.LabelMap.find_1.
        Focus 2.
        eapply LabelMap.LabelMap.add_1.
        eauto.
        symmetry.
        eapply In_find_list_Some.
        eauto.
        destruct k0.
        injection e; intros; subst.
        unfold func_to_import in *; simpl in *.
        eapply InA_eq_key_elt_List_In; intuition.
        erewrite BLMF.add_4.
        eauto.
        eauto.
      Qed.

      Lemma fullImports_no_effect : forall mn (fns : list (function mn)) imps, NoDupKey imps -> incl (map (@func_to_import _) fns) imps -> forall (k : label), LabelMap.LabelMap.find (k : Labels.label) (fullImports imps fns) = find_list k imps.
        intros.
        unfold fullImports.
        specialize fullImports_no_effect'; intros.
        unfold fullImports' in *.
        eapply H1; eauto.
        intros.
        eapply find_importsMap_find_list; eauto.
      Qed.

      Lemma incl_stubs_bimports : incl (map (@func_to_import _) stubs) bimports.
        admit.
      Qed.

      Lemma find_spec : forall A f (ls : list A) a, find f ls = Some a -> f a = true /\ In a ls.
        induction ls; simpl; intuition;
        (destruct (sumbool_of_bool (f a)); 
         [rewrite e in H; injection H; intros; subst; eauto | 
          rewrite e in H; eapply IHls in H; openhyp; eauto]).
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
        eapply NoDup_incl.
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
      eapply InA_eq_List_In.
      specialize In_In_keys; intros; unfold keys in *; eapply H0.
      eapply map_3; eauto.
      Qed.

      Lemma exports_bimports : forall k v, LabelMap.find k exports = Some v -> find_list k bimports = Some (spec_without_funcs_ok v fs).
        unfold bimports, bimports_base.
        intros.
        eapply NoDup_app_find_list.
        eapply NoDup_bimports.
        eapply NoDup_app_find_list_2.
        eapply NoDup_incl.
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
      eapply InA_eq_List_In.
      specialize In_In_keys; intros; unfold keys in *; eapply H0.
      eapply map_3; eauto.
      Qed.

      Lemma fullImports_eq_bimports : forall (k : label), LabelMap.LabelMap.find (k : Labels.label) (fullImports bimports stubs) = find_list k bimports.
        intros.
        eapply fullImports_no_effect.
        eapply NoDup_bimports.
        eapply incl_stubs_bimports.
      Qed.

      Corollary bimports_fullImports : forall (x : label), In x (map fst bimports) -> LabelMap.LabelMap.find (x : Labels.label) (fullImports bimports stubs) <> None.
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
          LabelMap.LabelMap.find (x : Labels.label) (fullImports bimports stubs) <> None.
      Proof.
        unfold accessible_labels.
        intros.
        eapply in_app_or in H.
        destruct H.

        specialize In_In_keys; intros; unfold keys in *.
        eapply InA_eq_List_In in H.
        eapply H0 in H.
        eapply in_imports_in_bimports in H.
        eapply bimports_fullImports; eauto.

        specialize In_In_keys; intros; unfold keys in *.
        eapply InA_eq_List_In in H.
        eapply H0 in H.
        eapply in_exports_in_bimports in H.
        eapply bimports_fullImports; eauto.
      Qed.

      Lemma exports_accessible_labels : forall l, LabelMap.find l exports <> None -> In l accessible_labels.
        unfold accessible_labels.
        intros.
        eapply in_or_app.
        right.
        specialize In_In_keys; intros; unfold keys in *.
        eapply InA_eq_List_In.
        eapply H0.
        eapply In_find_not_None; eauto.
      Qed.
      
      Lemma exports_fullImports : forall (l : label) spec, LabelMap.find l exports = Some spec -> LabelMap.LabelMap.find (l : Labels.label) (fullImports bimports stubs) = Some (spec_without_funcs_ok spec fs).
        intros.
        rewrite fullImports_eq_bimports.
        eapply exports_bimports; eauto.
      Qed.

      Lemma tgt_fullImports : forall f, In f (Functions m) -> LabelMap.LabelMap.find (tgt f : Labels.label) (fullImports bimports stubs) = Some (CompileFuncSpecMake.spec f).
        intros.
        rewrite fullImports_eq_bimports. 
        unfold bimports, bimports_base.
        eapply NoDup_app_find_list_2.
        eapply NoDup_bimports.
        unfold tgt.
        unfold mod_name.
        eapply In_find_list_Some.
        eapply NoDup_incl.
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
        specialize In_In_keys; intros; unfold keys in *.
        eapply InA_eq_List_In.
        eapply H0.
        eapply In_find_not_None; eauto.
      Qed.
      
      Lemma imports_fullImports : forall (l : label) spec, LabelMap.find l imports = Some spec -> LabelMap.LabelMap.find (l : Labels.label) (fullImports bimports stubs) = Some (foreign_spec spec).
        intros.
        rewrite fullImports_eq_bimports.
        eapply imports_bimports; eauto.
      Qed.

      Lemma specs_internal :
        forall specs stn p spec,
          augment (fullImports bimports stubs) specs stn accessible_labels ->
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
          augment (fullImports bimports stubs) specs stn accessible_labels ->
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
          augment (fullImports bimports stubs) specs stn accessible_labels ->
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

      Hypothesis in_modules : In m modules.

      Lemma good_vcs : forall ls, (forall x, In x ls -> In x (Functions m)) -> vcs (makeVcs bimports stubs (map make_stub ls)).
        induction ls; simpl; eauto.
        Opaque funcs_ok.
        Opaque spec_without_funcs_ok.
        wrap0.
        descend.

        eapply fs_funcs_ok; eauto.

        eauto.

        erewrite tgt_fullImports; eauto.
      Qed.        

      Theorem make_module_ok : XCAP.moduleOk make_module.
        eapply bmoduleOk.
        admit.
        admit.
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
