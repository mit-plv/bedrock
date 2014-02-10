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
  Module Import FMapFacts1LabelMapMake := WFacts_fun Key' LabelMap.

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

        Definition make_stub : function (GoodModule.Name m) :=
          (FName f, spec_without_funcs_ok f fs, body).

      End f.

      Definition Func_to_import (f : GoodFunction) := (impl_label (MName m) (FName f), CompileFuncSpecMake.spec f).

      Definition bimports : list import := 
        bimports_base ++ List.map Func_to_import (Functions m).
      
      Definition stubs := map make_stub (Functions m).

      Definition make_module := StructuredModule.bmodule_ bimports stubs.

      Lemma NoDup_bimports : NoDupKey bimports.
        admit.
      Qed.

      Definition importsMap' (imports : list import) base :=
        List.fold_left 
          (fun m p => 
             let '(modl, f, pre) := p in
             LabelMap.LabelMap.add (modl, Global f) pre m) imports base.

      Require Import SetoidList.
      Require Import GeneralTactics.
      Lemma InA_eq_List_In : forall elt ls x, InA (@eq elt) x ls <-> List.In x ls.
        induction ls; simpl; intros.
        intuition.
        eapply InA_nil in H; eauto.
        split; intros.
        inversion H; subst.
        eauto.
        right.
        eapply IHls.
        eauto.
        destruct H.
        subst.
        econstructor 1.
        eauto.
        econstructor 2.
        eapply IHls.
        eauto.
      Qed.

      Definition equiv_2 A B p1 p2 := forall (a : A) (b : B), p1 a b <-> p2 a b.

      Lemma equiv_2_trans : forall A B a b c, @equiv_2 A B a b -> equiv_2 b c -> equiv_2 a c.
        unfold equiv_2; intros; split; intros.
        eapply H0; eapply H; eauto.
        eapply H; eapply H0; eauto.
      Qed.

      Lemma eq_key_elt_eq : forall elt, equiv_2 (@LabelMap.eq_key_elt elt) eq.
        split; intros.
        unfold LabelMap.eq_key_elt in *.
        unfold LabelMap.Raw.PX.eqke in *.
        openhyp.
        destruct a; destruct b; simpl in *; subst; eauto.
        subst.
        unfold LabelMap.eq_key_elt in *.
        unfold LabelMap.Raw.PX.eqke in *.
        eauto.
      Qed.

      Lemma equiv_InA : forall elt (eq1 eq2 : elt -> elt -> Prop), equiv_2 eq1 eq2 -> equiv_2 (InA eq1) (InA eq2).
        unfold equiv_2; split; intros; eapply InA_weaken; eauto; intros; eapply H; eauto.
      Qed.

      Lemma InA_eq_key_elt_InA_eq : forall elt, equiv_2 (InA (@LabelMap.eq_key_elt elt)) (InA eq).
        intros; eapply equiv_InA; eapply eq_key_elt_eq.
      Qed.

      Lemma InA_eq_key_elt_List_In : forall elt ls x, InA (@LabelMap.eq_key_elt elt) x ls <-> List.In x ls.
        intros; eapply equiv_2_trans.
        eapply InA_eq_key_elt_InA_eq.
        unfold equiv_2; intros; eapply InA_eq_List_In.
      Qed.

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
