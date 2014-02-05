Require Import CompileFuncSpec.

Set Implicit Arguments.

Require Import Label.

Section TopSection.

  Require Import GoodModule.
  Variable modules : list GoodModule.

  Require Import Semantics.
  Variable imports : LabelMap.t ForeignFuncSpec.

  Definition FName := SyntaxFunc.Name.

  Definition MName := GoodModule.Name.

  Fixpoint flatten A (ls : list (list A)) :=
    match ls with
      | nil => nil
      | x :: xs => x ++ flatten xs
    end.

  Definition to_map B ls :=
    List.fold_left
      (fun m p => LabelMap.add (fst p) (snd p) m)
      ls (LabelMap.empty B).

  Require Import GoodFunction.
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

  Definition keys A (m : LabelMap.t A) := map fst (LabelMap.elements m).

  Definition accessible_labels := keys imports ++ keys exports.

  Section fs.

    Variable stn : settings.

    Require Import ConvertLabel Label.
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

  Require Import Inv.

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

          Require Import NameDecoration.

          Definition impl_label mod_name f_name : label := (impl_module_name mod_name, f_name).

          Definition tgt := impl_label mod_name (FName f).

          Require Import AutoSep.
          Definition body := 
            @Seq_ _ im_g mod_name
                 (AssertStar_ im mod_name accessible_labels (spec f))
                 (Goto_ im_g mod_name tgt).

        End body.

        Require Import StructuredModule.
        Definition make_stub : function (GoodModule.Name m) :=
          (FName f, spec_without_funcs_ok f fs, body).

      End f.

      Definition Func_to_import (f : GoodFunction) := (impl_label (MName m) (FName f), CompileFuncSpec.spec f).

      Definition bimports : list import := 
        bimports_base ++ List.map Func_to_import (Functions m).
          
      Definition stubs := map make_stub (Functions m).

      Definition make_module := StructuredModule.bmodule_ bimports stubs.

      Definition eqb x y := if Label.Key.eq_dec x y then true else false.

      Definition find_as_map B k (ls : list (label * B)) : option B :=
        SetoidList.findA (eqb k) ls.

      Definition option_dec A (x : option A) : {a | x = Some a} + {x = None}.
        destruct x.
        left.
        exists a.
        eauto.
        right.
        eauto.
      Qed.

      Require Import GeneralTactics.

      Definition NoDupKey A := SetoidList.NoDupA (@LabelMap.eq_key A).

      Lemma NoDup_app_find_as_map : forall A m1 m2 k (v : A), NoDupKey (m1 ++ m2) -> find_as_map k m1 = Some v -> find_as_map k (m1 ++ m2) = Some v.
        admit.
      Qed.

      Lemma NoDup_app_find_as_map_2 : forall A m1 m2 k (v : A), NoDupKey (m1 ++ m2) -> find_as_map k m2 = Some v -> find_as_map k (m1 ++ m2) = Some v.
        admit.
      Qed.

      Lemma NoDup_bimports : NoDupKey bimports.
        admit.
      Qed.

      Lemma NoDup_incl : forall A a b, @NoDupKey A b -> incl a b -> NoDupKey a.
        admit.
      Qed.

      Lemma NoDup_cons : forall A ls k1 (v1 : A) k2 v2, NoDupKey ((k1, v1) :: ls) -> In (k2, v2) ls -> k1 <> k2.
        admit.
      Qed.

      Lemma InA_In : forall A p ls, SetoidList.InA (LabelMap.eq_key_elt (elt := A)) p ls <-> In p ls.
        admit.
      Qed.

      Lemma In_find_as_map_Some_left : forall A k (v : A) ls, NoDupKey ls -> In (k, v) ls -> find_as_map k ls = Some v.
      Proof.
        induction ls; simpl; intros.
        intuition.
        destruct H0.
        unfold find_as_map in *; destruct a; simpl in *.
        injection H0; intros; subst.
        unfold eqb in *.
        destruct (Key.eq_dec k k); intuition.
        destruct a; simpl in *.
        generalize H0; eapply NoDup_cons in H0; eauto; intro.
        eapply IHls in H1.
        unfold find_as_map in *; simpl in *.
        unfold eqb in *.
        destruct (Key.eq_dec k k0); intuition.
        eapply NoDup_incl.
        eauto.
        intuition.
      Qed.

      Lemma In_find_as_map_Some_right : forall A k (v : A) ls, NoDupKey ls -> find_as_map k ls = Some v -> In (k, v) ls.
      Proof.
        induction ls; simpl; intros.
        unfold find_as_map in *; simpl in *.
        intuition.
        unfold find_as_map in *; destruct a; simpl in *.
        unfold eqb in *.
        destruct (Key.eq_dec k k0); intuition.
        injection H0; intros; subst.
        eauto.
        right.
        eapply IHls.
        eapply NoDup_incl.
        eauto.
        intuition.
        eauto.
      Qed.

      Lemma In_find_as_map_Some : forall A k (v : A) ls, NoDupKey ls -> (In (k, v) ls <-> find_as_map k ls = Some v).
        split; intros.
        eapply In_find_as_map_Some_left; eauto.
        eapply In_find_as_map_Some_right; eauto.
      Qed.

      Lemma In_find_Some : forall A k (v : A) m, In (k, v) (LabelMap.elements m) <-> LabelMap.find k m = Some v.
        split; intros.
        eapply LabelMap.find_1.
        eapply LabelMap.elements_2.
        eapply InA_In; eauto.
        eapply LabelMap.find_2 in H.
        eapply LabelMap.elements_1 in H.
        eapply InA_In; eauto.
      Qed.

      Lemma None_not_Some : forall A (a : option A), a = None <-> ~ exists v, a = Some v.
        split; intros.
        intuition.
        openhyp.
        intuition.
        destruct (option_dec a); eauto.
        destruct s.
        contradict H.
        eexists; eauto.
      Qed.

      Lemma find_as_map_elements : forall A k (m : LabelMap.t A), find_as_map k (LabelMap.elements m) = LabelMap.find k m.
        intros.
        destruct (option_dec (LabelMap.find k m0)).
        destruct s.
        rewrite e.
        eapply In_find_Some in e.
        eapply In_find_as_map_Some in e.
        eauto.
        eapply LabelMap.elements_3w.
        rewrite e.
        eapply None_not_Some in e.
        eapply None_not_Some.
        intuition.
        contradict e.
        openhyp.
        eapply In_find_as_map_Some in H.
        eapply In_find_Some in H.
        eexists; eauto.
        eapply LabelMap.elements_3w.
      Qed.

      Lemma In_find_as_map_not_None_left : forall B (ls : list (label * B)) k, In k (map fst ls) -> find_as_map k ls <> None.
      Proof.
        induction ls; simpl; intros.
        intuition.
        destruct H.
        unfold find_as_map in *; destruct a; simpl in *.
        unfold eqb in *.
        destruct (Key.eq_dec k l); intuition.
        eapply IHls in H.
        unfold find_as_map in *; destruct a; simpl in *.
        destruct (eqb k l); intuition.
      Qed.

      Lemma In_find_as_map_not_None_right : forall B (ls : list (label * B)) k, find_as_map k ls <> None -> In k (map fst ls).
      Proof.
        induction ls; simpl; intros.
        intuition.
        unfold find_as_map in *; destruct a; simpl in *.
        unfold eqb in *.
        destruct (Key.eq_dec k l); intuition.
      Qed.

      Lemma In_find_as_map_not_None : forall B (ls : list (label * B)) k, In k (map fst ls) <-> find_as_map k ls <> None.
        intros.
        split.
        eapply In_find_as_map_not_None_left.
        eapply In_find_as_map_not_None_right.
      Qed.

      Lemma In_find_not_None : forall A k (m : LabelMap.t A), LabelMap.find k m <> None <-> LabelMap.In k m.
        unfold LabelMap.In.
        unfold LabelMap.Raw.PX.In.
        split; intros.
        eapply ex_up in H.
        openhyp.
        eapply LabelMap.find_2 in H.
        eexists; eauto.

        openhyp.
        eapply LabelMap.find_1 in H.
        intuition.
      Qed.

      Lemma In_In_keys : forall A k (m : LabelMap.t A), LabelMap.In k m <-> In k (keys m).
        split; intros.
        eapply In_find_not_None in H.
        eapply In_find_as_map_not_None.
        rewrite find_as_map_elements.
        eauto.
        eapply In_find_not_None.
        unfold keys in *.
        eapply In_find_as_map_not_None in H.
        rewrite find_as_map_elements in H.
        eauto.
      Qed.

      Definition func_to_import mn (f : function mn) : import:= ((mn, fst (fst f)), snd (fst f)).

      Lemma fullImports_no_effect : forall mn (fns : list (function mn)) imps, NoDupKey imps -> incl (map (@func_to_import _) fns) imps -> forall (k : label), LabelMap.LabelMap.find (k : Labels.label) (fullImports imps fns) = find_as_map k imps.
      Proof.
        induction fns; simpl; intros.
        unfold fullImports.
        simpl.
        Lemma find_importsMap_find_as_map : forall imps (k : label), LabelMap.LabelMap.find (k : Labels.label) (importsMap imps) = find_as_map k imps.
          Definition importsMap' (imports : list import) base :=
            List.fold_left 
              (fun m p => 
                 let '(modl, f, pre) := p in
                 LabelMap.LabelMap.add (modl, Global f) pre m) imports base.

          Lemma find_importsMap_find_as_map' : 
            forall imps2 imps1 base, 
              NoDupKey (imps1 ++ imps2) -> 
              (forall (k : label), LabelMap.LabelMap.find (k : Labels.label) base = find_as_map k imps1) ->
              forall (k : label), LabelMap.LabelMap.find (k : Labels.label) (importsMap' imps2 base) = find_as_map k (imps1 ++ imps2).
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
            (*here*)
      Qed.

      Lemma incl_stubs_bimports : incl (map (@func_to_import _) stubs) bimports.
        admit.
      Qed.

      Lemma map_3 : forall A B (f : A -> B) k m, LabelMap.In k m -> LabelMap.In k (LabelMap.map f m).
      Proof.
        intros.
        unfold LabelMap.In in *.
        unfold LabelMap.Raw.PX.In in *.
        openhyp.
        eapply LabelMap.map_1 in H.
        eexists.
        eauto.
      Qed.

      Require Import Sumbool.
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
        eauto.
        intuition.
        rewrite e0 in H0; intuition.
        rewrite e0 in e; intuition.
        rewrite e in H.
        destruct (is_import stn p); intuition.
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

      Lemma find_map : forall A B (f : A -> B) k v m, LabelMap.find k m = Some v -> LabelMap.find k (LabelMap.map f m) = Some (f v).
        intros.
        eapply LabelMap.find_2 in H.
        eapply LabelMap.find_1.
        eapply LabelMap.map_1; eauto.
      Qed.

      Lemma imports_bimports : forall k v, LabelMap.find k imports = Some v -> find_as_map k bimports = Some (foreign_spec v).
        unfold bimports, bimports_base.
        intros.
        eapply NoDup_app_find_as_map.
        eapply NoDup_bimports.
        eapply NoDup_app_find_as_map.
        eapply NoDup_incl.
        eapply NoDup_bimports.
        unfold bimports, bimports_base.
        intuition.
        rewrite find_as_map_elements.
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
        eapply In_In_keys.
        eapply map_3; eauto.
      Qed.

      Lemma exports_bimports : forall k v, LabelMap.find k exports = Some v -> find_as_map k bimports = Some (spec_without_funcs_ok v fs).
        unfold bimports, bimports_base.
        intros.
        eapply NoDup_app_find_as_map.
        eapply NoDup_bimports.
        eapply NoDup_app_find_as_map_2.
        eapply NoDup_incl.
        eapply NoDup_bimports.
        unfold bimports, bimports_base.
        intuition.
        rewrite find_as_map_elements.
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
        eapply In_In_keys.
        eapply map_3; eauto.
      Qed.

      Lemma fullImports_eq_bimports : forall (k : label), LabelMap.LabelMap.find (k : Labels.label) (fullImports bimports stubs) = find_as_map k bimports.
        intros.
        eapply fullImports_no_effect.
        eapply NoDup_bimports.
        eapply incl_stubs_bimports.
      Qed.

      Corollary bimports_fullImports : forall (x : label), In x (map fst bimports) -> LabelMap.LabelMap.find (x : Labels.label) (fullImports bimports stubs) <> None.
      Proof.
        intros.
        eapply In_find_as_map_not_None in H.
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

        eapply In_In_keys in H.
        eapply in_imports_in_bimports in H.
        eapply bimports_fullImports; eauto.

        eapply In_In_keys in H.
        eapply in_exports_in_bimports in H.
        eapply bimports_fullImports; eauto.
      Qed.

      Lemma exports_accessible_labels : forall l, LabelMap.find l exports <> None -> In l accessible_labels.
        unfold accessible_labels.
        intros.
        eapply in_or_app.
        right.
        eapply In_In_keys.
        eapply In_find_not_None; eauto.
      Qed.
      
      Lemma exports_fullImports : forall (l : label) spec, LabelMap.find l exports = Some spec -> LabelMap.LabelMap.find (l : Labels.label) (fullImports bimports stubs) = Some (spec_without_funcs_ok spec fs).
        intros.
        rewrite fullImports_eq_bimports.
        eapply exports_bimports; eauto.
      Qed.

      Lemma tgt_fullImports : forall f, In f (Functions m) -> LabelMap.LabelMap.find (tgt f : Labels.label) (fullImports bimports stubs) = Some (spec f).
        intros.
        rewrite fullImports_eq_bimports. 
        unfold bimports, bimports_base.
        eapply NoDup_app_find_as_map_2.
        eapply NoDup_bimports.
        unfold tgt.
        unfold mod_name.
        eapply In_find_as_map_Some.
        eapply NoDup_incl.
        eapply NoDup_bimports.
        unfold bimports, bimports_base.
        intuition.
        unfold Func_to_import in *; simpl in *.
        eapply in_map with (f := fun x => Func_to_import x) in H.
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
        eauto.
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
        eapply In_In_keys.
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
        Opaque Inv.foreign_spec.
        post; descend.
        instantiate (1 := foreign_spec x0).
        erewrite specs_foreign; eauto.

        unfold foreign_spec.
        step auto_ext.
        Transparent Inv.foreign_spec.
        step auto_ext.
        rewrite sepFormula_eq; apply Imply_refl.
      Qed.

      Hypothesis in_modules : In m modules.

      Lemma good_vcs : forall ls, (forall x, In x ls -> In x (Functions m)) -> vcs (makeVcs bimports stubs (map make_stub ls)).
        induction ls; simpl; eauto.
        Require Import Wrap.
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
