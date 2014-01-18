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

  Definition exports : list (label * InternalFuncSpec) :=
    flatten 
      (List.map 
         (fun m =>
            List.map 
              (fun (f : GoodFunction) =>
                 ((MName m, FName f), f : InternalFuncSpec)
              ) (Functions m)
         ) modules).

  Definition accessible_labels := map fst (LabelMap.elements imports) ++ map fst exports.

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

    Definition find_by_word A m (p : W) : option A :=
      match find (fun x => is_label_map_to_word (fst x) p) m with
        | Some (_, a) => Some a
        | None => None
      end.

    Definition is_export := find_by_word exports.

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

  Definition bimports_base : list import := 
    List.map 
      (fun (p : label * ForeignFuncSpec) => 
         let lbl := fst p in
         let spec := snd p in
         (lbl, foreign_spec spec)) 
      (LabelMap.elements imports) 
      ++
      List.map 
      (fun (p : label * InternalFuncSpec) =>
         let lbl := fst p in
         let spec := snd p in
         (lbl, spec_without_funcs_ok spec fs))
      exports.
  
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

      Definition bimports : list import := 
        bimports_base
          ++
          List.map 
          (fun (f : GoodFunction) =>
             (impl_label (MName m) (FName f), CompileFuncSpec.spec f))
          (Functions m).
          

      Definition stubs := map make_stub (Functions m).

      Definition make_module := StructuredModule.bmodule_ bimports stubs.

      Definition eqb x y := if Label.Key.eq_dec x y then true else false.

      Definition find_as_map B k (ls : list (label * B)) : option B :=
        SetoidList.findA (eqb k) ls.

      Lemma In_find_as_map : forall B (ls : list (label * B)) k, In k (map fst ls) <-> find_as_map k ls <> None.
        admit.
      Qed.

      Lemma fs_internal : 
        forall stn p spec, 
          fs stn p = Some (Internal spec) -> 
          exists lbl, 
            find_as_map lbl exports = Some spec /\ 
            Labels stn lbl = Some p.
        admit.
      Qed.

      Require Import GeneralTactics.

      Set Printing Coercions.

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

      Lemma imports_bimports : forall k v, LabelMap.find k imports = Some v -> find_as_map k bimports = Some (foreign_spec v).
        admit.
      Qed.

      Corollary in_imports_in_bimports : forall x, In x (map fst (LabelMap.elements imports)) -> In x (map fst bimports).
        unfold bimports, bimports_base.
        intros.
        erewrite map_app.
        eapply in_or_app.
        left.
        erewrite map_app.
        eapply in_or_app.
        left.
        erewrite map_map.
        simpl.
        eauto.
      Qed.

      Lemma exports_bimports : forall k v, find_as_map k exports = Some v -> find_as_map k bimports = Some (spec_without_funcs_ok v fs).
        admit.
      Qed.

      Corollary in_exports_in_bimports : forall x, In x (map fst exports) -> In x (map fst bimports).
        unfold bimports, bimports_base.
        intros.
        erewrite map_app.
        eapply in_or_app.
        left.
        erewrite map_app.
        eapply in_or_app.
        right.
        erewrite map_map.
        simpl.
        eauto.
      Qed.

      Lemma fullImports_eq_bimports : forall (k : label) v, LabelMap.LabelMap.find (k : Labels.label) (fullImports bimports stubs) = Some v <-> find_as_map k bimports = Some v.
        admit.
      Qed.

      Corollary bimports_fullImports : forall (x : label), In x (map fst bimports) -> LabelMap.LabelMap.find (x : Labels.label) (fullImports bimports stubs) <> None.
      Proof.
        intros.
        eapply In_find_as_map in H.
        eapply ex_up in H.
        openhyp.
        eapply fullImports_eq_bimports in H.
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
        eapply in_imports_in_bimports in H.
        eapply bimports_fullImports; eauto.

        eapply in_exports_in_bimports in H.
        eapply bimports_fullImports; eauto.
      Qed.

      Lemma exports_accessible_labels : forall l, find_as_map l exports <> None -> In l accessible_labels.
        admit.
      Qed.
      
      Lemma exports_fullImports : forall l spec, find_as_map l exports = Some spec -> LabelMap.LabelMap.find (l : Labels.label) (fullImports bimports stubs) = Some (spec_without_funcs_ok spec fs).
        intros.
        eapply fullImports_eq_bimports.
        eapply exports_bimports; eauto.
      Qed.

      Lemma tgt_fullImports : forall m, In m modules -> forall f, In f (Functions m) -> LabelMap.LabelMap.find (tgt f : Labels.label) (fullImports bimports stubs) = Some (spec f).
        admit.
      Qed.

      Lemma fs_foreign :
        forall stn p spec, 
          fs stn p = Some (Foreign spec) -> 
          exists lbl : label, 
            LabelMap.find lbl imports = Some spec /\ 
            Labels stn lbl = Some p.
        admit.
      Qed.

      Lemma imports_accessible_labels : forall l, LabelMap.find l imports <> None -> In l accessible_labels.
        admit.
      Qed.
      
      Lemma imports_fullImports : forall (l : label) spec, LabelMap.find l imports = Some spec -> LabelMap.LabelMap.find (l : Labels.label) (fullImports bimports stubs) = Some (foreign_spec spec).
        intros.
        eapply fullImports_eq_bimports.
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
