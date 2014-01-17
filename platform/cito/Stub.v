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

  Section module.

      Variable m : GoodModule.

      Section f.

        Variable f : GoodFunction.

        Section body.
          
          Variable im : LabelMap.LabelMap.t assert.

          Variable im_g : importsGlobal im.

          Definition mod_name := MName m.

          Require Import NameDecoration.
          Definition tgt := ((impl_module_name mod_name)!(FName f))%SP.

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

      Require Import Inv.

      Definition foreign_spec spec : assert := 
        st ~> ExX, Inv.foreign_spec _ spec st.

      Definition bimports : list import := 
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
             (impl_module_name (fst lbl), snd lbl, CompileFuncSpec.spec spec))
          exports.
          

      Definition stubs := map make_stub (Functions m).

      Definition make_module := StructuredModule.bmodule_ bimports stubs.

      Definition find_as_map B k (ls : list (label * B)) : option B :=
        match find (fun p => if Label.Key.eq_dec k (fst p) then true else false) ls with
          | Some (_, v) => Some v
          | None => None
        end.

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

      Lemma imports_bimports : forall x, In x (map fst (LabelMap.elements imports)) -> In x (map fst bimports).
        unfold bimports.
        intros.
        erewrite map_app.
        eapply in_or_app.
        left.
        erewrite map_map.
        simpl.
        eauto.
      Qed.

      Lemma imports_fullImports : forall mn (imps : list import) (x : label), In x (map fst imps) -> forall exps, LabelMap.LabelMap.find (x : Labels.label) (fullImports (modName := mn) imps exps) <> None.
      Proof.
        admit.
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
        eapply imports_bimports in H.
        eapply imports_fullImports; eauto.

        Lemma exports_stubs : forall x, In x (map fst exports) -> In x (map (fun f => fst (fst f)) stubs).
        admit.
      Qed.

      Lemma exports_accessible_labels : forall l, find_as_map l exports <> None -> In l accessible_labels.
        admit.
      Qed.
      
      Lemma exports_fullImports : forall l spec, find_as_map l exports = Some spec -> LabelMap.find (l : Labels.label) (fullImports bimports stubs) = Some (spec_without_funcs_ok spec fs).
        admit.
      Qed.

      Lemma tgt_fullImports : forall m, In m modules -> forall f, In f (Functions m) -> LabelMap.find (tgt f) (fullImports bimports stubs) = Some (spec f).
        admit.
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
        admit.

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
