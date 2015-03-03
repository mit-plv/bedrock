Set Implicit Arguments.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Bedrock.Platform.Cito.ChangeSpec.
  Require Import Bedrock.Platform.Cito.SemanticsFacts4.
  Require Import Bedrock.Platform.Cito.ProgramLogic2.
  Require Import Bedrock.Platform.Cito.Transit.
  Require Import Bedrock.Platform.Cito.Semantics.
  Require Import Bedrock.Platform.Cito.LinkSpecFacts.
  Require Import Bedrock.Platform.Cito.LinkSpec.

  Require Import Bedrock.Platform.Cito.GLabelMap.
  Require Import Bedrock.Platform.Cito.StringMap.
  Require Import Bedrock.Platform.Cito.CModule.

  Variable m : CModule.

  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).

  Variable imports : GLabelMap.t AxiomaticSpec.

  Variable exports : StringMap.t AxiomaticSpec.

  Require Import Bedrock.Platform.Cito.StringMapFacts.
  Hypothesis exports_in_domain : is_sub_domain exports (Funs m) = true.

  (* the name of the module that contains operational export specs *)
  Variable op_mod_name : string.

  Hypothesis op_mod_name_ok : is_good_module_name op_mod_name = true.

  Require Import Bedrock.Platform.Cito.ListFacts3.

  Hypothesis import_module_names_ok : 
    let imported_module_names := List.map (fun x => fst (fst x)) (GLabelMap.elements imports) in
    List.forallb (fun x => negb (string_bool op_mod_name x)) imported_module_names = true.

  Require Import Bedrock.Platform.Cito.CModuleFacts.
  Definition cmod := cmodule_to_gmodule op_mod_name op_mod_name_ok m.

  Definition modules := cmod :: nil.

  Definition aug_mod_name (m_name s : string) := (m_name, s).

  Arguments GLabelMap.empty {elt}.

  Definition map_aug_mod_name elt m_name (m : StringMap.t elt) := GLabelMapFacts.of_list (List.map (fun p => (aug_mod_name m_name (fst p), (snd p))) (StringMap.elements m)).

  Require Import Bedrock.Platform.Cito.GLabelMap Bedrock.Platform.Cito.GLabelMapFacts.
  Import GLabelMap.GLabelMap GLabelMapFacts.FMapNotations.
  Open Scope fmap_scope.

  Coercion cfun_to_copspec (f : CFun) : GoodFunction := cfun_to_gfun "" f.

  Notation Foreign := (@Foreign ADTValue).
  Notation Internal := (@Internal ADTValue).

  Definition specs_op := map Foreign imports + map (fun (f : CFun) => Internal f) (map_aug_mod_name op_mod_name (Funs m)).
  Definition exports_with_glabel := map_aug_mod_name op_mod_name exports.
  Definition specs := apply_specs_diff specs_op exports_with_glabel.

  Definition exports_weakens_impl := forall env_ax, specs_env_agree specs env_ax -> strengthen_diff specs_op exports_with_glabel env_ax.

  Hypothesis Hewi : exports_weakens_impl.

  Import StringMap.StringMap.
  Require Import Bedrock.Platform.Cito.StringMapFacts.

  Lemma exports_sub_domain : sub_domain exports (Funs m).
  Proof.
    eapply is_sub_domain_sound; eauto.
  Qed.

  Import GLabelMap.GLabelMap.
  Require Import Bedrock.Platform.Cito.GLabelMapFacts.

  Require Import Bedrock.Platform.Cito.GeneralTactics.
  Require Import Bedrock.Platform.Cito.GeneralTactics4.

  Require Import Bedrock.Platform.Cito.ListFacts1.

  Lemma aug_mod_name_Injection mod_name : IsInjection (aug_mod_name mod_name).
  Proof.
    eapply Injective_IsInjection.
    intros s1 s2.
    intros H.
    inject H.
    eauto.
  Qed.

  Lemma NoDupKey_aug_mod_name A B mod_name (f : string * A -> string * string * B) d : (forall p, fst (f p) = aug_mod_name mod_name (fst p)) -> NoDupKey (List.map f (StringMap.elements d)).
  Proof.
    intros H.
    eapply NoDupKey_NoDup_fst.
    rewrite map_map; simpl.
    setoid_rewrite H.
    rewrite <- map_map.
    eapply Injection_NoDup.
    {
      eapply aug_mod_name_Injection.
    }
    eapply StringMapFacts.NoDup_elements.
  Qed.

  Lemma map_aug_mod_name_intro elt k mod_name k' d (v : elt) : k = (mod_name, k') -> StringMap.find k' d = Some v -> GLabelMap.find k (map_aug_mod_name mod_name d) = Some v.
  Proof.
    intros ? H.
    subst.
    unfold map_aug_mod_name.
    eapply find_mapsto_iff.
    eapply MapsTo_to_map.
    {
      eapply NoDupKey_aug_mod_name.
      intros; simpl; eauto.
    }
    eapply in_map_iff.
    unfold aug_mod_name.
    exists (k', v); split; eauto.
    eapply StringMapFacts.find_in_elements; eauto.
  Qed.

  Require Import Bedrock.Platform.Cito.GeneralTactics5.

  Lemma map_aug_mod_name_elim elt k mod_name d (v : elt) : find k (map_aug_mod_name mod_name d) = Some v -> exists k', k = (mod_name, k') /\ StringMap.find k' d = Some v.
  Proof.
    intros H.
    unfold map_aug_mod_name in *.
    eapply find_mapsto_iff in H.
    eapply MapsTo_to_map_elim in H.
    {
      eapply in_map_iff in H.
      unfold aug_mod_name in *.
      destruct H as  [ [k' v'] [Heq H] ].
      inject Heq.
      eapply StringMapFacts.in_elements_find in H.
      repeat eexists_split; eauto.
    }
    eapply NoDupKey_aug_mod_name.
    intros; simpl; eauto.
  Qed.

  Lemma map_aug_mod_name_sub_domain A B nm a b : @StringMapFacts.sub_domain A B a b -> sub_domain (map_aug_mod_name nm a) (map_aug_mod_name nm b).
  Proof.
    unfold sub_domain in *.
    intros Hsd lbl.
    intros H.
    eapply in_find_Some in H.
    destruct H as [v H].
    eapply map_aug_mod_name_elim in H.
    destruct H as [fname [? H] ].
    subst.
    Import StringMap.StringMap.
    Require Import Bedrock.Platform.Cito.StringMapFacts.
    eapply find_Some_in in H.
    eapply Hsd in H.
    eapply in_find_Some in H.
    destruct H as [v' H].
    Import GLabelMap.GLabelMap.
    Require Import Bedrock.Platform.Cito.GLabelMapFacts.
    eapply find_Some_in.
    eapply map_aug_mod_name_intro; eauto.
  Qed.

  Lemma specs_equal_domain : equal_domain specs specs_op.
  Proof.
    unfold specs.
    eapply sub_domain_apply_specs_diff_equal_domain.
    unfold specs_op, exports_with_glabel.
    eapply sub_domain_update_2.
    eapply sub_domain_map_2.
    eapply map_aug_mod_name_sub_domain.
    eapply exports_sub_domain; eauto.
  Qed.

  Lemma specs_op_intro fname op_spec : StringMap.find fname (Funs m) = Some op_spec -> find (op_mod_name, fname) specs_op = Some (Internal op_spec).
  Proof.
    intros H.
    unfold specs_op in *.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff.
    left.
    eapply map_mapsto_iff.
    eexists; split; eauto.
    eapply find_mapsto_iff.
    eapply map_aug_mod_name_intro; eauto.
  Qed.

  Import StringMap.StringMap.
  Require Import Bedrock.Platform.Cito.StringMapFacts.

  Require Import Bedrock.Platform.Cito.ListFacts4.

  Lemma find_Funs_label_mapsto fname op_spec : 
    find fname (Funs m) = Some (op_spec) ->
    exists (ispec : InternalFuncSpec) (m0 : GoodModule) (f : GoodFunction),
      Internal op_spec = Internal ispec /\
      List.In m0 (cmodule_to_gmodule op_mod_name op_mod_name_ok m :: nil) /\
      List.In f (Functions m0) /\
      ispec = f /\ (op_mod_name, fname) = (GoodModule.Name m0, Name f).
  Proof.
    intros H.
    exists op_spec.
    eexists.
    exists (cfun_to_gfun fname op_spec).
    repeat try_split; try reflexivity.
    {
      eapply in_singleton_iff; eauto.
    }
    {
      simpl.
      unfold cfuns_to_gfuns in *.
      eapply in_map_iff.
      exists (fname, op_spec).
      unfold uncurry in *; simpl in *.
      split; trivial.
      eapply find_in_elements; eauto.
    }
    {
      simpl; eauto.
    }
  Qed.

  Lemma label_mapsto_find_Funs (m' : GoodModule) (f : GoodFunction) :
    List.In m' (cmodule_to_gmodule op_mod_name op_mod_name_ok m :: nil) ->
    List.In f (Functions m') ->
    exists (f' : CFun) ,
      Internal f = Internal f' /\
      GoodModule.Name m' = op_mod_name /\
      find (Name f) (Funs m) = Some f'.
  Proof.
    intros Hinm Hinf.
    eapply in_singleton_iff in Hinm.
    subst.
    simpl in *.
    unfold cfuns_to_gfuns in *.
    eapply in_map_iff in Hinf.
    destruct Hinf as [ [fname f'] [Heq Hin] ].
    unfold uncurry in *; simpl in *.
    subst.
    eapply in_elements_find in Hin.
    exists f'; repeat try_split; eauto.
  Qed.

  Import GLabelMap.GLabelMap.
  Require Import Bedrock.Platform.Cito.GLabelMapFacts.

  Require Import Bedrock.Platform.Cito.Option.
  Require Import Coq.Bool.Bool.
  
  Lemma find_op_mod_name_imports_none fname : find (op_mod_name, fname) imports = None.
  Proof.
    simpl in *.
    destruct (option_dec (find (op_mod_name, fname) imports)) as [ [v Heq] | Heq]; trivial.
    pose (Himn := import_module_names_ok).
    eapply forallb_forall with (x := op_mod_name) in Himn.
    {
      eapply negb_true_iff in Himn.
      unfold string_bool in *. 
      unfold sumbool_to_bool in *.
      destruct (string_dec op_mod_name op_mod_name); intuition.
    }        
    eapply in_map_iff.
    exists (op_mod_name, fname, v); simpl; split; trivial.
    eapply find_in_elements; eauto.
  Qed.

  Lemma specs_op_equal : specs_equal specs_op modules imports.
  Proof.
    unfold specs_equal.
    unfold label_mapsto.
    unfold specs_op.
    intros lbl spec.
    split.
    {
      intros H.
      eapply find_mapsto_iff in H.
      eapply update_mapsto_iff in H.
      destruct H as [H | H].
      {
        left.
        eapply map_mapsto_iff in H.
        destruct H as [op_spec [? H] ].
        subst.
        eapply find_mapsto_iff in H.
        eapply map_aug_mod_name_elim in H.
        destruct H as [fname [? H] ].
        subst.
        unfold modules.
        unfold cmod.
        eapply find_Funs_label_mapsto; eauto.
      }
      {
        right.
        destruct H as [H Hnin].
        eapply map_mapsto_iff in H.
        destruct H as [ax_spec [? H] ].
        subst.
        eexists; split; eauto.
        eapply find_mapsto_iff; eauto.
      }
    }
    {
      intros [H | H].
      {
        eapply find_mapsto_iff.
        eapply update_mapsto_iff.
        left.
        eapply map_mapsto_iff.
        destruct spec as [ax_spec | op_spec].
        { openhyp; discriminate. }
        destruct H as [ispec [m' [f H ] ] ].
        destruct H as [Heq [Hinm [Hinf [? ?] ] ] ].
        subst.
        inject Heq.
        unfold modules, cmod in Hinm.
        eapply label_mapsto_find_Funs in Hinm; eauto.
        openhyp.
        eexists; split; eauto.
        eapply find_mapsto_iff.
        eapply map_aug_mod_name_intro.
        - subst; eauto.
        - eauto.
      }
      {
        destruct H as [ax_spec [? H] ].
        subst.
        eapply find_mapsto_iff.
        eapply update_mapsto_iff.
        right.
        split.
        {
          eapply map_mapsto_iff.
          eexists; split; eauto.
          eapply find_mapsto_iff; eauto.
        }
        {
          intro H2.
          eapply map_2 in H2.
          eapply in_find_Some in H2.
          destruct H2 as [op_spec H2].
          eapply map_aug_mod_name_elim in H2.
          destruct H2 as [fname [? H2] ].
          subst.
          rewrite find_op_mod_name_imports_none in *; discriminate.
        }
      }
    }
  Qed.

  Lemma new_env_strengthen : forall stn fs, env_good_to_use modules imports stn fs -> strengthen (from_bedrock_label_map (Labels stn), fs stn) (change_env specs (from_bedrock_label_map (Labels stn), fs stn)).
    intros.
    eapply strengthen_diff_strenghthen.
    - eapply Hewi; eauto.
      eapply change_env_agree; eauto.
      + eapply specs_equal_domain; eauto.
      + eapply specs_equal_agree; eauto.
        eapply specs_op_equal; eauto.
    - eapply specs_equal_agree; eauto; eapply specs_op_equal; eauto.
    - eapply change_env_agree; eauto.
      + eapply specs_equal_domain; eauto.
      + eapply specs_equal_agree; eauto.
        eapply specs_op_equal; eauto.
    - intros; simpl; eauto.
  Qed.

  Import StringMap.StringMap.
  Require Import Bedrock.Platform.Cito.StringMapFacts.

  Definition content := inter (Funs m) exports.

  Notation gl2w := from_bedrock_label_map.

  Require Import Bedrock.Platform.Cito.GLabelMap Bedrock.Platform.Cito.GLabelMapFacts.
  Import GLabelMap.GLabelMap GLabelMapFacts.FMapNotations.

  Lemma strengthen_elim_single stn fs fname op_spec ax_spec : 
    List.In (fname, (op_spec, ax_spec)) (StringMap.elements content) -> 
    env_good_to_use modules imports stn fs -> 
    strengthen_op_ax op_spec ax_spec ((change_env specs (gl2w (Labels stn), fs stn))).
  Proof.
    intros Hin Hegu.
    unfold exports_weakens_impl in *.
    eapply StringMapFacts.in_elements_find in Hin.
    eapply StringMapFacts.find_inter_elim in Hin.
    destruct Hin as [Hin1 Hin2].
    eapply strengthen_diff_elim in Hewi; try (eapply map_aug_mod_name_intro; eauto).
    Focus 2.
    {
      eapply change_env_agree; eauto.
      - eapply specs_equal_domain; eauto.
      - eapply specs_equal_agree; eauto.
        eapply specs_op_equal; eauto.
    }
    Unfocus.
    destruct Hewi as [Hewi' | Hewi']; clear Hewi.
    {
      erewrite specs_op_intro in Hewi' by eauto.
      discriminate.
    }
    {
      destruct Hewi' as [op_spec' [Hin1' Hstr] ].
      erewrite specs_op_intro in Hin1' by eauto.
      inject Hin1'.
      eauto.
    }
  Qed.

End ADTValue.

Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Bedrock.Platform.Cito.LinkSpec.
  Module Import LinkSpecMake := Make E.
  Module Import LinkSpecMake2 := Make M.
  Require Bedrock.Platform.Cito.LayoutHints4.
  Module LayoutHints4Make := LayoutHints4.Make E M.
  Require Import Bedrock.Platform.Cito.InvFacts.
  Module Import InvFactsMake := Make E.
  Module Import InvFactsMake2 := InvFactsMake.Make M.
  Require Import Bedrock.Platform.Cito.LayoutHints3.
  Module Import LayoutHints3Make := Make E M.
  Require Bedrock.Platform.Cito.LayoutHints2.
  Module LayoutHints2Make := LayoutHints2.Make E M.

  Section M.

    Variable m : CModule.
    
    Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).

    Variable imports : GLabelMap.t AxiomaticSpec.

    Variable exports : StringMap.t AxiomaticSpec.

    Require Import Bedrock.Platform.Cito.StringMapFacts.
    Hypothesis exports_in_domain : is_sub_domain exports (Funs m) = true.

    (* the name of the module that contains axiomatic export specs *)
    Variable ax_mod_name : string.

    Variable op_mod_name : string.

    Hypothesis op_mod_name_ok : is_good_module_name op_mod_name = true.

    Require Import Bedrock.Platform.Cito.ListFacts3.

    Hypothesis import_module_names_ok : 
      let imported_module_names := List.map (fun x => fst (fst x)) (GLabelMap.elements imports) in
      List.forallb (fun x => negb (string_bool op_mod_name x)) imported_module_names = true.

    Hypothesis name_neq : negb (string_bool ax_mod_name op_mod_name) = true.

    Notation exports_weakens_impl := (exports_weakens_impl m imports exports op_mod_name).

    Hypothesis Hewi : exports_weakens_impl.

    Require Import Bedrock.Platform.Cito.CModuleFacts.
    Definition cmod := cmodule_to_gmodule op_mod_name op_mod_name_ok m.

    Definition modules := cmod :: nil.

    Require Import Bedrock.Platform.Cito.StringMapFacts.

    Definition accessible_labels := 
      List.map (fun fname => (op_mod_name, fname)) (StringMapFacts.keys exports).

    Section Fun.

      Variable fname : string.

      Variable spec : AxiomaticSpec.

      Variable f : CFun.

      Section body.
        
        Require Import Bedrock.XCAP.

        Variable im : LabelMap.t assert.

        Variable im_g : importsGlobal im.

        Definition tgt_label : glabel := aug_mod_name op_mod_name fname.

        Definition tgt_spec := func_spec modules imports tgt_label f.

        Definition body := 
          @Seq_ _ im_g ax_mod_name
                (AssertStar_ im ax_mod_name accessible_labels tgt_spec)
                (Goto_ im_g ax_mod_name tgt_label).

      End body.

      Definition stub_spec := foreign_func_spec (ax_mod_name, fname) spec.

      Definition make_stub : StructuredModule.function ax_mod_name :=
        (fname, stub_spec, body).

    End Fun.

    Import StringMap.

    Definition tgt_spec_as_import {unused} (x : string * (CFun * unused)) : import := 
      let fname := fst x in
      let f := fst (snd x) in
      (tgt_label fname, tgt_spec fname f).

    Notation content := (content m exports).

    Definition bimports : list import := List.map tgt_spec_as_import (elements content).

    Definition make_stub' x := 
      let name := fst x in
      let op := fst (snd x) in
      let ax := snd (snd x) in
      make_stub name ax op.

    Definition stubs := List.map make_stub' (elements content).

    Definition make_module := StructuredModule.bmodule_ bimports stubs.

    Require Import Bedrock.Platform.Cito.NameVC.

    Require Import Bedrock.Platform.Cito.StructuredModuleFacts.
    Require Import Bedrock.Platform.Cito.GLabelMapFacts.

    Require Import Bedrock.Platform.Cito.ListFacts1.

    Lemma NoDupKey_bimports : NoDupKey bimports.
    Proof.
      unfold bimports, tgt_spec_as_import, tgt_label.
      eapply NoDupKey_aug_mod_name.
      intros; simpl; eauto.
    Qed.

    Lemma NoDupKey_stubs : NoDupKey (List.map (@func_to_import ax_mod_name) stubs).
    Proof.
      unfold func_to_import, stubs, make_stub', make_stub.
      repeat rewrite map_map; simpl.
      eapply NoDupKey_aug_mod_name.
      intros; simpl; eauto.
    Qed.

    Lemma no_dup_func_names : NoDupFuncNames stubs.
      eapply NoDup_NoDupFuncNames.
      unfold stubs, make_stub', make_stub; simpl.
      repeat rewrite map_map; simpl.
      eapply StringMapFacts.NoDup_elements.
    Qed.

    Lemma ax_neq_op_mod_name : ax_mod_name <> op_mod_name.
    Proof.
      Require Import Coq.Bool.Bool.
      eapply negb_true_iff in name_neq.
      unfold string_bool in *. 
      unfold sumbool_to_bool in *.
      destruct (string_dec ax_mod_name op_mod_name); intuition.
    Qed.

    Require Import Bedrock.Platform.Cito.GeneralTactics.

    Lemma DisjointKey_bimports_stubs : DisjointKey bimports (List.map (@func_to_import ax_mod_name) stubs).
    Proof.
      intros k.
      intros [Hin1 Hin2].
      unfold InKey in *.
      unfold bimports in *.
      unfold tgt_spec_as_import in *.
      unfold func_to_import in *.
      unfold tgt_label in *.
      unfold aug_mod_name in *.
      simpl in *.
      rewrite map_map in *.
      simpl in *.
      eapply in_map_iff in Hin1.
      openhyp.
      subst.
      eapply in_map_iff in Hin2.
      openhyp.
      injection H.
      intros.
      eapply ax_neq_op_mod_name; eauto.
    Qed.

    Lemma ax_mod_name_not_in_imports : NameNotInImports ax_mod_name bimports.
    Proof.
      eapply NotIn_NameNotInImports.
      intros Hin.
      unfold bimports in *.
      unfold tgt_spec_as_import in *.
      unfold tgt_label in *.
      unfold aug_mod_name in *.
      unfold fst_2 in *.
      simpl in *.
      rewrite map_map in *.
      simpl in *.
      eapply in_map_iff in Hin.
      openhyp.
      eapply ax_neq_op_mod_name; eauto.
    Qed.

    Lemma NoDupKey_bimports_stubs : NoDupKey (bimports ++ List.map (@func_to_import ax_mod_name) stubs).
    Proof.
      eapply NoDupKey_app.
      eapply NoDupKey_bimports.
      eapply NoDupKey_stubs.
      eapply DisjointKey_bimports_stubs.
    Qed.

    Lemma find_fullImports fun_name op_spec ax_spec : List.In (fun_name, (op_spec, ax_spec)) (StringMap.elements content) -> LabelMap.find (tgt_label fun_name : label) (fullImports bimports stubs) = Some (tgt_spec fun_name op_spec).
    Proof.
      intros Hin.
      rewrite fullImports_spec.
      {
        eapply In_find_list_Some.
        {
          eapply NoDupKey_bimports_stubs.
        }
        eapply InA_eqke_In.
        eapply in_app_iff.
        left.
        unfold bimports.
        eapply in_map_iff.
        eexists.
        split; eauto.
        eauto.
      }
      {
        eapply NoDupKey_bimports_stubs.
      }
    Qed.

    Require Import Bedrock.Platform.Wrap.
    Require Import Bedrock.Platform.Cito.Inv.

    Import SemanticsMake.
    Require Import Bedrock.Platform.Cito.SemanticsUtil.
    Require Import Bedrock.Platform.Cito.SemanticsFacts9.

    Arguments store_pair {_} _ _.
    
    Require Import Coq.Setoids.Setoid.

    Require Import Bedrock.Platform.Cito.WordMap Bedrock.Platform.Cito.WordMapFacts.
    Import WordMap.WordMap WordMapFacts.FMapNotations.

    Ltac remove_sel :=
      match goal with
        | H : context [sel ?VS] |- _ => change (sel VS) with VS in H
        | |- context [sel ?VS] => change (sel VS) with VS
      end.

    Require Import Bedrock.Platform.Cito.ListFacts4.

    Arguments SCA {ADTValue} _.
    Arguments ADT {ADTValue} _.

    Require Import Bedrock.Platform.Cito.WordMap.
    Import WordMap.

    Require Import Bedrock.Platform.Cito.GeneralTactics3.
    Require Import Bedrock.Platform.Cito.GeneralTactics4.

    Require Import Bedrock.Platform.Cito.WordMap Bedrock.Platform.Cito.WordMapFacts.
    Import WordMap.WordMap WordMapFacts.FMapNotations.
    Local Open Scope fmap_scope.

    Require Import Bedrock.Platform.Cito.ListFacts5.
    Require Import Bedrock.Platform.Cito.GeneralTactics5.

    Lemma TransitSafe_intro fun_name op_spec ax_spec pairs : 
      let words := List.map fst pairs in
      let inputs := List.map snd pairs in
      List.In (fun_name, (op_spec, ax_spec)) (StringMap.elements content) ->
      PreCond ax_spec inputs ->
      disjoint_ptrs pairs ->
      good_scalars pairs ->
      TransitSafe ax_spec words inputs (make_heap pairs).
    Proof.
      simpl.
      intros Hin Hpre Hdisj Hgs.
      unfold TransitSafe.
      repeat try_split; eauto.
      {
        repeat rewrite map_length in *; eauto.
      }
      rewrite combine_fst_snd.
      eapply disjoint_ptrs_good_scalars_good_inputs; eauto.
    Qed.

    Notation gl2w := from_bedrock_label_map.
    Notation specs := (specs m imports exports op_mod_name).

    Lemma safe_intro fun_name op_spec ax_spec stn fs vs_callee pairs : 
      List.In (fun_name, (op_spec, ax_spec)) (StringMap.elements content) ->
      env_good_to_use modules imports stn fs ->
      List.map (sel vs_callee) (ArgVars op_spec) = List.map fst pairs ->
      PreCond ax_spec (List.map snd pairs) ->
      disjoint_ptrs pairs ->
      good_scalars pairs ->
      Safe (gl2w (Labels stn), fs stn) (Body op_spec) (vs_callee, make_heap pairs).
    Proof.
      intros Hin Hegu Hfst Hpre Hdisj Hgs.
      eapply strengthen_safe with (env_ax := change_env specs (from_bedrock_label_map (Labels stn), fs stn)).
      { 
        eapply strengthen_elim_single in Hegu; eauto.
        eapply Hegu.
        simpl in *.
        rewrite Hfst.
        eapply TransitSafe_intro; eauto.
      }
      {
        eapply new_env_strengthen; eauto.
      }
    Qed.

    Lemma runsto_TransitTo fun_name (op_spec : CFun) ax_spec stn fs vs_callee vs_callee' h' pairs : 
      let words := List.map fst pairs in
      let inputs := List.map snd pairs in
      let outputs := List.map (fun k => find k h') words in
      let ret_w := sel vs_callee' (RetVar op_spec) in
      let ret_a := find ret_w h' in
      RunsTo (gl2w (Labels stn), fs stn) (Body op_spec) (vs_callee, make_heap pairs) (vs_callee', h') ->
      List.In (fun_name, (op_spec, ax_spec)) (StringMap.elements content) ->
      env_good_to_use modules imports stn fs ->
      List.map (sel vs_callee) (ArgVars op_spec) = words ->
      PreCond ax_spec inputs ->
      disjoint_ptrs pairs ->
      good_scalars pairs ->
      TransitTo ax_spec words inputs outputs ret_w ret_a (make_heap pairs) h'.
    Proof.
      simpl.
      intros Hrt Hin Hegu Hfst Hpre Hdisj Hgs.
      copy_as Hegu Hstr; eapply strengthen_elim_single in Hstr; eauto.
      eapply strengthen_runsto with (env_ax := change_env specs (from_bedrock_label_map (Labels stn), fs stn)) in Hrt.
      {
        set (words := List.map fst pairs) in *.
        set (inputs := List.map snd pairs) in *.
        eapply Hstr with (inputs := inputs) in Hrt; simpl in *.
        {
          rewrite Hfst in *.
          eauto.
        }
        {
          rewrite Hfst in *.
          eapply TransitSafe_intro; eauto.
        }
      }
      {
        eapply new_env_strengthen; eauto.
      }                
      {
        eapply Hstr.
        simpl in *.
        rewrite Hfst in *.
        eapply TransitSafe_intro; eauto.
      }                
    Qed.

    Definition retv p (h : Heap) : Ret := combine_ret p (find p h).

    Lemma runsto_elim fun_name (op_spec : CFun) ax_spec stn fs vs_callee vs_callee' h' pairs : 
      let words := List.map fst pairs in
      let inputs := List.map snd pairs in
      let outputs := List.map (fun k => find k h') words in
      let ret_w := sel vs_callee' (RetVar op_spec) in
      RunsTo (gl2w (Labels stn), fs stn) (Body op_spec) (vs_callee, make_heap pairs) (vs_callee', h') ->
      List.In (fun_name, (op_spec, ax_spec)) (StringMap.elements content) ->
      env_good_to_use modules imports stn fs ->
      List.map (sel vs_callee) (ArgVars op_spec) = words ->
      PreCond ax_spec inputs ->
      disjoint_ptrs pairs ->
      good_scalars pairs ->
      PostCond ax_spec (List.map (fun x1 => (ADTIn x1, ADTOut x1)) (make_triples pairs outputs)) (retv ret_w h').
    Proof.
      simpl; intros Hrt; intros.
      eapply runsto_TransitTo in Hrt; eauto.
      unfold TransitTo in *; openhyp.
      Require Import Bedrock.Platform.Cito.SemanticsFacts7.
      rewrite make_triples_ADTIn_ADTOut by (unfold_all; repeat rewrite map_length; eauto).
      eauto.
    Qed.

    Require Import Bedrock.Platform.Cito.WordMapFacts.
    Arguments empty {elt}.

    Opaque mult.

    Require Import Bedrock.Platform.Cito.StringMap.
    Import StringMap.

    Lemma good_vcs ls : List.incl ls (elements content) -> vcs (makeVcs bimports stubs (List.map make_stub' ls)).
    Proof.
      induction ls; simpl; eauto.
      Require Import Bedrock.Platform.Cito.ListFacts4.
      intros Hincl.
      eapply cons_incl_elim in Hincl.
      destruct Hincl as [Hin Hincl].
      destruct a as [fun_name [op_spec ax_spec] ].
      wrap0.
      Focus 2.
      {
        erewrite find_fullImports by eauto.
        eauto.
      }
      Unfocus.
      rename H into Hvcs.
      subst.
      {
        unfold name_marker.
        step auto_ext.
        unfold spec_without_funcs_ok.
        post.
        subst.

        Import List.

        Ltac hide_all_eq :=
          repeat match goal with
                   | H : _ = _ |- _ => generalize dependent H
                 end.

        Ltac clear_all_eq :=
          repeat match goal with
                   | H : _ = _ |- _ => clear H
                 end.

        rename H8 into Hlong.
        rename x1 into rp.
        rename x2 into e_stack.
        rename x0 into pairs.
        rename a into stn.
        rename b into bst.
        rename H3 into Hst.
        rename H2 into Hegu.
        rename H7 into Hpre.
        rename H0 into Hgs.
        rename H4 into Hdisj.
        Import CompileFuncSpecMake.InvMake2.
        unfold is_state, has_extra_stack in Hst.
        simpl in *.

        set (arr := map fst pairs) in *.
        set (avars := ArgVars op_spec) in *.
        Require Import Bedrock.Platform.Cito.SepHints3.
        rewrite (@replace_array_to_locals arr _ avars) in Hst.
        assert (Halok : array_to_locals_ok arr avars).
        {
          unfold array_to_locals_ok.
          unfold_all.
          split.
          {
            eapply strengthen_elim_single in Hegu; eauto.
            eapply Hegu in Hpre.
            repeat rewrite map_length in *.
            eauto.
          }
          {
            eapply NoDup_ArgVars.
          }
        }
        Ltac gd t := generalize dependent t.
        
        gd Hvcs; gd Hegu; gd Hpre; gd Hewi.
        clear Hewi.
        (* cause of universe inconsistency *)
        rename H1 into Haugment.
        clear Haugment.
        clear import_module_names_ok.
        Import InvMake.SemanticsMake.
        Require Import Bedrock.Platform.Cito.CompileStmtTactics.
        Ltac hiding tac :=
          clear_imports;
          ((let P := fresh "P" in
            match goal with
              | H : Safe ?fs _ _ |- _ => set (P := Safe fs) in *
              | H : RunsTo ?fs _ _ _ |- _ => set (P := RunsTo fs) in *
              | H : fs_good_to_use ?a ?b ?c ?d |- _ => set (P := fs_good_to_use a b c d) in *
            end;
            hiding tac;
            subst P) || tac).

        hiding ltac:(evaluate hints_array_to_locals).
        unfold toArray in *; simpl in *.
        intros.
        rename H12 into Havars.
        rename x0 into vs_callee.
        rename H2 into Hst.

        eexists.
        Import CompileFuncSpecMake.InvMake.
        set (h := make_heap pairs) in *.
        exists (vs_callee, h).
        exists rp, e_stack.
        descend.
        {
          unfold is_state.
          unfold has_extra_stack.
          simpl.
          Require Import Coq.Arith.Arith.
          Require Import Bedrock.Platform.Cito.WordFacts.
          rewrite mult_0_r in *.
          rewrite wplus_0 in *.
          rewrite plus_0_r in *.
          Ltac simpl_array_nil := let h0 := fresh in set (h0 := array nil _) in *; unfold array in h0; simpl in h0; subst h0.
          Ltac simpl_locals_nil := let h0 := fresh in set (h0 := locals nil _ _ _) in *; unfold locals in h0; unfold array in h0; simpl in h0; subst h0.
          simpl_array_nil.
          simpl_locals_nil.
          assert (Hleq : length arr = length avars).
          {
            unfold_all.
            unfold toArray in *; simpl in *.
            repeat rewrite map_length in *.
            eapply map_eq_length_eq; eauto.
          }
          rewrite  Hleq in *.

          clear Hvcs Hegu Hpre Hewi.
          repeat hiding ltac:(step auto_ext).
        }
        {
          eapply safe_intro; eauto.
        }
        {
          eauto.
        }
        {
          (* post call *)
          set (rv := Regs x0 Rv) in *.
          Import SemanticsMake.

          hiding ltac:(step auto_ext).
          hiding ltac:(step auto_ext).
          {
            instantiate (2 := rv).
            instantiate (2 := retv rv (snd x1)).
            instantiate (2 := List.map (heap_sel (snd x1)) arr).
            instantiate (4 := x2).
            instantiate (3 := x4).
            instantiate (1 := List.map (fst x1) avars).
            instantiate (1 := empty_vs).

            rename x2 into rp'.
            rename x4 into e_stack'.
            destruct H as [vs_callee' [Hrt [Hrv Hsp] ] ].
            rewrite Hsp in *.
            rename x1 into v_callee'.
            destruct v_callee' as [vs_callee'' h']; simpl in *.
            set (h'2 := fold_left _ _ _).
            set (ret_w := fst (decide_ret _ _)).
            set (ret_a := snd (decide_ret _ _)).
            assert (Hsep : separated h'2 ret_w ret_a).
            {
              unfold_all.
              unfold retv.
              rewrite fst_decide_ret_combine_ret.
              rewrite snd_decide_ret_combine_ret.
              rewrite Hrv.
              eapply runsto_TransitTo in Hrt; eauto.
              unfold TransitTo in *; openhyp.
              rewrite combine_fst_snd in *.
              eauto.
            }
            assert (Hh'2 : h' == heap_upd_option h'2 ret_w ret_a).
            {
              unfold_all.
              unfold retv.
              rewrite fst_decide_ret_combine_ret.
              rewrite snd_decide_ret_combine_ret.
              rewrite Hrv.
              eapply runsto_TransitTo in Hrt; eauto.
              unfold TransitTo in *; openhyp.
              rewrite combine_fst_snd in *.
              eauto.
            }                
            set (args' := List.map vs_callee'' avars).
            assert (Hargs' : args' = toArray avars vs_callee'').
            {
              unfold_all.
              unfold toArray in *; simpl in *.
              eauto.
            }
            assert (Hleq : length args' = length avars).
            {
              subst.
              rewrite map_length.
              eauto.
            }

            unfold is_state.
            unfold has_extra_stack.
            simpl.
            simpl_array_nil.
            simpl_locals_nil.
            rewrite plus_0_r in *.
            rewrite mult_0_r in *.
            rewrite wplus_0 in *.

            rewrite  Hleq in *.
            rewrite Hargs' in *.

            clear Hvcs Hegu Hpre Hrt Hewi.
            unfold locals.
            simpl.
            hiding ltac:(step auto_ext).
            {
              econstructor.
            }
            eapply Himp_trans.
            Focus 2.
            {
              eapply LayoutHints4Make.is_heap_upd_option_fwd; eauto.
            }
            Unfocus.
            unfold is_heap_upd_option.
            eapply is_heap_Equal; eauto.
          }
          {
            Import CompileFuncSpecMake.InvMake.SemanticsMake.
            destruct H as [vs_callee' [Hrt [Hrv Hsp] ] ].
            destruct x1 as [vs_callee'' h']; simpl in *.
            split.
            {
              Require Import Bedrock.Platform.Cito.GeneralTactics3.
              unfold_all.
              repeat rewrite map_length; eauto.
            }
            split.
            {
              rewrite Hrv.
              unfold_all.
              Import CompileFuncSpecMake.InvMake.
              eapply runsto_elim; eauto.
            }
            split.
            {
              unfold_all.
              Require Import Bedrock.Platform.Cito.SemanticsFacts6.
              rewrite make_triples_length; repeat rewrite map_length; trivial.
              Require Import Bedrock.Platform.Cito.ListFacts5.
              unfold toArray in *; simpl in *.
              eapply map_eq_length_eq; eauto.
            }
            split; trivial.
            unfold retv.
            Import WordMap.WordMap.
            destruct (find rv h'); simpl; eauto.
          }
        }
      }
    Qed.

    Theorem make_module_ok : XCAP.moduleOk make_module.
    Proof.
      eapply bmoduleOk.
      - eapply ax_mod_name_not_in_imports.
      - eapply no_dup_func_names.
      - eapply good_vcs; eauto.
        eapply incl_refl.
    Qed.

  End M.

End Make.
