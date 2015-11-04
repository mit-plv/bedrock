Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.MakeWrapper.
Require Import Bedrock.Platform.Cito.ADT Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Module Import MakeWrapperMake := MakeWrapper.Make E M.
  Export MakeWrapperMake.

  Import LinkSpecMake.
  Require Import Bedrock.Platform.Cito.LinkSpecFacts.

  Require Import Bedrock.Platform.Cito.Inv.
  Module Import InvMake := Make E.
  Module Import InvMake2 := Make M.

  Import LinkSpecMake2.
  Require Import Bedrock.Platform.Cito.StringMap Bedrock.Platform.Cito.WordMap Bedrock.Platform.Cito.GLabelMap.

  Require Import Bedrock.Platform.Cito.LinkFacts.
  Module Import LinkFactsMake := Make E.

  Require Import Bedrock.Platform.Cito.CompileModule2.
  Module CM2 := CompileModule2.Make E M.

  Section TopSection.

    Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).
    Variable exports : StringMap.t AxiomaticSpec.

    Require Import Bedrock.Platform.Facade.DFModule.
    Variable module : DFModule ADTValue.
    Require Import Bedrock.Platform.Cito.StringMapFacts.
    Hypothesis exports_in_domain : is_sub_domain exports (Funs module) = true.
    (* the name of the module that contains axiomatic export specs *)
    Variable ax_mod_name : string.
    (* the name of the module that contains operational export specs *)
    Variable op_mod_name : string.
    Hypothesis op_mod_name_ok : is_good_module_name op_mod_name = true.
    Require Import Bedrock.Platform.Cito.ListFacts3.
    Notation imports := (Imports module).
    Hypothesis op_mod_name_not_in_imports :
      let imported_module_names := List.map (fun x => fst (fst x)) (GLabelMap.elements imports) in
      List.forallb (fun x => negb (string_bool op_mod_name x)) imported_module_names = true.
    Hypothesis name_neq : negb (string_bool ax_mod_name op_mod_name) = true.
    Hypothesis Hewi : True.

    Notation Value := (@Value ADTValue).
    Require Import Bedrock.Platform.Facade.DFacade.
    Require Import Bedrock.Platform.Facade.CompileDFModule.
    Require Import Bedrock.Platform.Facade.NameDecoration.
    Require Import Bedrock.Platform.Cito.StringMap.
    Import StringMap.
    Require Import Bedrock.Platform.Cito.StringMapFacts.
    Import FMapNotations.
    Local Open Scope fmap_scope.
    Require Import Bedrock.Platform.Facade.Listy.
    Import Notations Instances.
    Local Open Scope listy_scope.

    Definition good_module := compile_to_gmodule module op_mod_name op_mod_name_ok.
    Definition gmodules := good_module :: nil.
    Require Import Bedrock.Platform.Cito.GoodModuleDec.
    Require Import Bedrock.Platform.Cito.GoodModuleDecFacts.
    Require Import Bedrock.Platform.Cito.Semantics.
    Require Import Bedrock.Platform.Facade.CompileDFacadeToCito.
    Import WordMapFacts.FMapNotations.
    Local Open Scope fmap_scope.

    Require Import Bedrock.Platform.Facade.CompileRunsTo.
    Import StringMapFacts.FMapNotations.
    Require Import Coq.Setoids.Setoid.
    Import WordMapFacts.FMapNotations.
    Require Import Bedrock.Platform.Cito.StringMapFacts.
    Require Import Bedrock.Platform.Cito.GeneralTactics4.
    Arguments empty {_}.
    Require Import Bedrock.Platform.Cito.SemanticsUtil.
    Require Import Bedrock.Platform.Cito.SemanticsFacts9.
    Arguments store_pair {_} _ _.
    Import StringMapFacts StringMap.StringMap.
    Import StringMapFacts.FMapNotations.
    Import WordMapFacts.FMapNotations.
    Require Import Bedrock.Platform.Cito.GeneralTactics5.
    Arguments empty {_}.

    Import Made.

    Arguments CM2.make_module_ok : clear implicits. 

    Definition cito_module := compile_to_cmodule module.

    Import StringMapFacts.

    Lemma is_sub_domain_complete : forall elt1 elt2 (m1 : t elt1) (m2 : t elt2), sub_domain m1 m2 -> is_sub_domain m1 m2 = true.
    Proof.
      intros.
      unfold is_sub_domain, sub_domain in *.
      eapply forallb_forall.
      intros k Hin.
      eapply mem_in_iff; eauto.
      eapply H.
      Require Import SetoidListFacts.
      eapply In_InA in Hin.
      eapply In_In_keys; eauto.     
    Qed.

    Require Import CModule.

    Lemma exports_in_domain_cmodule : is_sub_domain exports (CModule.Funs cito_module) = true.
    Proof.
      simpl.
      eapply is_sub_domain_complete.
      eapply is_sub_domain_sound in exports_in_domain.
      intros k Hin.
      do 2 eapply StringMapFacts.map_in_iff.
      eauto.
    Qed.

    Lemma Hewi_cmodule : exports_weakens_impl cito_module imports exports op_mod_name.
    Proof.
      unfold exports_weakens_impl.
      intros env_ax Henv_ax.
      Import ChangeSpec.
      Import ProgramLogic2.
      Import SemanticsFacts4.
      Notation Internal := (@Internal ADTValue).
      Require Import Bedrock.Platform.Cito.GLabel.
      Require Import Bedrock.Platform.Cito.GLabelMap.
      Import GLabelMap.
      Require Import Bedrock.Platform.Cito.GLabelMapFacts.
      Lemma strengthen_diff_intro : forall specs_diff env_ax specs, (forall lbl ax, find lbl specs_diff = Some ax -> find lbl specs = Some (Foreign ax) \/ exists op, find lbl specs = Some (Internal op) /\ strengthen_op_ax op ax env_ax) -> strengthen_diff specs specs_diff env_ax.
      Proof.
        do 3 intro.
        (* intros Hforall. *)
        (* unfold strengthen_diff. *)
        eapply fold_rec_bis with (P := fun specs_diff (H : Prop) => (forall lbl ax, find lbl specs_diff = Some ax -> find lbl specs = Some (Foreign ax) \/ exists op, find lbl specs = Some (Internal op) /\ strengthen_op_ax op ax env_ax) -> H); simpl.
        intros m m' a Heqm Ha Hforall.
        { 
          eapply Ha.
          intros lbl ax Hfind.
          rewrite Heqm in Hfind.
          eauto.
        }
        { eauto. }
        intros k e a m' Hmapsto Hnin Ha Hforall.
        unfold strengthen_diff_f.
        split.
        {
          eapply Ha.
          intros lbl ax Hfind.
          eapply Hforall.
          eapply find_mapsto_iff.
          eapply add_mapsto_iff.
          right.
          split.
          {
            intro Heq; subst.
            contradict Hnin.
            eapply MapsTo_In.
            eapply find_mapsto_iff.
            eauto.
          }
          eapply find_mapsto_iff.
          eauto.
        }
        eapply Hforall.
        eapply find_mapsto_iff.
        eapply add_mapsto_iff.
        left.
        eauto.
      Qed.
      eapply strengthen_diff_intro.
      intros lbl ax Hfind.
      right.
      eapply map_aug_mod_name_elim in Hfind.
      destruct Hfind as [k [? Hfind] ].
      subst; simpl in *.
      Require Import Bedrock.Platform.Cito.StringMap.
      Import StringMap.
      Require Import Bedrock.Platform.Cito.StringMapFacts.
      eapply is_sub_domain_sound in exports_in_domain.
      unfold sub_domain in *.
      copy_as Hfind Hin.
      eapply find_Some_in in Hin.
      eapply exports_in_domain in Hin.
      eapply in_find_Some in Hin.
      destruct Hin as [f Hf].
      eexists.
      split.
      {
        eapply specs_op_intro.
        unfold cito_module.
        Lemma find_DFModule_find_CModule k m f :
          find k (DFModule.Funs (ADTValue := ADTValue) m) = Some f ->
          find k (Funs (compile_to_cmodule m)) = Some (CompileModule.compile_func (compile_func f)).
        Proof.
          intros Hfind.
          simpl.
          eapply find_mapsto_iff.
          rewrite map_mapsto_iff.
          eexists.
          split; eauto.
          rewrite map_mapsto_iff.
          eexists.
          split; eauto.
          eapply find_mapsto_iff.
          eauto.
        Qed.
        eapply find_DFModule_find_CModule.
        eauto.
      }
      simpl.
      destruct f; simpl in *.
      destruct Core; simpl in *.
      unfold compile_func; simpl.
      unfold CompileModule.compile_func; simpl.
      unfold strengthen_op_ax; simpl.
      unfold strengthen_op_ax'; simpl.
      destruct ax; simpl in *.
      Import List.
      Definition outputs_gen words inputs h :=
        map (fun (w_input : W * Value ADTValue) =>
               let (w, input) := w_input in
               match input with
                   SCA _ => None
                 | ADT _ => heap_sel h w
               end
            ) (combine words inputs).
      Definition ret_a_gen w h := heap_sel h w.
      exists outputs_gen; simpl in *.
      exists ret_a_gen; simpl in *.
      repeat try_split.
      {
        unfold outputs_gen_ok.
        simpl.
        intros words inputs h Hpre Hlen.
        unfold outputs_gen.
        rewrite map_length.
        rewrite combine_length.
        rewrite Hlen.
        intuition.
      }
      {
        
      }
      admit.
    Qed.

    Definition output_module : XCAP.module := 
      CM2.make_module cito_module imports exports ax_mod_name op_mod_name op_mod_name_ok.

    Definition output_module_ok : moduleOk output_module.
      refine (CM2.make_module_ok cito_module imports exports _ ax_mod_name op_mod_name op_mod_name_ok op_mod_name_not_in_imports name_neq _).
      {
        eapply exports_in_domain_cmodule.
      }
      {
        eapply Hewi_cmodule.
      }
    Defined.

    Notation compile_cito_to_bedrock := compile_to_bedrock.

    Definition output_module_impl := (compile_cito_to_bedrock gmodules imports).

    Open Scope bool_scope.

    Require Import Coq.Bool.Bool.

    Import MakeWrapperMake.LinkMake.
    Import MakeWrapperMake.LinkMake.LinkModuleImplsMake.

    Lemma import_module_names_good : 
      let imported_module_names := List.map (fun x => fst (fst x)) (GLabelMap.elements imports) in
      forallb Cito.NameDecoration.is_good_module_name imported_module_names = true.
    Proof.
      generalize module; clear.
      destruct module.
      eapply import_module_names_good.
    Qed.

    Theorem output_module_impl_ok : moduleOk output_module_impl.
    Proof.

      clear ax_mod_name name_neq.
      unfold output_module_impl.

      match goal with
        | |- moduleOk (compile_to_bedrock ?Modules ?Imports ) =>
          let H := fresh in
          assert (GoodToLink_bool Modules Imports = true);
            [ unfold GoodToLink_bool(*; simpl*) |
              eapply GoodToLink_bool_sound in H; openhyp; simpl in *; eapply result_ok; simpl in * ]
            ; eauto
      end.

      eapply andb_true_iff.
      split.
      eapply andb_true_iff.
      split.
      {
        reflexivity.
      }
      {
        eapply forallb_forall.
        intros x Hin.
        rename op_mod_name_not_in_imports into Himn.
        eapply forallb_forall in Himn.
        2 : solve [eapply Hin].
        destruct (in_dec string_dec x (List.map GName gmodules)); simpl in *; trivial.
        intuition.
        subst; simpl in *; intuition.
        eapply negb_true_iff in Himn.
        Definition is_string_eq := string_bool.
        Lemma is_string_eq_iff a b : is_string_eq a b = true <-> a = b.
          unfold is_string_eq, string_bool.
          destruct (string_dec a b); intuition.
        Qed.
        Require Import Bedrock.Platform.Cito.StringSetFacts.
        Lemma is_string_eq_iff_conv a b : is_string_eq a b = false <-> a <> b.
        Proof.
          etransitivity.
          { symmetry; eapply not_true_iff_false. }
          eapply iff_not_iff.
          eapply is_string_eq_iff.
        Qed.
        eapply is_string_eq_iff_conv in Himn.
        intuition.
      }
      {
        simpl in *.
        eapply import_module_names_good.
      }
    Qed.

  End TopSection.

  Require Import Bedrock.Platform.Facade.DFModule.
  Require Import Bedrock.Platform.Cito.StringMapFacts.
  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).

  Require Import CompileUnit2.
  
  Variable exports : StringMap.t AxiomaticSpec.
  (* input of the this compiler *)
  Variable compile_unit : CompileUnit exports.

  Definition module := module compile_unit.
  Definition exports_in_domain := exports_in_domain compile_unit.
  Definition ax_mod_name := ax_mod_name compile_unit.
  Definition op_mod_name := op_mod_name compile_unit.
  Definition op_mod_name_ok := op_mod_name_ok compile_unit.
  Definition op_mod_name_not_in_imports := op_mod_name_not_in_imports compile_unit.
  Definition name_neq := name_neq compile_unit.

  Notation imports := (Imports module).
  Definition output_module' := output_module exports module ax_mod_name op_mod_name op_mod_name_ok.
  Definition output_module_ok' : moduleOk output_module' :=
    output_module_ok exports module exports_in_domain ax_mod_name op_mod_name op_mod_name_ok op_mod_name_not_in_imports name_neq.
  Definition output_module_impl' := output_module_impl module op_mod_name op_mod_name_ok.
  Definition output_module_impl_ok' : moduleOk output_module_impl' :=
    output_module_impl_ok module op_mod_name op_mod_name_ok op_mod_name_not_in_imports.

  Require Import CompileOut2.
  Definition compile : CompileOut exports :=
    Build_CompileOut exports output_module_ok' output_module_impl_ok'.

  (* In case Bedrock's tactic 'link' doesn't work well with simpl and unfold. Isn't needed in my test case *)
  Module LinkUnfoldHelp.

    Import MakeWrapperMake.LinkMake.LinkModuleImplsMake.

    Arguments Imports /.
              Arguments Exports /.
              Arguments CompileModuleMake.mod_name /.
              Arguments impl_module_name /.
              Arguments GName /.
              Arguments append /.
              Arguments CompileModuleMake.imports /.
              Arguments LinkMake.StubsMake.StubMake.bimports_diff_bexports /.
              Arguments LinkMake.StubsMake.StubMake.bimports_diff_bexports /.
              Arguments diff_map /.
              Arguments GLabelMapFacts.diff_map /.
              Arguments List.filter /.
              Arguments LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export /.
              Arguments LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label /.
              Arguments LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label /.
              Arguments GName /.
              Arguments impl_module_name /.
              Arguments append /.
              Arguments IsGoodModule.FName /.
              Arguments CompileModuleMake.mod_name /.
              Arguments impl_module_name /.
              Arguments LinkMake.StubsMake.StubMake.bimports_diff_bexports /.
              Arguments LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export /.
              Arguments LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label /.
              Arguments impl_module_name /.
              Arguments CompileModuleMake.imports /.

              Ltac link_simp2 :=
                simpl Imports;
                simpl Exports;
                unfold CompileModuleMake.mod_name;
                unfold impl_module_name;
                simpl GName;
                simpl append;
                unfold CompileModuleMake.imports;
                unfold LinkMake.StubsMake.StubMake.bimports_diff_bexports, LinkMake.StubsMake.StubMake.bimports_diff_bexports;
                unfold diff_map, GLabelMapFacts.diff_map;
                simpl List.filter;
                unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export, LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export;
                unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label, LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label;
                simpl GName;
                unfold impl_module_name;
                simpl append;
                simpl IsGoodModule.FName;
                unfold CompileModuleMake.mod_name;
                unfold impl_module_name;
                unfold LinkMake.StubsMake.StubMake.bimports_diff_bexports;
                unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export;
                unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label;
                unfold impl_module_name;
                unfold CompileModuleMake.imports.

    Ltac link2 ok1 ok2 :=
      eapply linkOk; [ eapply ok1 | eapply ok2
                       | reflexivity
                       | link_simp2; link_simp; eauto ..
                     ].

  End LinkUnfoldHelp.

End Make.
