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

(*
    Lemma H_op_mod_name_not_in_imports :
      let op_mod_name := module_name in
      let imported_module_names := List.map (fun x => fst (fst x)) (GLabelMap.elements imports) in
      List.forallb (fun x => negb (string_bool op_mod_name x)) imported_module_names = true.
    Proof.
      simpl.
      destruct compile_unit; simpl in *.
      rename op_mod_name_not_in_imports into H.
      Require Import Bool.
      eapply andb_true_iff in H; destruct H as [H ?].
      eapply H.
    Qed.
*)

    Arguments CM2.make_module_ok : clear implicits. 
    Require Import CModule.

    Definition compile_to_cmodule : DFModule ADTValue -> CModule.
      admit.
    Defined.

    Definition cito_module := compile_to_cmodule module.

    Lemma exports_in_domain_cmodule : is_sub_domain exports (Funs cito_module) = true.
      admit.
    Qed.

    Lemma Hewi_cmodule : exports_weakens_impl cito_module imports exports op_mod_name.
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

    (* should be in DFModule *)
    Lemma import_module_names_good : 
      let imported_module_names := List.map (fun x => fst (fst x)) (GLabelMap.elements imports) in
      forallb Cito.NameDecoration.is_good_module_name imported_module_names = true.
      admit.
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

  Variable exports : StringMap.t AxiomaticSpec.
  Variable module : DFModule ADTValue.
  Hypothesis exports_in_domain : is_sub_domain exports (Funs module) = true.
  (* the name of the module that contains axiomatic export specs *)
  Variable ax_mod_name : string.
  (* the name of the module that contains operational export specs *)
  Variable op_mod_name : string.
  Hypothesis op_mod_name_ok : is_good_module_name op_mod_name = true.
  Hypothesis op_mod_name_not_in_imports :
    let imported_module_names := List.map (fun x => fst (fst x)) (GLabelMap.elements (Imports module)) in
    List.forallb (fun x => negb (is_string_eq op_mod_name x)) imported_module_names = true.
  Hypothesis name_neq : negb (is_string_eq ax_mod_name op_mod_name) = true.

  Notation imports := (Imports module).
  Definition output_module' := output_module exports module ax_mod_name op_mod_name op_mod_name_ok.
  Definition output_module_ok' : moduleOk output_module' :=
    output_module_ok exports module ax_mod_name op_mod_name op_mod_name_ok op_mod_name_not_in_imports name_neq.
  Definition output_module_impl' := output_module_impl module op_mod_name op_mod_name_ok.
  Definition output_module_impl_ok' : moduleOk output_module_impl' :=
    output_module_impl_ok module op_mod_name op_mod_name_ok op_mod_name_not_in_imports.

  (* input of the this compiler *)
  Variable compile_unit : CompileUnit pre_cond post_cond.

  Require Import Bedrock.Platform.Facade.CompileUnit Bedrock.Platform.Facade.CompileOut.
  Module Import CompileOutMake := CompileOut.Make E M.
  Export CompileOutMake.

  Definition compile : CompileOut pre_cond post_cond. 
    refine 
      (Build_CompileOut output_module_ok _ output_module_impl_ok).
    admit. (* will be removed *)
  Defined.

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
