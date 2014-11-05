Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import ChangeSpec.
  Module Import ChangeSpecMake := Make E.
  Import SemanticsFacts4Make.
  Import ProgramLogicMake.
  Import TransitMake.
  Require Import Semantics.
  Import SemanticsMake.
  Require Import LinkSpecFacts.
  Module Import LinkSpecFactsMake := Make E.
  Require Import LinkSpec.
  Import LinkSpecMake.

  Require Import GLabelMap.
  Require Import StringMap.
  Require Import CModule.

  Section M.

    Variable m : CModule.
    
    Variable imports : GLabelMap.t ForeignFuncSpec.

    Variable exports : StringMap.t ForeignFuncSpec.

    (* the name of the module that contains axiomatic export specs *)
    Variable ax_mod_name : string.

    (* the name of the module that contains operational export specs *)
    Variable op_mod_name : string.

    Hypothesis op_mod_name_ok : is_good_module_name op_mod_name = true.

    Definition cmod := cmodule_to_gmodule op_mod_name op_mod_name_ok m.

    Definition modules := cmod :: nil.

    Arguments GLabelMap.empty {elt}.

    Definition aug_mod_name elt m_name (m : StringMap.t elt) := StringMap.fold (fun k v a => GLabelMap.add (m_name, k) v a) m GLabelMap.empty.

    Definition specs_op := make_specs modules imports.
    Definition exports_with_glabel := aug_mod_name ax_mod_name exports.
    Definition specs := apply_specs_diff specs_op exports_with_glabel.

    Hypothesis specs_strengthen_diff : forall env_ax, specs_env_agree specs env_ax -> strengthen_diff specs_op exports_with_glabel env_ax.

    Lemma specs_op_equal : specs_equal specs_op modules imports.
      admit.
    Qed.

    Lemma specs_equal_domain : equal_domain specs specs_op.
      admit.
    Qed.

    Lemma new_env_strengthen : forall stn fs, env_good_to_use modules imports stn fs -> strengthen (from_bedrock_label_map (Labels stn), fs stn) (change_env specs (from_bedrock_label_map (Labels stn), fs stn)).
      intros.
      eapply strengthen_diff_strenghthen.
      - eapply specs_strengthen_diff; eauto.
        eapply change_env_agree; eauto.
        eapply specs_equal_domain; eauto.
        eapply specs_equal_agree; eauto.
        eapply specs_op_equal; eauto.
      - eapply specs_equal_agree; eauto; eapply specs_op_equal; eauto.
      - eapply change_env_agree; eauto.
        eapply specs_equal_domain; eauto.
        eapply specs_equal_agree; eauto.
        eapply specs_op_equal; eauto.
      - intros; simpl; eauto.
    Qed.

  End M.

  Require Import RepInv.

  Module Make (Import M : RepInv E).
    
    Module Import LinkSpecMakeMake := LinkSpecMake.Make M.

    Section M.

      Variable m : CModule.
      
      Variable imports : GLabelMap.t ForeignFuncSpec.

      Variable exports : StringMap.t ForeignFuncSpec.

      Variable ax_mod_name : string.

      Variable op_mod_name : string.

      Hypothesis op_mod_name_ok : is_good_module_name op_mod_name = true.

      Definition cmod := cmodule_to_gmodule op_mod_name op_mod_name_ok m.

      Definition modules := cmod :: nil.

      Definition tgt_spec name f := func_spec modules imports (op_mod_name, name) f.

      Require Import StringMapFacts.

      Definition accessible_labels := 
        List.map (fun fname => (op_mod_name, fname)) (StringMapFacts.keys exports).

      Section Fun.

        Variable fname : string.

        Variable spec : ForeignFuncSpec.

        Variable f : CFun.

        Section body.
          
          Require Import XCAP.

          Variable im : LabelMap.t assert.

          Variable im_g : importsGlobal im.

          Definition tgt : glabel := (op_mod_name, fname).

          Definition body := 
            @Seq_ _ im_g ax_mod_name
                  (AssertStar_ im ax_mod_name accessible_labels (tgt_spec fname f))
                  (Goto_ im_g ax_mod_name tgt).

        End body.

        Definition stub_spec := foreign_func_spec (ax_mod_name, fname) spec.

        Definition make_stub : StructuredModule.function ax_mod_name :=
          (fname, stub_spec, body).

      End Fun.

      Import StringMap.

      Arguments StringMap.empty {elt}.

      Definition inter elt1 elt2 (d1 : t elt1) (d2 : t elt2) := fold (fun k v1 acc => match find k d2 with | Some v2 => add k (v1, v2) acc | None => acc end) d1 empty.

      Definition content := inter exports (Funs m).

      Definition tgt_spec_as_import {unused} (x : string * (unused * CFun)) : import := 
        match x with (name, (_, f)) => (op_mod_name, name, tgt_spec name f) end.

      Definition bimports : list import := List.map tgt_spec_as_import (elements content).
      
      Definition stubs := List.map (fun x => match x with (name, (ax, op)) => make_stub name ax op end) (elements content).

      Definition make_module := StructuredModule.bmodule_ bimports stubs.

      Theorem make_module_ok : XCAP.moduleOk make_module.
        eapply bmoduleOk.
        eapply module_name_not_in_imports.
        eapply no_dup_func_names.
        eapply good_vcs; eauto.
      Qed.


(*
    Definition main_spec_Bedrock := func_spec modules imports ("count"!"main")%stmtex main.

    Definition top := bimport [[ ("count"!"main", main_spec_Bedrock), "sys"!"printInt" @ [printIntS],
                                 "sys"!"abort" @ [abortS] ]]
      bmodule "top" {{
        bfunction "top"("R") [topS]
          "R" <-- Call "count"!"main"(extra_stack)
          [PREonly[_, R] [| R = 2 |] ];;

          Call "sys"!"printInt"("R")
          [PREonly[_] Emp ];;

          Call "sys"!"abort"()
          [PREonly[_] [| False |] ]
        end
      }}.
*)

    Lemma main_safe' : forall stn fs v, env_good_to_use modules imports stn fs -> Safe (change_env specs (from_bedrock_label_map (Labels stn), fs stn)) (Body main) v.
      cito_safe main empty_precond main_vcs_good.
      eapply change_env_agree; eauto; eapply specs_equal_agree; eauto.
    Qed.

    Lemma main_safe : forall stn fs v, env_good_to_use modules imports stn fs -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body main) v.
      intros.
      eapply strengthen_safe with (env_ax := change_env specs (from_bedrock_label_map (Labels stn), fs0 stn)).
      eapply main_safe'; eauto.
      eapply new_env_strengthen; eauto.
    Qed.

    Lemma main_runsto : forall stn fs v v', env_good_to_use modules imports stn fs -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body main) v v' -> sel (fst v') (RetVar f) = 2 /\ snd v' == snd v.
      intros.
      eapply strengthen_runsto with (env_ax := change_env specs (from_bedrock_label_map (Labels stn), fs0 stn)) in H0.
      cito_runsto main empty_precond main_vcs_good.
      split; eauto.
      2 : eauto.
      eapply change_env_agree; eauto; eapply specs_equal_agree; eauto.
      eapply new_env_strengthen; eauto.
      eapply main_safe'; eauto.
    Qed.

    Require Import Inv.
    Module Import InvMake := Make ExampleADT.
    Module Import InvMake2 := Make ExampleRepInv.
    Import Made.

    Theorem top_ok : moduleOk top.
      vcgen.

      sep_auto.
      sep_auto.
      sep_auto.
      sep_auto.

      post.
      call_cito 40 (@nil string).
      hiding ltac:(evaluate auto_ext).
      unfold name_marker.
      hiding ltac:(step auto_ext).
      unfold spec_without_funcs_ok.
      post.
      descend.
      eapply CompileExprs.change_hyp.
      Focus 2.
      apply (@is_state_in''' (upd x2 "extra_stack" 40)).
      autorewrite with sepFormula.
      clear H7.
      hiding ltac:(step auto_ext).
      apply main_safe; eauto.
      hiding ltac:(step auto_ext).
      repeat ((apply existsL; intro) || (apply injL; intro) || apply andL); reduce.
      apply swap; apply injL; intro.
      openhyp.
      Import LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.
      match goal with
        | [ x : State |- _ ] => destruct x; simpl in *
      end.
      eapply_in_any main_runsto; simpl in *; intuition subst.
      eapply replace_imp.
      change 40 with (wordToNat (sel (upd x2 "extra_stack" 40) "extra_stack")).
      apply is_state_out'''''.
      NoDup.
      NoDup.
      NoDup.
      eauto.

      clear H7.
      hiding ltac:(step auto_ext).
      hiding ltac:(step auto_ext).

      sep_auto.
      sep_auto.
      sep_auto.
      sep_auto.
      sep_auto.
      sep_auto.
      sep_auto.
    Qed.

    Definition all := link top (link_with_adts modules imports).

    Theorem all_ok : moduleOk all.
      link0 top_ok.
    Qed.