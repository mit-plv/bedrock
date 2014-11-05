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

      Definition make_stub' x := match x with (name, (ax, op)) => make_stub name ax op end.

      Definition stubs := List.map make_stub' (elements content).

      Definition make_module := StructuredModule.bmodule_ bimports stubs.

      Require Import NameVC.
      Require Import ListFacts3.

      Hypothesis name_neq : negb (string_bool ax_mod_name op_mod_name) = true.

      Lemma ax_mod_name_not_in_imports : NameNotInImports ax_mod_name bimports.
        admit.
      Qed.

      Require Import Wrap.

      Lemma good_vcs ls : vcs (makeVcs bimports stubs (List.map make_stub' ls)).
        induction ls; simpl; eauto.
        Opaque funcs_ok.
        Opaque spec_without_funcs_ok.
        wrap0.
        wrap0.
        (*here*)
        admit.
        admit.
      Qed.        

      Theorem make_module_ok : XCAP.moduleOk make_module.
        eapply bmoduleOk.
        eapply ax_mod_name_not_in_imports.
        admit. (* eapply no_dup_func_names. *)
        eapply good_vcs; eauto.
      Qed.

    End M.

  End Make.

End Make.
