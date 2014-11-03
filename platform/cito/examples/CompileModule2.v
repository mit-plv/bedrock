Set Implicit Arguments.

Require Import Arith.
Open Scope nat_scope.

Require Import GoodModule.
Local Notation MName := Name.
Require Import GLabelMap.
Require Import StringMap.

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

  Section M.

    Variable m : GoodModule.
    
    Variable imports : GLabelMap.t ForeignFuncSpec.

    Definition modules := m :: nil.

    Variable exports : StringMap.t ForeignFuncSpec.

    Definition m_name := MName m.

    Arguments GLabelMap.empty {elt}.

    Definition aug_mod_name elt (m : StringMap.t elt) := StringMap.fold (fun k v a => GLabelMap.add (m_name, k) v a) m GLabelMap.empty.

    Definition exports' := aug_mod_name exports.
    Definition specs_op := make_specs modules imports.
    Definition specs := apply_specs_diff specs_op exports'.

    Hypothesis specs_strengthen_diff : forall env_ax, specs_env_agree specs env_ax -> strengthen_diff specs_op exports' env_ax.

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

      Variable new_m_name : string.

      Variable m : GoodModule.
      
      Definition old_m_name := MName m.

      Definition modules := m :: nil.

      Variable imports : GLabelMap.t ForeignFuncSpec.

      Variable exports : StringMap.t ForeignFuncSpec.

      Require Import StringMapFacts.

      Definition accessible_labels := List.map (fun l => (old_m_name, l)) (StringMapFacts.keys exports).

      Section Fun.

        Variable f : GoodFunction.

        Definition fname := Name f.

        Variable spec : ForeignFuncSpec.

        Section body.
          
          Require Import XCAP.

          Variable im : LabelMap.t assert.

          Variable im_g : importsGlobal im.

          Definition tgt : glabel := (old_m_name, fname).

          Definition tgt_spec := func_spec modules imports (old_m_name, fname) f.

          Definition body := 
            @Seq_ _ im_g new_m_name
                  (AssertStar_ im new_m_name accessible_labels tgt_spec)
                  (Goto_ im_g new_m_name tgt).

        End body.

        Definition new_spec := foreign_func_spec (new_m_name, fname) spec.

        Definition make_stub : StructuredModule.function new_m_name :=
          (fname, new_spec, body).

      End Fun.
      
      (*here*)

      Notation Func_to_impl_import := func_impl_export.

      Definition bimports : list import := 
        bimports_base ++ List.map (Func_to_impl_import m) (Functions m).
      
      Definition stubs := List.map make_stub (Functions m).

      Definition bexports := List.map (@func_to_import _) stubs.

      Definition bimports_diff_bexports := diff_map bimports bexports.

      Definition make_module := StructuredModule.bmodule_ bimports_diff_bexports stubs.


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