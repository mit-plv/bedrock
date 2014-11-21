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

    Definition exports_weakens_impl := forall env_ax, specs_env_agree specs env_ax -> strengthen_diff specs_op exports_with_glabel env_ax.

    Hypothesis Hewi : exports_weakens_impl.

    Lemma specs_op_equal : specs_equal specs_op modules imports.
      admit.
    Qed.

    Lemma specs_equal_domain : equal_domain specs specs_op.
      admit.
    Qed.

    Lemma new_env_strengthen : forall stn fs, env_good_to_use modules imports stn fs -> strengthen (from_bedrock_label_map (Labels stn), fs stn) (change_env specs (from_bedrock_label_map (Labels stn), fs stn)).
      intros.
      eapply strengthen_diff_strenghthen.
      - eapply Hewi; eauto.
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
    
    Require Import LayoutHints3.
    Module Import LayoutHints3Make := Make E M.
    Module Import LinkSpecMakeMake := LinkSpecMake.Make M.
    Require Import MakeWrapper.
    Module Import MakeWrapperMake := Make E M.
    Require LayoutHints2.
    Module LayoutHints2Make := LayoutHints2.Make E M.

    Section M.

      Variable m : CModule.
      
      Variable imports : GLabelMap.t ForeignFuncSpec.

      Variable exports : StringMap.t ForeignFuncSpec.

      Variable ax_mod_name : string.

      Variable op_mod_name : string.

      Hypothesis op_mod_name_ok : is_good_module_name op_mod_name = true.

      Notation exports_weakens_impl := (exports_weakens_impl m imports exports ax_mod_name op_mod_name op_mod_name_ok).

      Hypothesis Hewi : exports_weakens_impl.

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

      Definition content := inter (Funs m) exports.

      Definition tgt_spec_as_import {unused} (x : string * (CFun * unused)) : import := 
        match x with (name, (f, _)) => (op_mod_name, name, tgt_spec name f) end.

      Definition bimports : list import := List.map tgt_spec_as_import (elements content).

      Definition make_stub' x := match x with (name, (op, ax)) => make_stub name ax op end.

      Definition stubs := List.map make_stub' (elements content).

      Definition make_module := StructuredModule.bmodule_ bimports stubs.

      Require Import NameVC.
      Require Import ListFacts3.

      Hypothesis name_neq : negb (string_bool ax_mod_name op_mod_name) = true.

      Lemma ax_mod_name_not_in_imports : NameNotInImports ax_mod_name bimports.
        admit.
      Qed.

      Require Import Wrap.
      Require Import Inv.

      Opaque mult.

      Lemma good_vcs ls : List.incl ls (elements content) -> vcs (makeVcs bimports stubs (List.map make_stub' ls)).
      Proof.
        induction ls; simpl; eauto.
        Require Import ListFacts4.
        intros Hincl.
        eapply cons_incl_elim in Hincl.
        destruct Hincl as [Hin Hincl].
        wrap0.
        rename H into Hvcs.
        destruct a as [fun_name [op_spec ax_spec] ].
        wrap0.
        {
          unfold name_marker.
          hiding ltac:(step auto_ext).
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

          rename H7 into Hlong.
          rename x1 into rp.
          rename x2 into e_stack.
          rename x0 into pairs.
          rename a into stn.
          rename b into bst.
          rename H2 into Hst.
          rename H8 into Hegu.
          rename H6 into Hpre.
          rename H into Hgs.
          rename H3 into Hdisj.
          unfold is_state, has_extra_stack in Hst.
          simpl in *.

          set (arr := map fst pairs) in *.
          set (avars := ArgVars op_spec) in *.
          Require Import SepHints3.
          rewrite (@replace_array_to_locals arr _ avars) in Hst.
          assert (Halok : array_to_locals_ok arr avars) by admit.
          Ltac gd t := generalize dependent t.
          
          gd Hvcs; gd Hegu; gd Hpre; gd Hewi.
          clear Hewi.
          hiding ltac:(evaluate hints_array_to_locals).
          intros.
          rename H13 into Hta.
          rename x0 into vs_callee.
          rename H3 into Hst.

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
            Require Import Arith.
            Require Import WordFacts.
            rewrite mult_0_r in *.
            rewrite wplus_0 in *.
            rewrite plus_0_r in *.
            Ltac simpl_array_nil := let h0 := fresh in set (h0 := array nil _) in *; unfold array in h0; simpl in h0; subst h0.
            Ltac simpl_locals_nil := let h0 := fresh in set (h0 := locals nil _ _ _) in *; unfold locals in h0; unfold array in h0; simpl in h0; subst h0.
            simpl_array_nil.
            simpl_locals_nil.
            assert (Hleq : length arr = length avars) by admit.
            rewrite  Hleq in *.

            clear Hvcs Hegu Hpre Hewi.
            repeat hiding ltac:(step auto_ext).
          }
          {
            Import SemanticsMake.
            Notation gl2w := from_bedrock_label_map.
            (*here*)
            Lemma safe_intro fun_name op_spec ax_spec stn fs vs_callee pairs : 
              let h := make_heap pairs in
              List.In (fun_name, (op_spec, ax_spec)) (elements content) ->
              env_good_to_use modules imports stn fs ->
              toArray (ArgVars op_spec) vs_callee = map fst pairs ->
              PreCond ax_spec (map snd pairs) ->
              disjoint_ptrs pairs ->
              good_scalars pairs ->
              Safe (gl2w (Labels stn), fs stn) (Body op_spec) (vs_callee, h).
            Proof.
              intros Hin Hegu Hfst Hpre Hdisj Hgs.
              Notation specs := (specs m imports exports ax_mod_name op_mod_name op_mod_name_ok).
              eapply strengthen_safe with (env_ax := change_env specs (from_bedrock_label_map (Labels stn), fs stn)).
              { 
                Coercion cfun_to_copspec (f : CFun) : InternalFuncSpec := cfun_to_gfun "" f.
                Lemma strengthen_elim_single stn fs fname op_spec ax_spec : List.In (fname, (op_spec, ax_spec)) (elements content) -> env_good_to_use modules imports stn fs -> strengthen_op_ax op_spec ax_spec ((change_env specs (gl2w (Labels stn), fs stn))).
                  admit.
                Qed.
                eapply strengthen_elim_single in Hegu; eauto.
                eapply Hegu.
                simpl in *.
                eexists pairs.
                Require Import GeneralTactics5.
                repeat try_split; eauto.
                split.
                Lemma good_scalars_forall_word_adt_match : forall h pairs, List.Forall word_scalar_match pairs -> List.Forall (word_adt_match h) pairs.
                  admit.
                Qed.
                - eapply good_scalars_forall_word_adt_match; eauto.
                - eauto.
              }
              {
                eapply new_env_strengthen.
                {
                  eauto.
                }
                {
                  eapply Hegu.
                }
              }
            Qed.

            eapply safe_intro; eauto.
          }
          {
            eauto.
          }
          {
            (* post call *)
            set (rv := Regs x0 Rv) in *.
            Require Import WordMap.
            Import SemanticsMake.

            Arguments SCA {ADTValue} _.
            Arguments ADT {ADTValue} _.

            Definition retv p (h : Heap) : Ret := 
              match WordMap.find p h with
                | Some a => ADT a
                | None => SCA p
              end.

            hiding ltac:(step auto_ext).
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
              destruct H1 as [vs_callee' [Hrt [Hrv Hsp] ] ].
              rewrite Hsp in *.
              rename x1 into v_callee'.
              destruct v_callee' as [vs_callee'' h']; simpl in *.
              set (h'2 := fold_left _ _ _).
              set (ret_w := fst (decide_ret _ _)).
              set (ret_a := snd (decide_ret _ _)).
              assert (Hsep : separated h'2 ret_w ret_a) by admit.
              Require Import WordMap WordMapFacts.
              Import WordMap.WordMap WordMapFacts.FMapNotations.
              Local Open Scope fmap_scope.
              assert (Hh'2 : h' == heap_upd_option h'2 ret_w ret_a) by admit.
              set (args' := List.map vs_callee'' avars).
              assert (Hargs' : args' = toArray avars vs_callee'') by admit.
              assert (Hleq : length args' = length avars) by admit.

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

              clear Hvcs Hegu Hpre Hrt.
              unfold locals.
              simpl.
              hiding ltac:(step auto_ext).
              Lemma is_heap_upd_option_fwd h addr a : separated h addr a -> is_heap_upd_option h addr a ===> layout_option addr a * is_heap h.
              Proof.
                intros Hsep.
                unfold is_heap_upd_option, separated, Semantics.separated in *.
                destruct a as [a| ]; simpl in *.
                {
                  destruct Hsep as [? | Hsep]; try discriminate.
                  eapply Himp_trans.
                  eapply Himp_trans.
                  2 : eapply LayoutHints2Make.split_heap.
                  {
                    unfold LayoutHints2Make.heap_to_split.
                    eapply Himp_refl.
                  }
                  {
                    instantiate (1 := (addr, ADT a) :: nil).
                    admit. (* good inputs *)
                  }
                  {
                    simpl.
                    Import LayoutHints2Make.U.InvMake.
                    Import LayoutHints2Make.U.InvMake2.
                    Import SemanticsMake.
                    unfold make_heap.
                    unfold store_pair.
                    unfold heap_upd.
                    simpl.
                    eapply Himp_star_frame.
                    {
                      unfold is_heap.
                      unfold heap_elements.
                      simpl.
                      eapply Himp_trans.
                      eapply Himp_star_comm.
                      eapply Himp_star_Emp.
                    }
                    {
                      eapply Made.Inner.is_heap_Equal.
                      admit. (* Equal *)
                    }
                  }
                }
                {
                  sepLemma.
                }
              Qed.
              eapply Himp_trans.
              2 : solve [eapply is_heap_upd_option_fwd; eauto].
              unfold is_heap_upd_option.
              eapply Made.Inner.is_heap_Equal; eauto.
            }
            {
              (* side conditions *) admit.
            }
          }
        }
        {
          assert (Hf : LabelMap.find (tgt fun_name : label) (fullImports bimports stubs) = Some (tgt_spec fun_name op_spec)) by admit.
          rewrite Hf.
          eauto.
        }
        (* universe inconsistency *)
        Set Printing Universes.
        Admitted.
      (* Qed.         *)

      Theorem make_module_ok : XCAP.moduleOk make_module.
        eapply bmoduleOk.
        eapply ax_mod_name_not_in_imports.
        admit. (* eapply no_dup_func_names. *)
        eapply good_vcs; eauto.
      Qed.

    End M.

  End Make.

End Make.
