Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import ChangeSpec.
  Require Import SemanticsFacts4.
  Require Import ProgramLogic2.
  Require Import Transit.
  Require Import Semantics.
  Require Import LinkSpecFacts.
  Module Import LinkSpecFactsMake := Make E.
  Require Import LinkSpec.
  Import LinkSpecMake.
  Import SemanticsMake.

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

    Definition aug_mod_name (m_name s : string) := (m_name, s).

    Arguments GLabelMap.empty {elt}.

    Definition map_aug_mod_name elt m_name (m : StringMap.t elt) := StringMap.fold (fun k v a => GLabelMap.add (aug_mod_name m_name k) v a) m GLabelMap.empty.

    Definition specs_op := make_specs modules imports.
    Definition exports_with_glabel := map_aug_mod_name ax_mod_name exports.
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

      Require Import ListFacts3.

      Hypothesis name_neq : negb (string_bool ax_mod_name op_mod_name) = true.

      Notation exports_weakens_impl := (exports_weakens_impl m imports exports ax_mod_name op_mod_name op_mod_name_ok).

      Hypothesis Hewi : exports_weakens_impl.

      Definition cmod := cmodule_to_gmodule op_mod_name op_mod_name_ok m.

      Definition modules := cmod :: nil.

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

      Arguments StringMap.empty {elt}.

      Definition inter elt1 elt2 (d1 : t elt1) (d2 : t elt2) := fold (fun k v1 acc => match find k d2 with | Some v2 => add k (v1, v2) acc | None => acc end) d1 empty.

      Definition content := inter (Funs m) exports.

      Definition tgt_spec_as_import {unused} (x : string * (CFun * unused)) : import := 
        let fname := fst x in
        let f := fst (snd x) in
        (tgt_label fname, tgt_spec fname f).

      Definition bimports : list import := List.map tgt_spec_as_import (elements content).

      Definition make_stub' x := 
        let name := fst x in
        let op := fst (snd x) in
        let ax := snd (snd x) in
        make_stub name ax op.

      Definition stubs := List.map make_stub' (elements content).

      Definition make_module := StructuredModule.bmodule_ bimports stubs.

      Require Import NameVC.

      Require Import StructuredModuleFacts.
      Require Import GLabelMapFacts.

      Require Import ListFacts1.

      Definition Injective A B (f : A -> B) := forall x1 x2, f x1 = f x2 -> x1 = x2.

      Lemma Injective_IsInjection A B (f : A -> B) : Injective f -> IsInjection f.
      Proof.
        unfold Injective, IsInjection in *; intuition.
      Qed.

      Require Import GeneralTactics4.

      Lemma aug_mod_name_Injection mod_name : IsInjection (aug_mod_name mod_name).
      Proof.
        eapply Injective_IsInjection.
        intros s1 s2.
        intros H.
        inject H.
        eauto.
      Qed.

      Lemma NoDupKey_bimports : NoDupKey bimports.
      Proof.
        unfold bimports.
        eapply NoDupKey_NoDup_fst.
        rewrite map_map.
        unfold tgt_spec_as_import; simpl.
        rewrite <- map_map.
        eapply Injection_NoDup.
        {
          eapply aug_mod_name_Injection.
        }
        eapply StringMapFacts.NoDup_elements.
      Qed.

      Require Import ListFacts4.

      Lemma fold_aug_mod_name {A} mod_name (x : string * A) : (mod_name, fst x) = aug_mod_name mod_name (fst x).
      Proof.
        eauto.
      Qed.

      Lemma NoDupKey_stubs : NoDupKey (List.map (@func_to_import ax_mod_name) stubs).
      Proof.
        eapply NoDupKey_NoDup_fst.
        unfold func_to_import.
        unfold stubs, make_stub', make_stub; simpl.
        repeat rewrite map_map; simpl.
        setoid_rewrite fold_aug_mod_name.
        rewrite <- map_map.
        eapply Injection_NoDup.
        {
          eapply aug_mod_name_Injection.
        }
        eapply StringMapFacts.NoDup_elements.
      Qed.

      Lemma no_dup_func_names : NoDupFuncNames stubs.
        eapply NoDup_NoDupFuncNames.
        unfold stubs, make_stub', make_stub; simpl.
        repeat rewrite map_map; simpl.
        eapply StringMapFacts.NoDup_elements.
      Qed.

      Lemma ax_neq_op_mod_name : ax_mod_name <> op_mod_name.
      Proof.
        Require Import Bool.
        eapply negb_true_iff in name_neq.
        unfold string_bool in *. 
        unfold sumbool_to_bool in *.
        destruct (string_dec ax_mod_name op_mod_name); intuition.
      Qed.

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

      Require Import Wrap.
      Require Import Inv.

      Import SemanticsMake.
      Notation gl2w := from_bedrock_label_map.
      Notation specs := (specs m imports exports ax_mod_name op_mod_name op_mod_name_ok).
      Require Import GeneralTactics5.
      Require Import SemanticsUtil.
      Lemma disjoint_ptrs_good_scalars_good_inputs pairs :
        disjoint_ptrs pairs ->
        good_scalars pairs ->
        good_inputs (make_heap pairs) pairs.
      Proof.
        intros Hdisj Hgs.
        split.
        Lemma good_scalars_forall_word_adt_match : forall pairs, List.Forall word_scalar_match pairs -> List.Forall (word_adt_match (make_heap pairs)) pairs.
          admit.
        Qed.
        - eapply good_scalars_forall_word_adt_match; eauto.
        - eauto.
      Qed.

      Coercion cfun_to_copspec (f : CFun) : InternalFuncSpec := cfun_to_gfun "" f.
      Lemma strengthen_elim_single stn fs fname op_spec ax_spec : List.In (fname, (op_spec, ax_spec)) (elements content) -> env_good_to_use modules imports stn fs -> strengthen_op_ax op_spec ax_spec ((change_env specs (gl2w (Labels stn), fs stn))).
        admit.
      Qed.

      Lemma safe_intro fun_name op_spec ax_spec stn fs vs_callee pairs : 
        List.In (fun_name, (op_spec, ax_spec)) (elements content) ->
        env_good_to_use modules imports stn fs ->
        toArray (ArgVars op_spec) vs_callee = List.map fst pairs ->
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
          unfold toArray in *; simpl in *.
          unfold TransitSafe.
          repeat try_split; eauto.
          {
            repeat rewrite map_length in *.
            Require Import ListFacts5.
            eapply map_eq_length_eq; eauto.
          }
          Ltac remove_sel :=
            match goal with
              | H : context [sel ?VS] |- _ => change (sel VS) with VS in H
              | |- context [sel ?VS] => change (sel VS) with VS
            end.
          remove_sel.
          rewrite Hfst.
          Lemma combine_fst_snd A B (pairs : list (A * B)) : List.combine (List.map fst pairs) (List.map snd pairs) = pairs.
          Proof.
            rewrite combine_map.
            setoid_rewrite <- surjective_pairing.
            rewrite map_id.
            eauto.
          Qed.
          rewrite combine_fst_snd.
          eapply disjoint_ptrs_good_scalars_good_inputs; eauto.
        }
        {
          eapply new_env_strengthen; eauto.
        }
      Qed.

      Arguments SCA {ADTValue} _.
      Arguments ADT {ADTValue} _.

      Require Import WordMap.
      Import WordMap.

      Definition retv p (h : Heap) : Ret := combine_ret p (find p h).

      Lemma runsto_elim fun_name (op_spec : CFun) ax_spec stn fs vs_callee vs_callee' h' pairs : 
        RunsTo (gl2w (Labels stn), fs stn) (Body op_spec) (vs_callee, make_heap pairs) (vs_callee', h') ->
        List.In (fun_name, (op_spec, ax_spec)) (StringMap.elements content) ->
        env_good_to_use modules imports stn fs ->
        toArray (ArgVars op_spec) vs_callee = List.map fst pairs ->
        PreCond ax_spec (List.map snd pairs) ->
        disjoint_ptrs pairs ->
        good_scalars pairs ->
        PostCond ax_spec (List.map (fun x1 => (ADTIn x1, ADTOut x1)) (make_triples pairs (List.map (heap_sel h') (List.map fst pairs)))) (retv (sel vs_callee' (RetVar op_spec)) h').
      Proof.
        intros Hrt Hin Hegu Hfst Hpre Hdisj Hgs.
        Require Import GeneralTactics4.
        copy_as Hegu Hstr; eapply strengthen_elim_single in Hstr; eauto.
        unfold toArray in *; simpl in *.
        eapply strengthen_runsto with (env_ax := change_env specs (from_bedrock_label_map (Labels stn), fs stn)) in Hrt.
        {
          set (words := List.map fst pairs) in *.
          set (inputs := List.map snd pairs) in *.
          eapply Hstr with (inputs := inputs) in Hrt; simpl in *.
          {
            unfold TransitTo in *.
            destruct Hrt as [Hleni [Hleno [Hgood [Hpre' [Hpost [Hsep Heqh' ] ] ] ] ] ]; simpl in *.
            repeat rewrite map_length in *.
            Require Import WordMap WordMapFacts.
            Import WordMap.WordMap WordMapFacts.FMapNotations.
            Local Open Scope fmap_scope.
            {
              unfold retv.
              repeat remove_sel.
              rewrite Hfst in Hpost.
              Lemma make_triples_ADTIn_ADTOut : forall pairs outs, length outs = length pairs -> List.map (fun x => (ADTIn x, ADTOut x)) (@make_triples ADTValue pairs outs) = List.combine (List.map snd pairs) outs.
              Proof.
                intros.
                erewrite <- combine_map.
                Require Import SemanticsFacts6.
                rewrite make_triples_ADTIn by eauto.
                Require Import SemanticsFacts7.
                rewrite make_triples_ADTOut by eauto.
                eauto.
              Qed.
              Require Import GeneralTactics3.
              rewrite make_triples_ADTIn_ADTOut by (unfold_all; repeat rewrite map_length; eauto).
              eauto.
            }
          }
          {
            unfold TransitSafe.
            repeat try_split; eauto.
            {
              unfold_all.
              repeat rewrite map_length in *.
              eapply map_eq_length_eq; eauto.
            }
            repeat remove_sel.
            rewrite Hfst.
            unfold_all.
            rewrite combine_fst_snd.
            eapply disjoint_ptrs_good_scalars_good_inputs; eauto.
          }
        }
        {
          eapply new_env_strengthen; eauto.
        }                
        {
          eapply Hstr.
          simpl in *.
          unfold TransitSafe.
          repeat try_split; eauto.
          {
            unfold_all.
            repeat rewrite map_length in *.
            eapply map_eq_length_eq; eauto.
          }
          repeat remove_sel.
          rewrite Hfst.
          unfold_all.
          rewrite combine_fst_snd.
          eapply disjoint_ptrs_good_scalars_good_inputs; eauto.
        }                
      Qed.

      Lemma good_inputs_add addr a h : ~ In addr h -> good_inputs (add addr a h) ((addr, ADT a) :: nil).
      Proof.
        intros Hnin.
        unfold good_inputs.
        unfold Semantics.good_inputs.
        unfold Semantics.disjoint_ptrs.
        unfold Semantics.word_adt_match.
        simpl.
        split.
        - repeat econstructor; simpl.
          rewrite add_eq_o by eauto.
          eauto.
        - repeat econstructor; eauto.
      Qed.

      Require Import WordMapFacts.
      Arguments empty {elt}.

      Lemma singleton_in_iff elt k' k (v : elt) : In k' (add k v empty) <-> k = k'.
      Proof.
        split; intros H.
        {
          eapply add_in_iff in H.
          destruct H as [? | H]; trivial.
          eapply empty_in_iff in H; intuition.
        }
        subst.
        eapply add_in_iff; eauto.
      Qed.

      Lemma add_diff_singleton elt k (v : elt) d : ~ In k d -> add k v d - add k v empty == d.
      Proof.
        intros Hnin.
        intros k'.
        destruct (weq k' k) as [? | Heq].
        {
          subst.
          rewrite diff_o_none.
          - eapply not_find_in_iff in Hnin; eauto.
          - eapply add_in_iff; eauto.
        }
        {
          rewrite diff_o.
          - rewrite add_neq_o by eauto; eauto.
          - intros Hin.
            eapply singleton_in_iff in Hin.
            subst; intuition.
        }
      Qed.

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
            eapply good_inputs_add; eauto.
          }
          {
            simpl.
            Import LayoutHints2Make.InvMake.
            Import LayoutHints2Make.InvMake2.
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
              eapply add_diff_singleton; eauto.
            }
          }
        }
        {
          clear Hewi.
          sepLemma.
        }
      Qed.

      Opaque mult.

      Require Import StringMap.
      Import StringMap.

      Lemma good_vcs ls : List.incl ls (elements content) -> vcs (makeVcs bimports stubs (List.map make_stub' ls)).
      Proof.
        induction ls; simpl; eauto.
        Require Import ListFacts4.
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
              assert (Hsep : separated h'2 ret_w ret_a) by admit.
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

              clear Hvcs Hegu Hpre Hrt Hewi.
              unfold locals.
              simpl.
              hiding ltac:(step auto_ext).
              eapply Himp_trans.
              2 : solve [eapply is_heap_upd_option_fwd; eauto].
              unfold is_heap_upd_option.
              eapply Made.Inner.is_heap_Equal; eauto.
            }
            {
              Import CompileFuncSpecMake.InvMake.SemanticsMake.
              destruct H as [vs_callee' [Hrt [Hrv Hsp] ] ].
              destruct x1 as [vs_callee'' h']; simpl in *.
              split.
              {
                Require Import GeneralTactics3.
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
                rewrite make_triples_length; repeat rewrite map_length; trivial.
                Require Import ListFacts5.
                unfold toArray in *; simpl in *.
                eapply map_eq_length_eq in Hta.
                eauto.
              }
              split; trivial.
              unfold retv.
              Import WordMap.WordMap.
              destruct (find rv h'); simpl; eauto.
            }
          }
        }
        (* universe inconsistency *)
        Set Printing Universes.
        Admitted.
      (* Qed. *)

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

End Make.
