Set Implicit Arguments.

Require Import Arith.
Open Scope nat_scope.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import ChangeSpec.
  Module Import ChangeSpecMake := Make E.
  Import SemanticsFacts4Make.
  Import TransitMake.
  Require Import Semantics.
  Import SemanticsMake.

  Section GoodModule.

    Require Import GoodModule.

    Variable gm : GoodModule.
    
    Require Import GLabelMap.
    Import GLabelMap.

    Variable imports : GLabelMap.t ForeignFuncSpec.

    Definition modules := gm :: nil.
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

    (* actually 'exports' *)
    Variable specs_change_table : GLabelMap.t ForeignFuncSpec.

    Definition specs_op := make_specs modules imports.
    Definition specs := apply_specs_diff specs_op specs_change_table.

    Lemma count_strengthen : forall env_ax, specs_env_agree specs env_ax -> strengthen_op_ax count count_spec env_ax.
      intros.
      unfold strengthen_op_ax.
      split_all.
      intros.
      simpl in *.
      openhyp.
      rewrite H0; simpl; eauto.

      intros.
      cito_safe count count_pre count_vcs_good.
      split.
      eauto.
      Import SemanticsFacts4Make.TransitMake.
      unfold TransitSafe in *.
      openhyp.
      simpl in *.
      openhyp.
      subst; simpl in *.
      Lemma combine_fst_snd : forall A B (ls : list (A * B)), List.combine (List.map fst ls) (List.map snd ls) = ls.
        induction ls; simpl; intuition.
        simpl; f_equal; eauto.
      Qed.
      Lemma combine_fst_snd' : forall A B (ls : list (A * B)) a b, a = List.map fst ls -> List.map snd ls = b -> ls = List.combine a b.
        intros.
        specialize (combine_fst_snd ls); intros.
        rewrite H0 in H1.
        rewrite <- H in H1.
        eauto.
      Qed.
      eapply_in_any combine_fst_snd'; try eassumption.
      subst; simpl in *.
      Import SemanticsMake.
      unfold good_inputs, Semantics.good_inputs in *.
      openhyp.
      unfold Semantics.word_adt_match in *.
      inversion_Forall; simpl in *.
      descend; eauto.

      cito_runsto count count_pre count_vcs_good.
      2 : split; eauto.
      unfold TransitSafe in *.
      openhyp.
      simpl in *.
      openhyp.
      subst; simpl in *.
      eapply_in_any combine_fst_snd'; try eassumption.
      subst; simpl in *.
      unfold good_inputs, Semantics.good_inputs in *.
      openhyp.
      unfold Semantics.word_adt_match in *.
      inversion_Forall; simpl in *.
      rewrite H9 in H0; injection H0; intros; subst.
      unfold TransitTo.
      descend.
      instantiate (1 := [[ {| Word := sel (fst v) "arr"; ADTIn := inr (Arr x); ADTOut := Some (Arr x) |}, {| Word := sel (fst v) "len"; ADTIn := inl (sel (fst v) "len"); ADTOut := None |} ]]); eauto.
      split.
      unfold Semantics.word_adt_match in *.
      simpl.
      repeat econstructor.
      simpl; eauto.
      unfold Semantics.disjoint_ptrs.
      NoDup.
      simpl.
      descend.
      eauto.
      eauto.
      eauto.
      simpl.
      descend; eauto.
      simpl.
      unfold store_out, Semantics.store_out in *; simpl in *.
      repeat econstructor.
      simpl.
      unfold store_out, Semantics.store_out in *; simpl in *.
      Import WordMap.
      rewrite H2.
      Lemma add_no_effect : forall elt k v h, @find elt k h = Some v -> add k v h == h.
        unfold Equal; intros.
        repeat rewrite add_o.
        destruct (eq_dec k y); subst; intuition.
      Qed.
      rewrite add_no_effect; eauto; reflexivity.
      unfold decide_ret, Semantics.decide_ret.
      simpl.
      eauto.

      unfold TransitSafe in *.
      openhyp.
      simpl in *.
      openhyp.
      subst; simpl in *.
      specialize (combine_fst_snd x); intros.
      rewrite H3 in H4.
      rewrite <- H1 in H4.
      subst; simpl in *.
      unfold good_inputs, Semantics.good_inputs in *.
      openhyp.
      unfold Semantics.word_adt_match in *.
      inversion_Forall; simpl in *.
      descend; eauto.
      Grab Existential Variables.
      eapply ($0).
    Qed.

    Lemma main_vcs_good : and_all (vc main_body empty_precond) specs.
      unfold empty_precond, main_body; simpl; unfold imply_close, and_lift; simpl; split_all.

      (* vc1 *)
      intros.
      subst.
      unfold SafeDCall.
      simpl.
      intros.
      Import Notations4Make.
      Import ProgramLogicMake.
      Import TransitMake.
      unfold TransitSafe.
      descend.
      instantiate (1 := [[ ($3, _) ]]).
      eauto.
      repeat econstructor.
      instantiate (1 := inl $3).
      repeat econstructor.
      repeat econstructor.
      descend; eauto.

      (* vc2 *)
      intros.
      destruct_state.
      openhyp.
      subst.
      unfold RunsToDCall in *.
      simpl in *.
      openhyp.
      unfold TransitTo in *.
      openhyp.
      unfold PostCond in *; simpl in *.
      openhyp.
      subst; simpl in *.
      eapply triples_intro in H3; try eassumption.
      subst; simpl in *.
      Import SemanticsMake.
      unfold good_inputs, Semantics.good_inputs in *.
      openhyp.
      unfold Semantics.word_adt_match in *.
      inversion_Forall; simpl in *.
      subst.
      unfold store_out, Semantics.store_out in *; simpl in *.
      descend; eauto.
      rewrite H5.
      eapply separated_star; eauto.

      (* vc3 *)
      intros.
      unfold SafeDCall.
      simpl.
      intros.
      destruct_state.
      openhyp.
      destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in *; rewrite update_add in *.
      unfold TransitSafe.
      descend.
      sel_upd_simpl.
      eapply map_fst_combine.
      instantiate (1 := [[ _, _, _ ]]); eauto.
      split.
      unfold Semantics.word_adt_match.
      repeat econstructor; simpl.
      eauto.
      instantiate (1 := inr (Arr x)); simpl in *.
      rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
      instantiate (1 := inl $0); simpl in *.
      eauto.
      instantiate (1 := inl $10); simpl in *.
      eauto.
      simpl.
      unfold Semantics.disjoint_ptrs.
      NoDup.
      descend; eauto.
      rewrite H0.
      eauto.

      (* vc4 *)
      intros.
      openhyp.
      destruct_state.
      destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
      unfold RunsToDCall in *.
      simpl in *.
      openhyp.
      unfold TransitTo in *.
      openhyp.
      unfold PostCond in *; simpl in *.
      openhyp.
      subst; simpl in *.
      eapply_in_any triples_intro; try eassumption.
      subst; simpl in *.
      unfold store_out, Semantics.store_out in *; simpl in *.
      unfold good_inputs, Semantics.good_inputs in *.
      openhyp.
      unfold Semantics.word_adt_match in *.
      inversion_Forall; simpl in *.
      subst; simpl in *.
      sel_upd_simpl.
      rewrite H in H10.
      eapply_in_any add_o_eq; subst.
      injection H10; intros; subst.
      descend.
      split.
      rewrite H8.
      rewrite H; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
      eapply map_add_same_key.
      eapply same_keys_all_disj; eauto.
      simpl; eauto.
      rewrite upd_length; eauto.
      eapply CompileExpr.sel_upd_eq; eauto.
      rewrite H1; eauto.

      (* vc5 *)
      intros.
      unfold SafeDCall.
      simpl.
      intros.
      destruct_state.
      openhyp.
      destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
      unfold TransitSafe.
      sel_upd_simpl.
      descend.
      eapply map_fst_combine.
      instantiate (1 := [[ _, _, _ ]]); eauto.
      split.
      unfold Semantics.word_adt_match.
      repeat econstructor; simpl.
      instantiate (1 := inr (Arr x)); simpl in *.
      rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
      instantiate (1 := inl $1); simpl in *.
      eauto.
      instantiate (1 := inl $20); simpl in *.
      eauto.
      simpl.
      unfold Semantics.disjoint_ptrs.
      NoDup.
      descend; eauto.
      rewrite H0; eauto.

      (* vc6 *)
      intros.
      openhyp.
      destruct_state.
      destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
      unfold RunsToDCall in *.
      simpl in *.
      openhyp.
      unfold TransitTo in *.
      openhyp.
      unfold PostCond in *; simpl in *.
      openhyp.
      subst; simpl in *.
      eapply_in_any triples_intro; try eassumption.
      subst; simpl in *.
      unfold store_out, Semantics.store_out in *; simpl in *.
      unfold good_inputs, Semantics.good_inputs in *.
      openhyp.
      unfold Semantics.word_adt_match in *.
      inversion_Forall; simpl in *.
      subst; simpl in *.
      sel_upd_simpl.
      rewrite H in H11; eapply_in_any add_o_eq; subst; injection H11; intros; subst.
      destruct x5; simpl in *; try discriminate.
      destruct x5; simpl in *; try discriminate.
      destruct x5; simpl in *; try discriminate.
      descend.
      split.
      rewrite H9.
      rewrite H; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
      eapply map_add_same_key.
      eapply same_keys_all_disj; eauto.
      simpl; eauto.
      Transparent natToWord.
      unfold Array.upd; simpl.
      unfold Array.sel in H2; simpl in H2; subst.
      repeat f_equal.
      destruct x5; simpl in *; try discriminate.
      eauto.
      Opaque natToWord.

      (* vc7 *)
      intros.
      unfold SafeDCall.
      simpl.
      intros.
      destruct_state.
      openhyp.
      destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
      unfold TransitSafe.
      sel_upd_simpl.
      descend.
      eapply map_fst_combine.
      instantiate (1 := [[ _, _, _ ]]); eauto.
      split.
      unfold Semantics.word_adt_match.
      repeat econstructor; simpl.
      instantiate (1 := inr (Arr x)); simpl in *.
      rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
      instantiate (1 := inl $2); simpl in *.
      eauto.
      instantiate (1 := inl $10); simpl in *.
      eauto.
      simpl.
      unfold Semantics.disjoint_ptrs.
      NoDup.
      descend; eauto.
      rewrite H0; eauto.

      (* vc8 *)
      intros.
      openhyp.
      destruct_state.
      destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
      unfold RunsToDCall in *.
      simpl in *.
      openhyp.
      unfold TransitTo in *.
      openhyp.
      unfold PostCond in *; simpl in *.
      openhyp.
      subst; simpl in *.
      eapply_in_any triples_intro; try eassumption.
      subst; simpl in *.
      unfold store_out, Semantics.store_out in *; simpl in *.
      unfold good_inputs, Semantics.good_inputs in *.
      openhyp.
      unfold Semantics.word_adt_match in *.
      inversion_Forall; simpl in *.
      subst; simpl in *.
      sel_upd_simpl.
      rewrite H in H9; eapply_in_any add_o_eq; subst; injection H9; intros; subst.
      descend.
      split.
      rewrite H8.
      rewrite H; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
      eapply map_add_same_key.
      eapply same_keys_all_disj; eauto.
      simpl; eauto.
      Transparent natToWord.
      reflexivity.
      Opaque natToWord.

      (* vc9 *)
      intros.
      unfold SafeDCall.
      simpl.
      intros.
      destruct_state.
      openhyp.
      destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
      unfold TransitSafe.
      sel_upd_simpl.
      descend.
      eapply map_fst_combine.
      instantiate (1 := [[ _, _ ]]); eauto.
      split.
      unfold Semantics.word_adt_match.
      repeat econstructor; simpl.
      instantiate (1 := inr (Arr x)); simpl in *.
      rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
      instantiate (1 := inl $3); simpl in *.
      eauto.
      simpl.
      unfold Semantics.disjoint_ptrs.
      NoDup.
      descend.
      eauto.
      rewrite H0; eauto.
      rewrite H0; simpl.
      eauto.

      (* vc10 *)
      intros.
      openhyp.
      destruct_state.
      destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
      unfold RunsToDCall in *.
      simpl in *.
      openhyp.
      unfold TransitTo in *.
      openhyp.
      unfold PostCond in *; simpl in *.
      openhyp.
      subst; simpl in *.
      eapply_in_any triples_intro; try eassumption.
      subst; simpl in *.
      unfold store_out, Semantics.store_out in *; simpl in *.
      unfold good_inputs, Semantics.good_inputs in *.
      openhyp.
      unfold Semantics.word_adt_match in *.
      inversion_Forall; simpl in *.
      subst; simpl in *.
      sel_upd_simpl.
      rewrite H in H9; eapply_in_any add_o_eq; subst; injection H9; intros; subst.
      descend.
      split.
      rewrite H8.
      rewrite H; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
      eapply map_add_same_key.
      eapply same_keys_all_disj; eauto.
      simpl; eauto.
      reflexivity.

      (* vc11 *)
      intros.
      unfold SafeDCall.
      simpl.
      intros.
      destruct_state.
      openhyp.
      destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
      unfold TransitSafe.
      sel_upd_simpl.
      descend.
      eapply map_fst_combine.
      instantiate (1 := [[ _ ]]); eauto.
      split.
      unfold Semantics.word_adt_match.
      repeat econstructor; simpl.
      instantiate (1 := inr (Arr x)); simpl in *.
      rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
      simpl.
      unfold Semantics.disjoint_ptrs.
      NoDup.
      descend.
      eauto.

      (* vc12 *)
      intros.
      openhyp.
      destruct_state.
      destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
      unfold RunsToDCall in *.
      simpl in *.
      openhyp.
      unfold TransitTo in *.
      openhyp.
      unfold PostCond in *; simpl in *.
      openhyp.
      subst; simpl in *.
      eapply_in_any triples_intro; try eassumption.
      subst; simpl in *.
      unfold store_out, Semantics.store_out in *; simpl in *.
      unfold good_inputs, Semantics.good_inputs in *.
      openhyp.
      unfold Semantics.word_adt_match in *.
      inversion_Forall; simpl in *.
      subst; simpl in *.
      sel_upd_simpl.
      rewrite H in H10; eapply_in_any add_o_eq; subst; injection H10; intros; subst.
      descend.
      rewrite H8.
      rewrite H.
      eapply not_in_add_remove.
      eapply singleton_disj.
      inv_clear H2.
      inversion_Forall.
      eauto.

      eauto.
    Qed.

    Local Hint Immediate main_vcs_good.

    Lemma main_strengthen : forall env_ax, specs_env_agree specs env_ax -> strengthen_op_ax main main_spec env_ax.
      intros.
      unfold strengthen_op_ax.
      split_all.
      intros.
      simpl in *.
      rewrite H0; simpl; eauto.

      intros.
      cito_safe main empty_precond main_vcs_good.

      cito_runsto main empty_precond main_vcs_good.
      2 : eauto.
      Import SemanticsFacts4Make.TransitMake.
      unfold TransitTo.
      descend.
      instantiate (1 := [[]]).
      eauto.
      simpl.
      Import SemanticsMake.
      repeat econstructor.
      eauto.
      eauto.
      simpl.
      repeat econstructor.
      simpl.
      eauto.
      unfold decide_ret, Semantics.decide_ret.
      simpl.
      eauto.
      Grab Existential Variables.
      eapply ($0).
    Qed.

    Lemma specs_strengthen_diff : forall env_ax, specs_env_agree specs env_ax -> strengthen_diff specs_op specs_change_table env_ax.
      intros.
      unfold strengthen_diff.
      rewrite GLabelMap.fold_1.
      Opaque specs specs_op.
      simpl.
      Transparent specs specs_op.
      unfold strengthen_diff_f.
      split_all.
      eauto.
      right.
      eexists.
      split.
      reflexivity.
      eapply count_strengthen; eauto.
      right.
      eexists.
      split.
      reflexivity.
      eapply main_strengthen; eauto.
    Qed.

    Import LinkSpecMake.
    Require Import LinkSpecFacts.
    Module Import LinkSpecFactsMake := Make ExampleADT.

    Import GLabelMap.GLabelMap.
    Import GLabelMapFacts.
    Import LinkSpecMake.

    Lemma specs_op_equal : specs_equal specs_op modules imports.
      split; intros.
      unfold specs_equal, specs_op in *; simpl in *.
      eapply find_mapsto_iff in H; eapply add_mapsto_iff in H; openhyp.
      subst; simpl in *.
      left; descend; eauto.
      unfold gm, to_good_module; simpl; eauto.
      eapply add_mapsto_iff in H0; openhyp.
      subst; simpl in *.
      left; descend; eauto.
      unfold gm, to_good_module; simpl; eauto.
      eapply map_mapsto_iff in H1; openhyp.
      subst; simpl in *.
      eapply find_mapsto_iff in H2.
      right; descend; eauto.

      unfold label_mapsto in *.
      openhyp.
      subst; simpl in *.
      openhyp.
      subst; simpl in *.
      openhyp.
      subst; simpl in *.
      reflexivity.
      subst; simpl in *.
      reflexivity.
      intuition.
      intuition.
      subst; simpl in *.
      assert (lbl <> ("count", "count") /\ lbl <> ("count", "main")).
      split.
      nintro.
      subst; simpl in *.
      compute in H0; intuition.
      nintro.
      subst; simpl in *.
      compute in H0; intuition.
      openhyp.
      eapply find_mapsto_iff.
      eapply add_mapsto_iff.
      right.
      split.
      eauto.
      eapply add_mapsto_iff.
      right.
      split.
      eauto.
      eapply find_mapsto_iff in H0.
      eapply map_mapsto_iff.
      descend; eauto.
    Qed.

    Lemma specs_equal_domain : equal_domain specs specs_op.
      eapply equal_domain_dec_sound; reflexivity.
    Qed.

    Hint Resolve specs_op_equal specs_equal_domain.

    Lemma new_env_strengthen : forall stn fs, env_good_to_use modules imports stn fs -> strengthen (from_bedrock_label_map (Labels stn), fs stn) (change_env specs (from_bedrock_label_map (Labels stn), fs stn)).
      intros.
      eapply strengthen_diff_strenghthen.
      Focus 2.
      eapply specs_equal_agree; eauto.
      Focus 2.
      eapply change_env_agree; eauto; eapply specs_equal_agree; eauto.
      eapply specs_strengthen_diff; eauto.
      eapply change_env_agree; eauto; eapply specs_equal_agree; eauto.
      intros; simpl; eauto.
    Qed.

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