Set Implicit Arguments.

Require Import ExampleImpl.

Require Import MakeWrapper.
Require Import ExampleADT ExampleRepInv.
Module Import MakeWrapperMake := Make(ExampleADT)(ExampleRepInv).
Export MakeWrapperMake.

Import LinkSpecMake.
Require Import LinkSpecFacts.
Module Import LinkSpecFactsMake := Make ExampleADT.
Import LinkSpecMake.

Require Import Inv.
Module Import InvMake := Make ExampleADT.
Module Import InvMake2 := Make ExampleRepInv.

Import LinkSpecMake2.

Section TopSection.

  Require Import DFacade.
  Require Import DFModule.
  Require Import StringMap WordMap GLabelMap.
  Require Import CompileDFModule.
  Require Import ListFacts3.
  Require Import Facade.NameDecoration.

  Notation module_name := "dfmodule".
  Notation fun_name := "dffun".
  Notation argvars := nil.
  Notation retvar := "ret".

  Variable body : Stmt.
  Hypothesis no_assign_to_args : is_disjoint (assigned body) (StringSetFacts.of_list argvars) = true.
  Hypothesis syntax_ok : is_syntax_ok body = true.
  Definition Core := Build_OperationalSpec argvars retvar body eq_refl eq_refl no_assign_to_args eq_refl eq_refl syntax_ok.
  Hypothesis compile_syntax_ok : FModule.is_syntax_ok (CompileDFacade.compile_op Core) = true.

  Variable imports : GLabelMap.t (AxiomaticSpec ADTValue).

  Variable PostCond : W -> Prop.

  Notation specs := (GLabelMap.map (@Axiomatic _) imports).

  Hypothesis dfacade_safe : DFacade.Safe specs body (StringMap.empty _).

  Hypothesis dfacade_runsto : forall st', DFacade.RunsTo specs body (StringMap.empty _) st' -> exists w, StringMap.Equal st' (StringMap.add "ret" (SCA w) (StringMap.empty _)) /\ PostCond w.

  Definition function :=Build_DFFun Core compile_syntax_ok.
  Definition module := Build_DFModule imports (StringMap.add fun_name function (@StringMap.empty _)).

  Definition good_module := compile_to_gmodule module module_name eq_refl.

  Definition modules := good_module :: nil.

  Require Import GoodModuleDec.

  Definition dummy_gf : GoodFunction.
    refine (to_good_function f _).
    eapply is_good_func_sound.
    reflexivity.
  Defined.    

  Definition spec_op := hd dummy_gf (Functions good_module).

  Notation spec_op_b := (func_spec modules imports (module_name, fun_name) spec_op).

  Require Import Semantics.

  Notation extra_stack := 20.
  Definition topS := SPEC reserving (4 + extra_stack)%nat
    PREonly[_] mallocHeap 0.
  Import Made.

  Definition top := bimport [[ (module_name!fun_name, spec_op_b), "sys"!"printInt" @ [printIntS],
                               "sys"!"abort" @ [abortS] ]]
    bmodule "top" {{
      bfunction "top"("R") [topS]
        "R" <-- Call module_name!fun_name(extra_stack)
        [PREonly[_, R] [| PostCond R |] ];;

        Call "sys"!"printInt"("R")
        [PREonly[_] Emp ];;

        Call "sys"!"abort"()
        [PREonly[_] [| False |] ]
      end
    }}.

  Require Import CompileDFacadeToCito.

  Import WordMapFacts.FMapNotations.
  Local Open Scope fmap_scope.

  Lemma env_good_to_use_cenv_impls_env modules stn fs : env_good_to_use modules imports stn fs -> cenv_impls_env (from_bedrock_label_map (Labels stn), fs stn) (GLabelMap.map (@Axiomatic _) imports).
    admit.
  Qed.

  Lemma empty_related vs : @CompileRunsTo.related ADTValue (StringMap.empty _) (vs, (WordMap.empty _)).
    admit.
  Qed.

  Require Import Setoid.
  Global Add Morphism (@CompileRunsTo.related ADTValue) with signature StringMap.Equal ==> Logic.eq ==> iff as related_m.
  admit.
  Qed.

  Lemma sca_related st cst x w : @CompileRunsTo.related ADTValue st cst -> StringMap.Equal st (StringMap.add x (SCA w) (StringMap.empty _)) -> Locals.sel (fst cst) x = w /\ snd cst == WordMap.empty _.
    admit.
  Qed.

  Lemma submap_diff_empty_equal elt a b : a <= b -> b - a == WordMap.empty elt -> b == a.
    admit.
  Qed.

  Lemma body_safe : forall stn fs v, env_good_to_use modules imports stn fs -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body spec_op) v.
  Proof.
    intros.
    destruct v as [vs h].
    eapply compile_safe; try reflexivity; simpl in *.
    Focus 2.
    {
      eauto.
    }
    Unfocus.
    Focus 3.
    {
      eapply WordMapFacts.empty_submap.
    }
    Unfocus.
    Focus 2.
    {
      rewrite StringMapFacts.empty_o; eauto.
    }
    Unfocus.
    Focus 2.
    {
      eapply empty_related.
    }
    Unfocus.
    Focus 2.
    {
      eapply env_good_to_use_cenv_impls_env; eauto.
    }
    Unfocus.
    eapply dfacade_safe; eauto.
  Qed.

  Lemma body_runsto : forall stn fs v v', env_good_to_use modules imports stn fs -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body spec_op) v v' -> PostCond (Locals.sel (fst v') (RetVar spec_op)) /\ snd v' == snd v.
  Proof.
    intros.
    eapply compile_runsto in H0; try reflexivity; simpl in *.
    Focus 2.
    {
      eauto.
    }
    Unfocus.
    Focus 2.
    {
      eapply WordMapFacts.empty_submap.
    }
    Unfocus.
    Focus 2.
    {
      eapply empty_related.
    }
    Unfocus.
    Focus 2.
    {
      rewrite StringMapFacts.empty_o; eauto.
    }
    Unfocus.
    Focus 2.
    {
      eapply env_good_to_use_cenv_impls_env; eauto.
    }
    Unfocus.
    Focus 2.
    {
      eapply dfacade_safe; eauto.
    }
    Unfocus.
    openhyp.
    eapply dfacade_runsto in H0.
    openhyp.
    rewrite H0 in H2.
    rewrite WordMapFacts.diff_empty in H1.
    eapply sca_related in H2; simpl in *.
    Focus 2.
    {
      reflexivity.
    }
    Unfocus.
    {
      openhyp.
      rewrite H2.
      split; eauto.
      rewrite WordMapFacts.diff_empty in H4.
      eapply submap_diff_empty_equal; eauto.
    }
  Qed.

  Theorem top_ok : moduleOk top.
    clear dfacade_safe dfacade_runsto.

    vcgen.

    sep_auto.
    sep_auto.
    sep_auto.
    sep_auto.

    post.
    call_cito 20 (@nil string).
    hiding ltac:(evaluate auto_ext).
    unfold name_marker.
    hiding ltac:(step auto_ext).
    unfold spec_without_funcs_ok.
    post.
    descend.
    eapply CompileExprs.change_hyp.
    Focus 2.
    apply (@is_state_in''' (upd x2 "extra_stack" 20)).
    autorewrite with sepFormula.
    clear H7.
    hiding ltac:(step auto_ext).
    apply body_safe; eauto.
    hiding ltac:(step auto_ext).
    repeat ((apply existsL; intro) || (apply injL; intro) || apply andL); reduce.
    apply swap; apply injL; intro.
    openhyp.
    Import LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.
    match goal with
      | [ x : State |- _ ] => destruct x; simpl in *
    end.
    Require Import GeneralTactics3.
    eapply_in_any body_runsto; simpl in *; intuition subst.
    eapply replace_imp.
    change 20 with (wordToNat (Locals.sel (upd x2 "extra_stack" 20) "extra_stack")).
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

End TopSection.

Theorem all_ok : moduleOk all.
  link0 top_ok. (* takes about 20 seconds *)
Qed.

