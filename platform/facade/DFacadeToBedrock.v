Set Implicit Arguments.

Require Import MakeWrapper.
Require Import ADT RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Module Import MakeWrapperMake := MakeWrapper.Make E M.
  Export MakeWrapperMake.

  Import LinkSpecMake.
  Require Import LinkSpecFacts.
  Module Import LinkSpecFactsMake := Make E.
  Import LinkSpecMake.

  Require Import Inv.
  Module Import InvMake := Make E.
  Module Import InvMake2 := Make M.

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
    Notation argvar1 := "arg1".
    Notation argvar2 := "arg2".
    Notation argvars := (argvar1 :: argvar2 :: nil) (only parsing).

    Variable body : Stmt.
    Hypothesis no_assign_to_args : is_disjoint (assigned body) (StringSetFacts.of_list argvars) = true.
    Hypothesis syntax_ok : is_syntax_ok body = true.
    Variable retvar : string.
    Hypothesis ret_not_in_args : negb (is_in retvar argvars) = true.
    Hypothesis ret_name_ok : is_good_varname retvar = true.
    Definition Core := Build_OperationalSpec argvars retvar body eq_refl ret_not_in_args no_assign_to_args eq_refl ret_name_ok syntax_ok.
    Hypothesis compile_syntax_ok : FModule.is_syntax_ok (CompileDFacade.compile_op Core) = true.

    Variable imports : GLabelMap.t (AxiomaticSpec ADTValue).

    Notation Value := (@Value ADTValue).

    (* PreCond arg1 arg2 *)
    Variable PreCond : Value -> Value -> Prop.
    (* PostCond arg1 arg2 ret *)
    Variable PostCond : Value -> Value -> Value -> Prop.

    Notation specs := (GLabelMap.map (@Axiomatic _) imports).

    Require Import StringMap.
    Import StringMap.
    Require Import StringMapFacts.
    Import FMapNotations.
    Local Open Scope fmap_scope.

    Require Import Listy.
    Import Notations Instances.
    Local Open Scope listy_scope.

    Hypothesis dfacade_safe : forall st arg1 arg2, st == make_map {argvar1; argvar2} {arg1; arg2} -> PreCond arg1 arg2 -> DFacade.Safe specs body st.

    Hypothesis dfacade_runsto : forall st st' arg1 arg2, st == make_map {argvar1; argvar2} {arg1; arg2} -> PreCond arg1 arg2 -> DFacade.RunsTo specs body st st' -> exists ret, st' == make_map {retvar} {ret} /\ PostCond arg1 arg2 ret.

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

    Lemma sca_related st cst x w : @CompileRunsTo.related ADTValue st cst -> StringMap.Equal st (StringMap.add x (SCA _ w) (StringMap.empty _)) -> Locals.sel (fst cst) x = w /\ snd cst == WordMap.empty _.
      admit.
    Qed.

    Lemma submap_diff_empty_equal elt a b : a <= b -> b - a == WordMap.empty elt -> b == a.
      admit.
    Qed.
(*
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
*)

    Notation extra_stack := 20.
    Definition topS := SPEC("a", "b") reserving (6 + extra_stack)%nat
      Al v1, Al v2, Al h,                             
      PRE[V] is_heap h * [| PreCond v1 v2 /\ let pairs := {(V "a", v1); (V "b", v2)} in good_scalars pairs /\ h == make_heap pairs |] * mallocHeap 0
      POST[R] Ex h', is_heap h' * [| exists r, PostCond v1 v2 r /\ let pairs := {(R, r)} in good_scalars pairs /\ h' == make_heap pairs |] * mallocHeap 0.
    Import Made.

    Definition top := bimport [[ (module_name!fun_name, spec_op_b) ]]
      bmodule "top" {{
        bfunction "top"("a", "b", "R") [topS]
          "R" <-- Call module_name!fun_name(extra_stack, "a", "b")
          [PRE[_, R] Emp
           POST[R'] [| R' = R |] ];;
          Return "R"
        end
      }}.

    Require Import AutoSep.

      Require Import GeneralTactics3.
      Opaque mult.
      Import LinkMake.StubsMake.StubMake.LinkSpecMake2.CompileFuncSpecMake.InvMake.
      Require Import Locals.

      Theorem is_state_in2 : forall vs sp args e_stack h F, locals ("rp" :: "extra_stack" :: args) vs e_stack sp * is_heap h * mallocHeap 0 * F ===> is_state sp (Locals.sel vs "rp") (wordToNat (Locals.sel vs "extra_stack")) e_stack args (vs, h) nil * mallocHeap 0 * F.
        intros; sepLemma.
        etransitivity; [ | apply is_state_in'' ]; auto.
        sepLemma.
      Qed.

  Theorem is_state_out'' sp rp args pairs vs e_stack e_stack' h :
    NoDup args
    -> ~List.In "rp" args
    -> ~List.In "extra_stack" args
    -> length args = length pairs
    -> is_state sp rp e_stack e_stack' nil
    (vs, h) (List.map fst pairs)
    ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp
    * is_heap h * [| sel vs' "extra_stack" = e_stack |]
    * [| saved_vars vs' args pairs |].
    unfold is_state, locals, Inv.has_extra_stack; simpl.
    intros.
    apply Himp_ex_c.
    exists (upd (upd (zip_vals args pairs) "extra_stack" e_stack) "rp" rp).
    selify.
    replace (S (S (length args)) * 4)%nat with (8 + 4 * length args)%nat by omega.
    rewrite map_length.
    rewrite <- H2.
    rewrite natToWord_plus.
    eapply Himp_trans; [ | do 4 (apply Himp_star_frame; [ | apply Himp_refl ]);
      apply Himp_star_frame; [ apply Himp_refl | apply ptsto32m'_out ] ].
    simpl.
    generalize (List.map fst pairs); intro.
    unfold array at 1; simpl.
    sepLemma.
    do 2 (apply saved_vars_irrel; auto).
    eauto using saved_vars_zip_vars.

    etransitivity; [ apply himp_star_comm | ].
    apply himp_star_frame.
    etransitivity; [ | apply Arrays.ptsto32m'_in ].
    etransitivity; [ | apply ptsto32m_shift_base ].
    unfold array.
    instantiate (1 := 8).
    simpl.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    reflexivity.
    auto.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    unfold natToW.
    sepLemma.
  Qed.

  Theorem is_state_out''' sp rp args pairs vs h e_stack e_stack' :
                              NoDup args
                              -> ~List.In "rp" args
                              -> ~List.In "extra_stack" args
                              -> toArray args vs = List.map fst pairs
                              -> is_state sp rp e_stack e_stack' args
                                          (vs, h) nil
                                          ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp
                                                       * is_heap h * [| sel vs' "extra_stack" = e_stack |]
                                                       * [| saved_vars vs' args pairs |].
    unfold Himp; intros.
    etransitivity.
    2 : eapply is_state_out''; eauto.
    2 : eapply toArray_map_length; eauto.
    change LinkSpecMake2.CompileFuncSpecMake.InvMake2.is_state with is_state.
    change LinkMake.StubsMake.StubMake.LinkSpecMake2.CompileFuncSpecMake.InvMake.make_heap with make_heap.
    unfold is_state, locals, Inv.has_extra_stack; simpl.
    rewrite H2.
    Require Import Mult.
    rewrite mult_0_r.
    Require Import WordFacts.
    rewrite wplus_0.
    set (array (List.map _ _) _).
    set (is_heap _).
    rewrite map_length.
    replace (length args) with (length pairs).
    rewrite plus_0_r.
    clear_all.
    sepLemma.
    symmetry; eapply toArray_map_length; eauto.
    Grab Existential Variables.
    eauto.
  Qed.

  Theorem is_state_out''''' vs sp rp F e_stack e_stack' args h (pairs : list (W * Value ADTValue)):
    toArray args vs = List.map fst pairs ->
                               NoDup args
                               -> ~List.In "rp" args
                               -> ~List.In "extra_stack" args
                               -> (is_state sp rp e_stack e_stack' args
                                            (vs, h) nil * mallocHeap 0) * F
                                                                                     ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp * is_heap h
                                                                                                  * [| sel vs' "extra_stack" = e_stack|]
                                                                                                  * mallocHeap 0 * F.
    intros Hfstpairs.
    intros.
    eapply Himp_trans; [ do 2 (apply Himp_star_frame; [ | apply Himp_refl ]); apply is_state_out''' | ]; eauto.
    set (_ :: _ :: _).
    clear_all.
    sepLemma.
  Qed.

      Transparent mult.

    Theorem top_ok : moduleOk top.
      clear_all.
      vcgen.

      sep_auto.
      sep_auto.
      sep_auto.
      sep_auto.

      post.
      call_cito 20 (argvars).
      hiding ltac:(evaluate auto_ext).
      unfold name_marker.
      hiding ltac:(step auto_ext).
      unfold spec_without_funcs_ok.
      post.
      descend.
      set (vs := Locals.upd _ argvar2 _) in *.
      eapply CompileExprs.change_hyp.
      Focus 2.
      apply (@is_state_in2 vs).
      autorewrite with sepFormula.
      clear H9.
      hiding ltac:(step auto_ext).
      Lemma body_safe : 
        forall cenv stmt cst stn fs v1 v2 w1 w2, 
          env_good_to_use modules imports stn fs -> 
          fst cenv = from_bedrock_label_map (Labels stn) -> 
          snd cenv = fs stn -> 
          stmt = Compile.compile (CompileDFacade.compile body) -> 
          PreCond v1 v2 -> 
          good_scalars {(w1, v1); (w2, v2)} -> 
          Locals.sel (fst cst) argvar1 = w1 -> 
          Locals.sel (fst cst) argvar2 = w2 -> 
          snd cst == make_heap {(w1, v1); (w2, v2)} -> 
          Safe cenv stmt cst.
        admit.
      Qed.
      eapply body_safe; eauto; simpl in *; try reflexivity.
      hiding ltac:(step auto_ext).
      repeat ((apply existsL; intro) || (apply injL; intro) || apply andL); reduce.
      apply swap; apply injL; intro.
      openhyp.
      Import LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.
      match goal with
        | [ x : State |- _ ] => destruct x; simpl in *
      end.
      Lemma body_runsto : 
        forall cenv stmt cst cst' stn fs v1 v2 w1 w2, 
          RunsTo cenv stmt cst cst' -> 
          env_good_to_use modules imports stn fs -> 
          fst cenv = from_bedrock_label_map (Labels stn) -> 
          snd cenv = fs stn -> 
          stmt = Compile.compile (CompileDFacade.compile body) -> 
          PreCond v1 v2 -> 
          good_scalars {(w1, v1); (w2, v2)} -> 
          Locals.sel (fst cst) argvar1 = w1 -> 
          Locals.sel (fst cst) argvar2 = w2 -> 
          snd cst == make_heap {(w1, v1); (w2, v2)} -> 
          exists vr,
            let wr := Locals.sel (fst cst') retvar in
            let pairs := {(wr, vr)} in
            PostCond v1 v2 vr /\ 
            snd cst' == make_heap pairs /\
            good_scalars pairs.
        admit.
      Qed.
      rename H10 into Hrunsto.
      eapply body_runsto in Hrunsto; eauto. 
      simpl in *.
      destruct Hrunsto as [vr [Hpost [Hheq Hgs] ] ].
      eapply replace_imp.
      set (vs := Locals.upd _ argvar2 _) in *.
      change 20 with (wordToNat (Locals.sel vs "extra_stack")).

      eapply is_state_out'''''.
      {
        instantiate (1 := {(_, _); (_, _)}).
        simpl; eauto.
      }
      {
        NoDup.
      }
      {
        NoDup.
      }
      {
        NoDup.
      }

      clear H9.
      hiding ltac:(step auto_ext).
      hiding ltac:(step auto_ext).

      sep_auto.
      sep_auto.
      {
        rewrite H9.
        rewrite H12.
        rewrite H1.
        words.
      }
      {
        eauto.
      }
      {
        rewrite H7.
        rewrite H11.
        eauto.
      }
      {
        rewrite H7.
        rewrite H11.
        eauto.
      }        
      sep_auto.
      sep_auto.
      sep_auto.
      Grab Existential Variables.
      eauto.
      eauto.
    Qed.

    Definition all := link top (link_with_adts modules imports).

  End TopSection.

End Make.

(*
(* can only use link0 on concrete imports *)
Theorem all_ok : moduleOk all.
  link0 top_ok. (* takes about 20 seconds *)
Qed.
*)
