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
  Require Import StringMap WordMap GLabelMap.

  Section TopSection.

    Require Import CompileUnit.

    Variable compile_unit : CompileUnit ADTValue.

    Notation pre_cond := (CompileUnit.pre_cond compile_unit).
    Notation post_cond := (CompileUnit.post_cond compile_unit).

    Require Import AutoSep.

    Notation extra_stack := 20.
    Definition compileS := SPEC("a", "b") reserving (6 + extra_stack)%nat
      Al v1, Al v2, Al h,                             
      PRE[V] is_heap h * [| pre_cond v1 v2 /\ let pairs := (V "a", v1) :: (V "b", v2) :: nil in disjoint_ptrs pairs /\ good_scalars pairs /\ WordMap.Equal h (make_heap pairs) |] * mallocHeap 0
      POST[R] Ex h', is_heap h' * [| exists r, post_cond v1 v2 r /\ let pairs := (R, r) :: nil in good_scalars pairs /\ WordMap.Equal h' (make_heap pairs) |] * mallocHeap 0.

    Notation prog := (CompileUnit.prog compile_unit).
    Definition unit_no_assign_to_args := (CompileUnit.no_assign_to_args compile_unit).
    Definition unit_syntax_ok := (CompileUnit.syntax_ok compile_unit).
    Definition unit_compile_syntax_ok := (CompileUnit.compile_syntax_ok compile_unit).
    Notation imports := (CompileUnit.imports compile_unit).

    Notation Value := (@Value ADTValue).

    Notation dfacade_safe := (CompileUnit.pre_safe compile_unit).
    Notation dfacade_runsto := (CompileUnit.pre_runsto_post compile_unit).

    Require Import DFacade.
    Require Import DFModule.
    Require Import CompileDFModule.
    Require Import Facade.NameDecoration.

    Definition core := Build_OperationalSpec argvars retvar prog eq_refl eq_refl unit_no_assign_to_args eq_refl eq_refl unit_syntax_ok.
    Definition function :=Build_DFFun core unit_compile_syntax_ok.
    Definition module := Build_DFModule imports (StringMap.add fun_name function (@StringMap.empty _)).

    Require Import ListFacts3.

    Notation specs := (GLabelMap.map (@Axiomatic _) imports).

    Require Import StringMap.
    Import StringMap.
    Require Import StringMapFacts.
    Import FMapNotations.
    Local Open Scope fmap_scope.

    Require Import Listy.
    Import Notations Instances.
    Local Open Scope listy_scope.

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

    Lemma submap_diff_empty_equal elt a b : a <= b -> b - a == WordMap.empty elt -> b == a.
      admit.
    Qed.

    Import StringMapFacts.FMapNotations.

    Import WordMapFacts.FMapNotations.

    Lemma submap_refl elt (m : WordMap.t elt) : m <= m.
      admit.
    Qed.

    Lemma make_map_make_heap_related ks values pairs st h vs cst : 
      StringMap.Equal st (make_map ks values) ->
      WordMap.Equal h (make_heap pairs) ->
      good_scalars pairs ->
      disjoint_ptrs pairs ->
      List.map fst pairs = List.map vs ks ->
      List.map snd pairs = values ->
      vs = fst cst ->
      h = snd cst ->
      CompileRunsTo.related st cst.
      admit.
    Qed.

    Lemma prog_safe cenv stmt cst stn fs v1 v2 w1 w2 :
      env_good_to_use modules imports stn fs -> 
      fst cenv = from_bedrock_label_map (Labels stn) -> 
      snd cenv = fs stn -> 
      stmt = Compile.compile (CompileDFacade.compile prog) -> 
      pre_cond v1 v2 -> 
      disjoint_ptrs ((w1, v1) :: (w2, v2) :: nil) ->
      good_scalars ((w1, v1) :: (w2, v2) :: nil) -> 
      w1 = Locals.sel (fst cst) argvar1 -> 
      w2 = Locals.sel (fst cst) argvar2 -> 
      snd cst == make_heap ((w1, v1) :: (w2, v2) :: nil) -> 
      Safe cenv stmt cst.
    Proof.
      destruct cenv as [l2w w2spec]; simpl in *.
      destruct cst as [vs h]; simpl in *.
      intros Hegtu ? ? ? Hpre Hdisj Hgs ? ? Hheq.
      subst.
      eapply compile_safe; try reflexivity; simpl in *; trivial.
      {
        eapply dfacade_safe; eauto.
        reflexivity.
      }
      {
        eapply unit_syntax_ok.
      }
      {
        eauto.
      }
      {
        eapply submap_refl.
      }
      {
        eapply make_map_make_heap_related; eauto; simpl in *.
        instantiate (1 := argvars).
        reflexivity.
        eauto.
      }
      {
        eapply env_good_to_use_cenv_impls_env; eauto.
      }
    Qed.

    Import StringMapFacts.FMapNotations.

    Import WordMapFacts.FMapNotations.

    Require Import GeneralTactics5.

    Lemma make_map_related_make_heap ks values pairs st h vs cst : 
      StringMap.Equal st (make_map ks values) ->
      CompileRunsTo.related st cst ->
      List.map fst pairs = List.map vs ks ->
      List.map snd pairs = values ->
      vs = fst cst ->
      h == snd cst ->
      WordMap.Equal h (make_heap pairs) /\
      disjoint_ptrs pairs /\
      good_scalars pairs.
      admit.
    Qed.

    Lemma prog_runsto cenv stmt cst cst' stn fs v1 v2 w1 w2 :
      RunsTo cenv stmt cst cst' -> 
      env_good_to_use modules imports stn fs -> 
      fst cenv = from_bedrock_label_map (Labels stn) -> 
      snd cenv = fs stn -> 
      stmt = Compile.compile (CompileDFacade.compile prog) -> 
      pre_cond v1 v2 -> 
      disjoint_ptrs {(w1, v1); (w2, v2)} ->
      good_scalars {(w1, v1); (w2, v2)} -> 
      w1 = Locals.sel (fst cst) argvar1 -> 
      w2 = Locals.sel (fst cst) argvar2 -> 
      snd cst == make_heap {(w1, v1); (w2, v2)} -> 
      exists vr,
        let wr := Locals.sel (fst cst') retvar in
        let pairs := {(wr, vr)} in
        post_cond v1 v2 vr /\ 
        snd cst' == make_heap pairs /\
        disjoint_ptrs pairs /\
        good_scalars pairs.
    Proof.
      destruct cenv as [l2w w2spec]; simpl in *.
      destruct cst as [vs h]; simpl in *.
      destruct cst' as [vs' h']; simpl in *.
      intros Hrt Hegtu ? ? ? Hpre Hdisj Hgs ? ? Hheq.
      subst.
      eapply compile_runsto in Hrt; try reflexivity; simpl in *; trivial.
      destruct Hrt as [st' [Hrt [Hsm Hr] ] ].
      6 : eapply env_good_to_use_cenv_impls_env; eauto.
      2 : eapply unit_syntax_ok.
      Focus 3.
      {
        eapply make_map_make_heap_related; eauto; simpl in *.
        instantiate (1 := argvars).
        reflexivity.
        eauto.
        eauto.
      }
      Unfocus.
      simpl in *.
      {
        eapply dfacade_runsto in Hrt; eauto.
        2 : reflexivity.
        destruct Hrt as [ret [Hst' Hpost] ].
        eapply make_map_related_make_heap in Hr.
        {
          destruct Hr as [Hh' [Hgs' Hdisj'] ].
          exists ret.
          repeat try_split.
          - eauto.
          - eapply Hh'.
          - eauto.
          - eauto.
        }
        {
          rewrite Hst'.
          instantiate (1 := ret :: nil).
          instantiate (1 := retvar :: nil).
          reflexivity.
        }
        {
          reflexivity.
        }
        {
          reflexivity.
        }
        {
          eauto.
        }
        {
          simpl.
          Require Import WordMapFacts.
          rewrite diff_same.
          rewrite diff_empty.
          reflexivity.
        }
      }
      {
        eapply submap_refl.
      }        
      {
        eauto.
      }
      {
        eapply dfacade_safe; eauto.
        reflexivity.
      }
    Qed.

    Import Made.

    Definition compile := bimport [[ (module_name!fun_name, spec_op_b) ]]
      bmodule "export" {{
        bfunction fun_name("a", "b", "R") [compileS]
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

    Theorem compile_ok : moduleOk compile.
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
      clear H10.
      hiding ltac:(step auto_ext).
      eapply prog_safe; eauto; simpl in *; try reflexivity.
      hiding ltac:(step auto_ext).
      repeat ((apply existsL; intro) || (apply injL; intro) || apply andL); reduce.
      apply swap; apply injL; intro.
      openhyp.
      Import LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.
      match goal with
        | [ x : State |- _ ] => destruct x; simpl in *
      end.
      rename H11 into Hrunsto.
      eapply prog_runsto in Hrunsto; eauto. 
      simpl in *.
      destruct Hrunsto as [vr [Hpost [Hheq [Hdisj Hgs] ] ] ].
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

      clear H10.
      hiding ltac:(step auto_ext).
      hiding ltac:(step auto_ext).

      sep_auto.
      sep_auto.
      {
        rewrite H10.
        rewrite H13.
        rewrite H1.
        words.
      }
      {
        eauto.
      }
      {
        rewrite H7.
        rewrite H12.
        eauto.
      }
      {
        rewrite H7.
        rewrite H12.
        eauto.
      }        
      sep_auto.
      sep_auto.
      sep_auto.
      Grab Existential Variables.
      eauto.
      eauto.
    Qed.

    Definition all := link compile (link_with_adts modules imports).

  End TopSection.

End Make.

(*
(* can only use link0 on concrete imports *)
Theorem all_ok : moduleOk all.
  link0 compile_ok. (* takes about 20 seconds *)
Qed.
*)
