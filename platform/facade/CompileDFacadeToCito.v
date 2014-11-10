Set Implicit Arguments.

Require Import CompileRunsTo.
Require Import CompileDFacade.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import DFacade.

  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation Value := (@Value ADTValue).
  Notation FuncSpec := (@FuncSpec ADTValue).
  Notation RunsTo := (@RunsTo ADTValue).
  Notation Safe := (@Safe ADTValue).

  Require Import Memory.
  Require Import GLabel.

  Notation CState := (@Semantics.State ADTValue).
  Notation CCallee := (@Semantics.Callee ADTValue).
  Notation CInternal := (@Semantics.Internal ADTValue).
  Notation CRunsTo := (@Semantics.RunsTo ADTValue).
  Notation CEnv := ((glabel -> option W) * (W -> option CCallee))%type.

  Notation FEnv := (@Facade.Env ADTValue).

  Require Import GLabelMap.

  Definition compile s := (Compile.compile (compile s)).

  Definition compile_spec s := (CompileRunsTo.compile_spec (@compile_spec ADTValue s)).

  Require Import Label2Word Label2WordFacts.

  Require Import GLabelMap.
  Import GLabelMap.
  Require Import GLabelMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Definition cenv_impls_env (cenv : CEnv) (env : Env) :=
    (forall lbl spec,
      GLabelMap.find lbl env = Some spec ->
      exists w,
        fst cenv lbl = Some w /\
        snd cenv w = Some (compile_spec spec)) /\
    stn_injective (fun k => In k env) (fst cenv).

  Require Import StringSet.

  Require Import Option.

  Require Import GeneralTactics.
  Require Import GeneralTactics3.
  Require Import GeneralTactics4.
  Require Import GeneralTactics5.

  Lemma option_map_some_elim A B (f : A -> B) o b : option_map f o = Some b -> exists a, o = Some a /\ f a = b.
  Proof.
    intros H.
    destruct (option_dec o) as [[a Ha]| Hn]; [rewrite Ha in H | rewrite Hn in H; discriminate]; simpl in *.
    inject H.
    exists a; eauto.
  Qed.

  Lemma option_map_some_intro A B (f : A -> B) o a b : o = Some a -> b = f a -> option_map f o = Some b.
  Proof.
    intros Ho Hb.
    destruct (option_dec o) as [[a' Ha]| Hn]; [rewrite Ha in * | rewrite Hn in *; discriminate]; simpl in *.
    inject Ho.
    eauto.
  Qed.

  Lemma cenv_impls_env_fenv cenv env : cenv_impls_env cenv env -> exists fenv, CompileRunsTo.cenv_impls_env cenv fenv /\ fenv_impls_env fenv env.
  Proof.
    intros [H Hinj].
    set (fenv :=
           {|
             Label2Word := fst cenv;
             Word2Spec w := option_map (@CompileDFacade.compile_spec _) (find_by_word (fst cenv) (elements env) w)
           |} : FEnv).
    unfold cenv_impls_env in *.
    unfold CompileRunsTo.cenv_impls_env in *.
    unfold fenv_impls_env in *.
    exists fenv.
    unfold_all; simpl in *.
    split.
    {
      split.
      {
        eauto.
      }
      {
        intros w fspec Hfw.
        eapply option_map_some_elim in Hfw.
        destruct Hfw as [spec [Hfw ?]].
        subst.
        eapply find_by_word_elements_elim in Hfw.
        destruct Hfw as [lbl [Hflbl Hlblw]].
        eapply H in Hflbl.
        destruct Hflbl as [w' [Hlblw' Hw'spec]].
        unif w'.
        eauto.
      }
    }
    {
      intros lbl spec Hflbl.
      copy_as Hflbl Hflbl'.
      eapply H in Hflbl.
      destruct Hflbl as [w [Hlblw Hwspec]].
      exists w.
      split; eauto.
      eapply option_map_some_intro; eauto.
      eapply find_by_word_elements_intro; eauto.
    }
  Qed.

  Require Import StringMap.
  Import StringMap.
  Require Import StringMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Notation equivf := (equiv (StringSet.singleton fun_ptr_varname)).
  Infix "===" := equivf (at level 70).

  Require Import String.

  Require Import Facade.NameDecoration.

  Lemma find_equiv_fpv (st1 st2 : State) x : st1 === st2 -> x <> fun_ptr_varname -> find x st1 = find x st2.
  Proof.
    intros Heq Hgn.
    unfold equiv in *.
    simpl in *.
    destruct Heq as [Heq [Hnadt1 Hnadt2]].
    eapply Heq.
    eapply StringSetFacts.singleton_not_iff; eauto.
  Qed.
  Arguments find_equiv_fpv st1 st2 [_] _ _.

  Lemma not_find_fpv_adt st1 st2 (a : ADTValue) : st1 === st2 -> find fun_ptr_varname st2 <> Some (ADT a).
  Proof.
    intros Heqv Hf.
    eapply equiv_nma_fpv in Heqv.
    eapply not_mapsto_adt_iff in Heqv.
    contradict Heqv.
    eexists; eauto.
  Qed.

  Existing Instance equiv_rel_Symmetric.
  Existing Instance equiv_rel_Transitive.

  Lemma equiv_related (st st' : State) cst : related st cst -> st' === st -> find fun_ptr_varname st' = None -> related st' cst.
  Proof.
    intros Hr Heqv Hfpv.
    unfold related.
    split.
    {
      intros k v Hfk.
      destruct (string_dec k fun_ptr_varname) as [Heqk | Hnek].
      {
        subst.
        rewrite Hfk in Hfpv; discriminate.
      }
      erewrite find_equiv_fpv in Hfk; eauto.
      eapply Hr in Hfk.
      eauto.
    }
    intros p a Hpa.
    eapply Hr in Hpa.
    destruct Hpa as [x [[Hxp Hxa] Huni]].
    destruct (string_dec x fun_ptr_varname) as [Heqx | Hnex].
    {
      subst.
      contradict Hxa.
      eapply not_find_fpv_adt; eauto.
    }
    exists x.
    split.
    {
      split; eauto.
      erewrite find_equiv_fpv; eauto.
    }
    intros x' [Hx'p Hx'a].
    destruct (string_dec x' fun_ptr_varname) as [Heqx' | Hnex'].
    {
      subst.
      contradict Hx'a.
      symmetry in Heqv.
      eapply not_find_fpv_adt; eauto.
    }
    erewrite find_equiv_fpv in Hx'a; eauto.
  Qed.

  Require Import StringSetFacts.
  Import StringSet.
  Lemma union_not_iff a b x : ~ In x (union a b) <-> (~ In x a /\ ~ In x b).
  Proof.
    etransitivity.
    - eapply iff_not_iff.
      eapply union_iff.
    - intuition.
  Qed.
  Lemma of_list_not_iff x ls : ~ In x (of_list ls) <-> ~ List.In x ls.
    etransitivity.
    - eapply iff_not_iff.
      eapply of_list_spec.
    - intuition.
  Qed.
  Lemma not_in_add_remove_many' ks : forall types outs x (st1 st2 : State), ~ List.In x ks -> find x st1 = find x st2 -> find x (add_remove_many ks types outs st1) = find x st2.
  Proof.
    induction ks; destruct types; destruct outs; simpl; try solve [intuition].
    intros x st1 st2 Hnin Hst.
    eapply Decidable.not_or in Hnin.
    destruct Hnin as [Hnin1 Hnin2].
    rename a into k.
    rename x into k'.
    destruct v as [w | a].
    {
      eauto.
    }
    destruct o as [o|].
    {
      eapply IHks; eauto.
      rewrite add_neq_o by eauto.
      eauto.
    }
    eapply IHks; eauto.
    rewrite remove_neq_o by eauto.
    eauto.
  Qed.

  Lemma not_in_add_remove_many ks : forall types outs x (st : State), ~ List.In x ks -> find x (add_remove_many ks types outs st) = find x st.
    intros; eapply not_in_add_remove_many'; eauto.
  Qed.

  Lemma not_free_vars_no_change env s st st' x : RunsTo env s st st' -> ~ StringSet.In x (free_vars s) -> find x st' = find x st.
  Proof.
    induction 1; simpl; intros Hnin.
    {
      eauto.
    }
    {
      eapply union_not_iff in Hnin.
      openhyp; rewrite IHRunsTo2; eauto.
    }
    {
      eapply union_not_iff in Hnin.
      destruct Hnin as [Hnin ?].
      eapply union_not_iff in Hnin.
      openhyp; eauto.
    }      
    {
      eapply union_not_iff in Hnin.
      destruct Hnin as [Hnin ?].
      eapply union_not_iff in Hnin.
      openhyp; eauto.
    }      
    {
      unfold_all.
      simpl in *.
      copy_as Hnin Hnin'.
      eapply union_not_iff in Hnin.
      openhyp; rewrite IHRunsTo2; eauto.
    }
    {
      eauto.
    }
    {
      rename H1 into Hst'.
      eapply union_not_iff in Hnin.
      destruct Hnin as [Hnin1 Hnin2].
      eapply singleton_not_iff in Hnin1.
      rewrite Hst'.
      rewrite add_neq_o by eauto.
      eauto.
    }      
    {
      unfold_all.
      simpl in *.
      rename H5 into Hst''.
      eapply union_not_iff in Hnin.
      destruct Hnin as [Hnin1 Hnin2].
      eapply singleton_not_iff in Hnin1.
      eapply of_list_not_iff in Hnin2.
      rewrite Hst''.
      rewrite add_neq_o by eauto.
      eapply not_in_add_remove_many; eauto.
    }
    {
      unfold_all.
      simpl in *.
      rename H6 into Hst''.
      eapply union_not_iff in Hnin.
      destruct Hnin as [Hnin1 Hnin2].
      eapply singleton_not_iff in Hnin1.
      eapply of_list_not_iff in Hnin2.
      rewrite Hst''.
      rewrite add_neq_o by eauto.
      eapply not_in_add_remove_many; eauto.
    }
  Qed.

  Require Import WordMap.
  Import WordMap.
  Require Import WordMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Theorem compile_runsto t t_env t_st t_st' :
    CRunsTo t_env t t_st t_st' -> 
    forall s, 
      t = compile s -> 
      is_syntax_ok s = true -> 
      (* h1 : the heap portion that this program is allowed to change *)
      forall h1, 
        h1 <= snd t_st -> 
        forall s_st, 
          related s_st (fst t_st, h1) -> 
          StringMap.find fun_ptr_varname s_st = None ->
          forall s_env, 
            cenv_impls_env t_env s_env -> 
            Safe s_env s s_st -> 
            exists s_st', 
              RunsTo s_env s s_st s_st' /\ 
              (* h2 : the frame heap (the outside portion that won't be touched by this program *)
              let h2 := snd t_st - h1 in 
              (* the frame heap will be intacked in the final state *)
              h2 <= snd t_st' /\ 
              (* main result: final source-level and target level states are related *)
              related s_st' (fst t_st', snd t_st' - h2).
  Proof.
    intros Hcrt s Hcomp Hsyn h1 Hsm s_st Hr Hnotmp s_env Henv Hsf.
    eapply cenv_impls_env_fenv in Henv.
    destruct Henv as [fenv [Htenv Hfenv]].
    eapply CompileRunsTo.compile_runsto in Hcrt; eauto.
    - destruct Hcrt as [s_st' [Hfrt Hsst']]; simpl in *.
      destruct Hsst' as [Hsm' [Hnoass [Hnocollide Hr']]].
      eapply CompileDFacade.compile_runsto in Hfrt; eauto.
      + destruct Hfrt as [d_st' [Hdrt Heqv]].
        exists d_st'.
        repeat try_split.
        * eauto.
        * eauto.
        * eapply equiv_related; eauto.
          eapply not_free_vars_no_change in Hdrt; eauto.
          erewrite Hdrt; eauto.
          eapply syntax_ok_fptr_not_fv; eauto.
      + eapply equiv_refl; eauto.
        eapply find_none_not_mapsto_adt; eauto.
    - eapply CompileDFacade.compile_safe; eauto.
      eapply equiv_refl; eauto.
      eapply find_none_not_mapsto_adt; eauto.
  Qed.

  Require Import CompileSafe.

  Notation CSafe := (@Semantics.Safe ADTValue).

  Theorem compile_safe s_env s s_st :
  Safe s_env s s_st ->
  is_syntax_ok s = true ->
  StringMap.find fun_ptr_varname s_st = None ->
  (* h1 : the heap portion that this program is allowed to change *)
  forall vs h h1, 
    h1 <= h -> 
    related s_st (vs, h1) -> 
    forall t_env,
      cenv_impls_env t_env s_env ->
      let t := compile s in
      let t_st := (vs, h) in
      CSafe t_env t t_st.
  Proof.
    simpl; intros Hsfs Hsyn Hsstok vs h h1 Hsm Hr t_env Henv.
    eapply cenv_impls_env_fenv in Henv.
    destruct Henv as [fenv [Htenv Hfenv]].
    eapply CompileSafe.compile_safe; eauto.
    eapply CompileDFacade.compile_safe; eauto.
    eapply equiv_refl.
    eapply find_none_not_mapsto_adt; eauto.
  Qed.

End ADTValue.