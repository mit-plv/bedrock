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

  Definition cenv_impls_env (cenv : CEnv) (env : Env) :=
    forall lbl spec,
      GLabelMap.find lbl env = Some spec ->
      exists w,
        fst cenv lbl = Some w /\
        snd cenv w = Some (compile_spec spec).

  Require Import GeneralTactics.
  Require Import GeneralTactics3.
  Require Import GeneralTactics4.
  Require Import GeneralTactics5.

  Require Import StringSet.

  Require Import Label2Word Label2WordFacts.

  Require Import GLabelMap.
  Import GLabelMap.
  Require Import GLabelMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Lemma cenv_impls_env_fenv cenv env : cenv_impls_env cenv env -> exists fenv, CompileRunsTo.cenv_impls_env cenv fenv /\ fenv_impls_env fenv env.
  Proof.
    intros H.
    set (fenv :=
           {|
             Label2Word := fst cenv;
             Word2Spec w := option_map (@CompileDFacade.compile_spec _) (find_by_word (fst cenv) (elements env) w)
           |} : FEnv).
    unfold cenv_impls_env in *.
    unfold CompileRunsTo.cenv_impls_env in *.
    unfold fenv_impls_env in *.
    exists fenv.
    split.
    {
      admit.
    }
    {
      admit.
    }
  Qed.

  Require Import StringMap.
  Import StringMap.
  Require Import StringMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Notation equivf := (equiv (StringSet.singleton fun_ptr_varname)).
  Infix "===" := equivf (at level 70).

  Lemma equiv_related (st st' : State) cst : related st cst -> st' === st -> find fun_ptr_varname st' = None -> related st' cst.
    admit.
  Qed.

  Lemma not_free_vars_no_change env s st st' x : RunsTo env s st st' -> ~ StringSet.In x (free_vars s) -> find x st' = find x st.
    admit.
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
    - admit (* safe *).
  Qed.

End ADTValue.