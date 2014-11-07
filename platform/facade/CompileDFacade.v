Set Implicit Arguments.

Require Import FacadeFacts.
Require Import DFacadeFacts.
Require Import Facade.
Require Import DFacade.

Require Import Facade.NameDecoration.
Require Import SyntaxExpr.
Require Import String.
Local Open Scope string_scope.

Local Notation PRE := tmp_prefix.
Definition fun_ptr_varname := PRE ++ "fptr".

Fixpoint compile (s : Stmt) : Facade.Stmt :=
  match s with
    | Skip => Facade.Skip
    | Seq a b => Facade.Seq (compile a) (compile b)
    | If e t f => Facade.If e (compile t) (compile f)
    | While e c => Facade.While e (compile c)
    | Assign x e => Facade.Assign x e
    | Call x f args => 
      Facade.Seq 
        (Facade.Label fun_ptr_varname f)
        (Facade.Call x (Var fun_ptr_varname) args)
  end.

Lemma compile_no_assign_to_args (spec : OperationalSpec) : is_disjoint (Facade.assigned (compile (Body spec))) (ArgVars spec) = true.
  admit.
Qed.

Definition compile_op (spec : OperationalSpec) : Facade.OperationalSpec.
  refine
    (Facade.Build_OperationalSpec (ArgVars spec) (RetVar spec) (compile (Body spec)) (args_no_dup spec) (ret_not_in_args spec) _).
  eapply compile_no_assign_to_args.
Defined.

Section ADTValue.

  Variable ADTValue : Type.

  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation Value := (@Value ADTValue).
  Notation FuncSpec := (@FuncSpec ADTValue).
  Notation RunsTo := (@RunsTo ADTValue).
  Notation Safe := (@Safe ADTValue).

  Require Import Memory.
  Require Import GLabel.

  Notation FEnv := (@Facade.Env ADTValue).
  Notation FFuncSpec := (@Facade.FuncSpec ADTValue).
  Notation FRunsTo := (@Facade.RunsTo ADTValue).
  Notation FSafe := (@Facade.Safe ADTValue).

  Require Import GLabelMap.
  Import GLabelMap.

  Arguments Facade.Operational {ADTValue} _.

  Definition compile_spec (spec : FuncSpec) : FFuncSpec :=
    match spec with
      | Axiomatic s => Facade.Axiomatic s
      | Operational s => Facade.Operational (compile_op s)
    end.

  Definition fenv_impls_env (fenv : FEnv) (env : Env) :=
    forall lbl spec,
      find lbl env = Some spec ->
      exists w,
        Label2Word fenv lbl = Some w /\
        Word2Spec fenv w = Some (compile_spec spec).
    
  Require Import GeneralTactics4.
  Require Import GeneralTactics3.

  Require Import StringMap.
  Import StringMap.
  Require Import StringMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Require Import ListFacts4.

  Require Import Setoid.
  Add Morphism FRunsTo 
      with signature (@eq FEnv) ==> (@eq Facade.Stmt) ==> (@Equal Value) ==> (@Equal Value) ==> iff as FRunsTo_m.
    admit.
  Qed.

  Require Import StringSet.

  Definition only_diff_in elt (m1 m2 : t elt) s := forall k v1 v2, find k m1 = Some v1 -> find k m2 = Some v2 -> m1 <> m2 -> StringSet.In k s.

  Coercion string2elt (x : string) : StringSet.elt := x.
  Coercion StringSet.singleton : StringSet.elt >-> StringSet.t.

  Definition equiv (a b : State) := only_diff_in a b fun_ptr_varname.

  Lemma equiv_refl st : equiv st st.
    admit.
  Qed.

  Require Import Option.

  Theorem compile_runsto : 
    forall t t_env st st', 
      FRunsTo t_env t st st' -> 
      forall s, 
        t = compile s -> 
        is_syntax_ok s = true -> 
        forall s_env, 
          fenv_impls_env t_env s_env -> 
          Safe s_env s st -> 
          exists s_st',
            RunsTo s_env s st s_st' /\
            equiv s_st' st'. 
  Proof.
    induction 1; simpl; destruct s; unfold_all; simpl in *; try solve [intros; try discriminate]; intros Hcomp Hsyn s_env Henv Hsf.
    {
      (* skip *)
      exists st.
      split.
      - eapply RunsToSkip; eauto.
      - eapply equiv_refl; eauto.
    }
    {
      Lemma is_syntax_ok_seq_elim a b : is_syntax_ok (Seq a b) = true -> is_syntax_ok a = true /\ is_syntax_ok b = true.
        admit.
      Qed.

      (* seq *)
      inject Hcomp.
      inversion Hsf; subst.
      destruct H4 as [Hsf1 Hsf2].
      rename H into Hrt1.
      rename H0 into Hrt2.
      eapply is_syntax_ok_seq_elim in Hsyn.
      destruct Hsyn as [Hsyn1 Hsyn2].
      edestruct IHRunsTo1 as [s_st' [Hsst' Heq']]; eauto.
      edestruct IHRunsTo2 as [s_st'' [Hsst'' Heq'']]; eauto.
      (*here*)
      eapply Hsf2; eauto.
      eapply
      eapply RunsToSeq; eauto.
    }
    {
      (* call *)
      inject Hcomp.
      rename H into Hrtlbl.
      rename H0 into Hrtcall.
      inversion Hrtlbl; subst.
      rename H1 into Hlw.
      rename H2 into Hnadt.
      rename H5 into Hst'.
      rewrite Hst' in Hrtcall.
      inversion Hrtcall; unfold_all; subst.
      {
        (* axiomatic *)
        rename H3 into Hfw.
        rename H4 into Hspec.
        rename H5 into Hmm.
        rename H6 into Hnadt2.
        rename H7 into Hpre.
        rename H8 into Hlen.
        rename H11 into Hpost.
        rename H12 into Hst''.
        inversion Hsf; subst.
        {
          eapply RunsToCallAx.
        

    }
    {
      (* if-true *)
      inject Hcomp.
      inversion Hsf; subst; rename H5 into He; rename H6 into Hsfbr.
      - eapply RunsToIfTrue; eauto.
      - exfalso; eapply is_true_is_false; eauto.
    }
    {
      (* if-false *)
      inject Hcomp.
      inversion Hsf; subst; rename H5 into He; rename H6 into Hsfbr.
      - exfalso; eapply is_true_is_false; eauto.
      - eapply RunsToIfFalse; eauto.
    }
    {
      (* while-true *)
      inject Hcomp.
      inversion Hsf; unfold_all; subst.
      - eapply RunsToWhileTrue; eauto.
      - exfalso; eapply is_true_is_false; eauto.
    }
    {
      (* while-false *)
      inject Hcomp.
      inversion Hsf; unfold_all; subst.
      - exfalso; eapply is_true_is_false; eauto.
      - eapply RunsToWhileFalse; eauto.
    }
    {
      (* assign *)
      inject Hcomp.
      eapply RunsToAssign; eauto.
    }
  Qed.
