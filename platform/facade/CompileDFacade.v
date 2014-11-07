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

  Definition fenv_impls_env (fenv : FEnv) (env : Env) :=
    forall lbl spec,
      find lbl env = Some spec ->
      exists w,
        Label2Word fenv lbl = Some w /\
        Word2Spec fenv w = Some (Axiomatic spec).
    
  Require Import GeneralTactics4.
  Require Import GeneralTactics3.

  Require Import StringMap.
  Import StringMap.
  Require Import StringMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Arguments SCA {ADTValue} _.
  Arguments ADT {ADTValue} _.

  Require Import ListFacts4.

  Require Import Setoid.
(*
  Add Morphism FRunsTo 
      with signature (@eq FEnv) ==> (@eq Facade.Stmt) ==> (@Equal Value) ==> (@Equal Value) ==> iff as FRunsTo_m.
    admit.
  Qed.
*)

  Hint Extern 0 (_ == _) => reflexivity.

  Require Import StringSet.

  Definition only_diff_in s (m1 m2 : State) := forall k v1 v2, find k m1 = Some v1 -> find k m2 = Some v2 -> m1 <> m2 -> StringSet.In k s /\ (exists w1, v1 = SCA w1) /\ exists w2, v2 = SCA w2.

  Coercion string2elt (x : string) : StringSet.elt := x.
  Coercion StringSet.singleton : StringSet.elt >-> StringSet.t.

  Definition equiv := only_diff_in fun_ptr_varname.

  Add Morphism equiv 
      with signature Equal ==> Equal ==> iff as equiv_m.
    admit.
  Qed.

  Infix "===" := equiv (at level 70).

  Require Import Option.

  Lemma is_syntax_ok_seq_elim a b : is_syntax_ok (Seq a b) = true -> is_syntax_ok a = true /\ is_syntax_ok b = true.
    admit.
  Qed.
  Definition is_syntax_ok_e e := StringSet.for_all is_good_varname (FreeVarsExpr.free_vars e).
  Lemma is_syntax_ok_if_elim e a b : is_syntax_ok (If e a b) = true -> is_syntax_ok_e e = true /\ is_syntax_ok a = true /\ is_syntax_ok b = true.
    admit.
  Qed.
  Lemma is_syntax_ok_while_elim e b : is_syntax_ok (While e b) = true -> is_syntax_ok_e e = true /\ is_syntax_ok b = true.
    admit.
  Qed.
  Lemma is_syntax_ok_assign_elim x e : is_syntax_ok (Assign x e) = true -> is_good_varname x = true /\ is_syntax_ok_e e = true.
    admit.
  Qed.

  Lemma find_equiv st1 st2 x : st1 === st2 -> is_good_varname x = true -> find x st1 = find x st2.
    admit.
  Qed.
  Lemma eval_equiv st1 st2 e : st1 === st2 -> is_syntax_ok_e e = true -> eval st1 e = eval st2 e.
    admit.
  Qed.
  Lemma is_false_equiv st1 st2 e : is_false st1 e -> st1 === st2 -> is_syntax_ok_e e = true -> is_false st2 e.
    admit.
  Qed.
  Lemma is_true_equiv st1 st2 e : is_true st1 e -> st1 === st2 -> is_syntax_ok_e e = true -> is_true st2 e.
    admit.
  Qed.
  Lemma not_mapsto_adt_equiv st1 st2 x : st1 === st2 -> is_good_varname x = true -> not_mapsto_adt x st1 = not_mapsto_adt x st2.
    admit.
  Qed.
  Lemma add_equiv st1 st2 x v : st1 === st2 -> is_good_varname x = true -> add x v st1 === add x v st2.
    admit.
  Qed.

  Lemma equiv_intro st1 st2 w : st1 == add fun_ptr_varname (SCA w) st2 -> st1 === st2.
    admit.
  Qed.

  Lemma equiv_sym a b : a === b -> b === a.
    admit.
  Qed.

  Lemma equiv_trans a b c : a === b -> b === c -> a === c.
    admit.
  Qed.

  Add Relation State equiv
      symmetry proved by equiv_sym
      transitivity proved by equiv_trans
        as equiv_rel.

  Lemma is_syntax_ok_call_elim x f args : is_syntax_ok (Call x f args) = true -> is_good_varname x = true /\ List.forallb is_good_varname args = true.
    admit.
  Qed.

  Lemma mapM_find_equiv st1 st2 ls : st1 === st2 -> List.forallb is_good_varname ls = true -> mapM (sel st1) ls = mapM (sel st2) ls.
    admit.
  Qed.
  Arguments mapM_find_equiv st1 st2 [_] _ _.

  Lemma add_remove_many_equiv st1 st2 args input output : st1 === st2 -> List.forallb is_good_varname args = true -> add_remove_many args input output st1 === add_remove_many args input output st2.
    admit.
  Qed.

  Theorem compile_runsto t t_env t_st t_st' :
    FRunsTo t_env t t_st t_st' -> 
    forall s, 
      t = compile s -> 
      is_syntax_ok s = true -> 
      forall s_env, 
        fenv_impls_env t_env s_env -> 
        forall s_st,
          Safe s_env s s_st -> 
          equiv s_st t_st ->
          exists s_st',
            RunsTo s_env s s_st s_st' /\
            equiv s_st' t_st'. 
  Proof.
    induction 1; simpl; destruct s; unfold_all; simpl in *; try solve [intros; try discriminate]; intros Hcomp Hsyn s_env Henv s_st Hsf Heqv.
    {
      (* skip *)
      exists s_st; split.
      - eapply RunsToSkip; eauto.
      - eauto.
    }
    {
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
      exists s_st''; split.
      - eapply RunsToSeq; eauto.
      - eauto.
    }
    {
      (* call *)
      inject Hcomp.
      rename s into x.
      rename g into lbl.
      rename l into args.
      rename H into Hrtlbl.
      rename H0 into Hrtcall.
      inversion Hrtlbl; subst.
      rename H1 into Hlw.
      rename H2 into Hnadt.
      rename H5 into Hst'.
      copy_as Hst' Hst'2.
      eapply equiv_intro in Hst'.
      assert (Heqv' : st' === s_st) by
          (etransitivity; eauto; symmetry; eauto).
      eapply is_syntax_ok_call_elim in Hsyn.
      destruct Hsyn as [Hsynx Hsynargs].
      inversion Hsf; subst.
      rename H2 into Hflbl.
      rename H3 into Hmm'.
      rename H5 into Hxnadt.
      rename H6 into Hpre'.
      copy_as Hflbl Hflbl'; eapply Henv in Hflbl.
      destruct Hflbl as [f_w' [Hfw' Hspec']]; simpl in *.
      unif f_w'.
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
        simpl in *.
        rewrite Hst'2 in Hfw.
        rewrite add_eq_o in Hfw by eauto.
        inject Hfw.
        unif (Facade.Axiomatic spec0).
        rewrite (mapM_find_equiv st' s_st) in Hmm by eauto.
        unif input0.
        exists (add x ret (add_remove_many args input (wrap_output output) s_st)).
        split.
        {
          eapply RunsToCallAx; eauto.
        }
        {
          rewrite Hst''.
          eapply add_equiv; eauto.
          eapply add_remove_many_equiv; eauto.
          symmetry; eauto.
        }
      }
      {
        (* operational *)
        rename H3 into Hfw.
        rename H4 into Hspec.
        simpl in *.
        rewrite Hst'2 in Hfw.
        rewrite add_eq_o in Hfw by eauto.
        inject Hfw.
        rewrite Hspec in Hspec'; discriminate.
      }
    }
    {
      (* if-true *)
      inject Hcomp.
      eapply is_syntax_ok_if_elim in Hsyn.
      destruct Hsyn as [Hsyne [Hsyn1 Hsyn2]].
      inversion Hsf; subst; rename H5 into He; rename H6 into Hsfbr.
      - edestruct IHRunsTo as [s_st' [Hsst' Heq']]; eauto.
        exists s_st'; split.
        + eapply RunsToIfTrue; eauto.
        + eauto.
      - eapply is_false_equiv in He; eauto.
        exfalso; eapply is_true_is_false; eauto.
    }
    {
      (* if-false *)
      inject Hcomp.
      eapply is_syntax_ok_if_elim in Hsyn.
      destruct Hsyn as [Hsyne [Hsyn1 Hsyn2]].
      inversion Hsf; subst; rename H5 into He; rename H6 into Hsfbr.
      - eapply is_true_equiv in He; eauto.
        exfalso; eapply is_true_is_false; eauto.
      - edestruct IHRunsTo as [s_st' [Hsst' Heq']]; eauto.
        exists s_st'; split.
        + eapply RunsToIfFalse; eauto.
        + eauto.
    }
    {
      (* while-true *)
      inject Hcomp.
      copy_as Hsyn Hsyn'.
      eapply is_syntax_ok_while_elim in Hsyn.
      destruct Hsyn as [Hsyne Hsynb].
      inversion Hsf; unfold_all; subst.
      - edestruct IHRunsTo1 as [s_st' [Hsst' Heq']]; eauto.
        edestruct (IHRunsTo2 (While e s)) as [s_st'' [Hsst'' Heq'']]; try eapply Heq'; eauto.
        exists s_st''; split.
        + eapply RunsToWhileTrue; eauto.
        + eauto.
      - rename H5 into He.
        eapply is_false_equiv in He; eauto.
        exfalso; eapply is_true_is_false; eauto.
    }
    {
      (* while-false *)
      inject Hcomp.
      eapply is_syntax_ok_while_elim in Hsyn.
      destruct Hsyn as [Hsyne Hsynb].
      inversion Hsf; unfold_all; subst.
      - rename H2 into He.
        eapply is_true_equiv in He; eauto.
        exfalso; eapply is_true_is_false; eauto.
      - exists s_st; split.
        + eapply RunsToWhileFalse; eauto.
        + eauto.
    }
    {
      (* assign *)
      inject Hcomp.
      rename s into x.
      rename H into He.
      rename H0 into Hnadt.
      rename H1 into Hst'.
      eapply is_syntax_ok_assign_elim in Hsyn.
      destruct Hsyn as [Hsynx Hsyne].
      erewrite <- eval_equiv in He by eauto.
      erewrite <- not_mapsto_adt_equiv in Hnadt by eauto.
      exists (add x (SCA w) s_st); split.
      - eapply RunsToAssign; eauto.
      - rewrite Hst'.
        eapply add_equiv; eauto.
    }
  Qed.

End ADTValue.