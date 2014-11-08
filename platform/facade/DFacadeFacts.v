Set Implicit Arguments.

Require Import FacadeFacts.
Export FacadeFacts.
Require Import Facade.
Require Import DFacade.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Option.

  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation Value := (@Value ADTValue).
  Notation Sca := (@SCA ADTValue).

  Lemma safe_if_true : forall (env : Env) e t f st, Safe env (If e t f) st -> is_true st e -> Safe env t st.
  Proof.
    intros.
    inversion H; subst.
    eauto.
    exfalso; eapply is_true_is_false; eauto.
  Qed.

  Lemma safe_if_is_bool : forall (env : Env) e t f st, Safe env (If e t f) st -> is_bool st e.
  Proof.
    intros.
    inversion H; subst.
    eapply is_true_is_bool; eauto.
    eapply is_false_is_bool; eauto.
  Qed.

  Lemma safe_if_false : forall (env : Env) e t f st, Safe env (If e t f) st -> is_false st e -> Safe env f st.
  Proof.
    intros.
    inversion H; subst.
    exfalso; eapply is_true_is_false; eauto.
    eauto.
  Qed.

  Require Import SyntaxExpr.

  (* test boolean deciders *)
  Open Scope string_scope.
  Require Import List.
  Import ListNotations.
  Goal assigned (Seq (Assign "x" (Var "a")) (Assign "y" (Var "b"))) = ["x"; "y"]. Proof. exact eq_refl. Qed.

  Import StringSetFacts.
  Import StringSet.

  Require Import String.
  Require Import List.
  Require Import StringMap.
  Import StringMap.
  Require Import StringMapFacts.
  Require Import ListFacts4.
  Require Import GeneralTactics.
  Require Import GeneralTactics2.
  Require Import GeneralTactics4.
  
  Require Import ListFacts3.

  Lemma NoDup_ArgVars : forall spec, NoDup (ArgVars spec).
    intros; destruct spec; simpl; eapply is_no_dup_sound; eauto.
  Qed.

  Lemma not_incl_spec : forall spec, ~ List.In (RetVar spec) (ArgVars spec).
    intros; destruct spec; simpl; eapply negb_is_in_iff; eauto.
  Qed.

  Lemma in_args_not_assigned spec x : List.In x (ArgVars spec) -> ~ List.In x (assigned (Body spec)).
  Proof.
    destruct spec; simpl in *; nintro; eapply is_disjoint_sound; eauto.
  Qed.

  Lemma safe_seq_1 : forall (env : Env) a b st, Safe env (Seq a b) st -> Safe env a st.
  Proof.
    intros.
    inversion H; subst.
    openhyp.
    eauto.
  Qed.

  Lemma safe_seq_2 : forall (env : Env) a b st, Safe env (Seq a b) st -> forall st', RunsTo env a st st' -> Safe env b st'.
  Proof.
    intros.
    inversion H; subst.
    openhyp.
    eauto.
  Qed.

  Require Import GeneralTactics3.

  Lemma safe_while_is_bool (env : Env) e s st : Safe env (While e s) st -> is_bool st e.
  Proof.
    intros H.
    inversion H; unfold_all; subst.
    eapply is_true_is_bool; eauto.
    eapply is_false_is_bool; eauto.
  Qed.

End ADTValue.  
