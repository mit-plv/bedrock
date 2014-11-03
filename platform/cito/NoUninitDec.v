Set Implicit Arguments.

Require Import Syntax.

Require Import FreeVarsExpr.

Require Import Option.
Require Import String.
Local Open Scope string_scope.

Require Import List.
Import ListNotations.
Local Open Scope list_scope.

Module ListNotationsFix.
  Notation " [ ] " := (@nil _) : list_scope.
  Notation " [ x , .. , y ] " := (cons x .. (cons y nil) ..) : list_scope.
  Notation " +[ ] " := (@nil _) : list_scope.
  Notation " +[ x , .. , y ] " := (cons x .. (cons y nil) ..) : list_scope.
End ListNotationsFix.
Import ListNotationsFix.

Require Import StringSet.
Import StringSet.
Require Import StringSetFacts.
Import FSetNotations.
Import FSetNotationsTrial.
Local Open Scope fset_scope.

Coercion string2elt (x : string) : elt := x.
Coercion singleton : elt >-> t.

Fixpoint inits stmt : StringSet.t :=
  match stmt with
    | Assign x _ => x
    | Label x _ => x
    | Seq a b => inits a + inits b
    | Skip => []
    | Syntax.If _ t f => inits t * inits f
    | While _ _ => []
    | Syntax.Call x _ _ => default empty (option_map singleton x)
  end.

Fixpoint uninited_reads inited stmt :=
  match stmt with
    | Assign _ e => free_vars e - inited
    | Label _ _ => []
    | Seq a b => uninited_reads inited a + uninited_reads (inited + inits a) b
    | Skip => []
    | Syntax.If e t f => (free_vars e - inited) + uninited_reads inited t + uninited_reads inited f
    | While e s => (free_vars e - inited) + uninited_reads inited s
    | Syntax.Call _ f args => List.fold_left (fun acc e => free_vars e - inited + acc) args (free_vars f - inited)
  end.

Require Import FuncCore.

Local Open Scope bool_scope.

Definition is_no_uninited_reads (f : FuncCore) := is_empty (uninited_reads (of_list (ArgVars f)) (Body f)).

Definition is_no_uninited (f : FuncCore) := is_no_uninited_reads f && mem (RetVar f) (inits (Body f)).

Require Wf.
Require Import Bool.

Require Import GeneralTactics2.

Lemma inits_elim stmt : forall x, In x (inits stmt) -> Wf.writes stmt x.
Proof.
  induction stmt; simpl; intros x Hin.
  - eapply empty_iff in Hin; eauto.
  - eapply union_iff in Hin.
    destruct Hin as [Hin | Hin].
    + left; eauto.
    + right; eauto.
  - eapply inter_iff in Hin.
    destruct Hin as [Hin1 Hin2].
    eauto.
  - eapply empty_iff in Hin; eauto.
  - destruct o as [lhs|]; simpl in *.
    + eapply singleton_iff in Hin.
      eauto.
    + eapply empty_iff in Hin; eauto.
  - eapply singleton_iff in Hin.
    eauto.
  - eapply singleton_iff in Hin.
    eauto.
Qed.

Lemma uninited_reads_intro' stmt : forall x uninited inited, Wf.reads uninited stmt x -> (forall x, uninited x -> In x inited -> False) -> In x (uninited_reads inited stmt).
Proof.
  induction stmt; simpl; intros x uninited inited Hr Hdisj.
  - eapply empty_iff; eauto.
  - eapply union_iff.
    destruct Hr as [Hr1 | Hr2].
    + left.
      eauto.
    + right.
      eapply IHstmt2; eauto.
      intros x' Hu Hi.
      simpl in *.
      eapply union_iff in Hi.
      destruct Hu as [Hu Hnw].
      (*here*)
Qed.

Lemma uninited_reads_intro stmt : forall x inited, Wf.reads (fun x => ~ List.In x inited) stmt x -> In x (uninited_reads (of_list inited) stmt).

Lemma is_no_uninited_reads_sound f : is_no_uninited_reads f = true -> forall x, ~ Wf.reads (fun x => ~ List.In x (ArgVars f)) (Body f) x.
Proof.
  intros Hb x.
  unfold is_no_uninited_reads in *.
  nintro.
  eapply uninited_reads_intro in H.
  eapply is_empty_iff in Hb.
  contradict H.
  eauto.
Qed.

Lemma is_no_uninited_sound f : is_no_uninited f = true -> Wf.NoUninitialized (ArgVars f) (RetVar f) (Body f).
Proof.
  intros Hb.
  unfold is_no_uninited, Wf.NoUninitialized in *.
  eapply andb_true_iff in Hb.
  destruct Hb as [Hnur Hr].
  split.
  eapply is_no_uninited_reads_sound; eauto.
  eapply mem_iff in Hr.
  eapply inits_elim; eauto.
Qed.

