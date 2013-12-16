Set Implicit Arguments.

Require Import Semantics Safe.
Require Import Syntax.

Definition Optimizer := Stmt -> Stmt.

Definition GoodOptimizer : Optimizer -> Prop.
  admit.
Qed.

Lemma GoodOptimizer_Safe : forall opt, GoodOptimizer opt -> forall fs s v, Safe fs s v -> Safe fs (opt s) v.
  admit.
Qed.

Lemma GoodOptimizer_RunsTo : forall opt, GoodOptimizer opt -> forall fs s v v', RunsTo fs (opt s) v v' -> RunsTo fs s v v'.
  admit.
Qed.

Require Import GoodFunc.
Require Import GetLocalVars.
Require Import Depth.
Require Import SyntaxFunc.
Lemma GoodFunc_GoodOptimizer_goodSize : 
  forall f opt, 
    GoodFunc f -> 
    GoodOptimizer opt -> 
    let s := opt (Body f) in
    goodSize (length (get_local_vars s (ArgVars f) (RetVar f)) + depth s).
  admit.
Qed.

Require Import Notations.
Local Open Scope stmt.
Require Import CompileStmtSpec.
Lemma GoodFunc_GoodOptimizer_syn_req : 
  forall f, 
    GoodFunc f -> 
    forall opt, 
      GoodOptimizer opt -> 
      let s := opt (Body f) in
      CompileStmtSpec.syn_req (ArgVars f ++ get_local_vars s (ArgVars f) (RetVar f)) (depth s) (s ;; skip).
  admit.
Qed.





(*
Require Import Syntax Semantics.
Require Import CompileStatement.
Require Import GeneralTactics.

Set Implicit Arguments.

Definition is_good_optimizer optimizer :=
  (forall fs s v vs' heap', RunsTo fs (optimizer s) v (vs', heap') -> exists vs'', RunsTo fs s v (vs'', heap')) /\ 
  (forall fs s v, Safety.Safe fs s v -> Safety.Safe fs (optimizer s) v) /\
  (forall s, List.incl (SemanticsLemmas.footprint (optimizer s)) (SemanticsLemmas.footprint s)) /\
  (forall s, CompileStatement.depth (optimizer s) <= CompileStatement.depth s).

Definition compose A B C (g : B -> C) (f : A -> B) x := g (f x).

Lemma is_good_optimizer_trans : 
  forall a b,
    is_good_optimizer a ->
    is_good_optimizer b ->
    is_good_optimizer (compose a b).
Proof.
  unfold is_good_optimizer, compose; intros.

  openhyp.
  repeat split.
  intros.
  eapply H in H7; eauto; openhyp.
  eapply H0 in H7; eauto; openhyp.

  eauto.

  eauto.

  eauto using Le.le_trans.
Qed.
 *)