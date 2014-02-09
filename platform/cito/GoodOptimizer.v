Set Implicit Arguments.

Require Import Syntax.
Require Import String.

Definition Optimizer := Stmt -> string -> Stmt.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import Semantics.
  Module Import SemanticsMake := Semantics.Make E.

  Definition PreserveSafe (opt : Optimizer) := forall fs s v, Safe fs s v -> forall ret, Safe fs (opt s ret) v.

  Definition PreserveRunsTo (opt : Optimizer) :=  forall ret fs s v v', RunsTo fs (opt s ret) v v' -> exists vs', RunsTo fs s v (vs', snd v') /\ Locals.sel vs' ret = Locals.sel (fst v') ret.

  Require Import GoodFunc.
  Require Import GetLocalVars.
  Require Import Depth.
  Require Import SyntaxFunc.
  Definition PreserveGoodSize (opt : Optimizer) :=
    forall f, 
      GoodFunc f -> 
      let s := opt (Body f) (RetVar f) in
      goodSize (length (get_local_vars s (ArgVars f) (RetVar f)) + depth s).

  Require Import Notations.
  Local Open Scope stmt.
  Require Import CompileStmtSpec.
  Definition PreserveSynReq (opt : Optimizer) :=
    forall f, 
      GoodFunc f -> 
      let s := opt (Body f) (RetVar f) in
      CompileStmtSpec.syn_req (ArgVars f ++ get_local_vars s (ArgVars f) (RetVar f)) (depth s) (s ;; skip).

  Definition GoodOptimizer opt := 
    PreserveSafe opt /\ 
    PreserveRunsTo opt /\
    PreserveGoodSize opt /\
    PreserveSynReq opt.

  Lemma GoodOptimizer_Safe : forall opt, GoodOptimizer opt -> PreserveSafe opt.
    unfold GoodOptimizer; intuition.
  Qed.

  Lemma GoodOptimizer_RunsTo : forall opt, GoodOptimizer opt -> PreserveRunsTo opt.
    unfold GoodOptimizer; intuition.
  Qed.

  Lemma GoodFunc_GoodOptimizer_goodSize : forall opt, GoodOptimizer opt -> PreserveGoodSize opt.
    unfold GoodOptimizer; intuition.
  Qed.

  Lemma GoodFunc_GoodOptimizer_syn_req : forall opt, GoodOptimizer opt -> PreserveSynReq opt.
    unfold GoodOptimizer; intuition.
  Qed.

End Make.



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