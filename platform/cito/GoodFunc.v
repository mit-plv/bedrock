Set Implicit Arguments.

Require Import Wf.
Export Wf.

Section TopSection.

  Require Import Notations.
  Local Open Scope stmt.
  Require Import SyntaxFunc.
  Require CompileStmtSpec.
  Require Import GetLocalVars.
  Require Import Depth.

  Definition GoodFunc f := 
    NoDup (ArgVars f) /\ 
    NoUninitialized (ArgVars f) (Body f) /\
    let s := Body f in 
    CompileStmtSpec.syn_req (ArgVars f ++ get_local_vars s (ArgVars f) (RetVar f)) (depth s) s.

  Require Import GetLocalVars.
  Lemma GoodFunc_NoDup_vars : forall f, GoodFunc f -> forall s r, NoDup (ArgVars f ++ get_local_vars s (ArgVars f) r).
    admit.
  Qed.

End TopSection.

Require Import ADT.

Module Make (Import E : ADT).

  Module Import WfMake := Wf.Make E.
  Require Import Semantics.
  Import SemanticsMake.

  Require Import GeneralTactics.

  Section TopSection.

    Lemma GoodFunc_Safe : forall f, GoodFunc f -> let s := Body f in forall fs vs h, Safe fs s (vs, h) -> forall vs', agree_in vs vs' (ArgVars f) -> Safe fs s (vs', h).
      intros.
      eapply NoUninitialized_Safe; eauto.
      destruct H; openhyp; eauto.
    Qed.

    Lemma GoodFunc_RunsTo : forall f, GoodFunc f -> let s := Body f in forall fs vs h v', RunsTo fs s (vs, h) v' -> forall vs', agree_in vs vs' (ArgVars f) -> RunsTo fs s (vs', h) v'.
      intros.
      eapply NoUninitialized_RunsTo; eauto.
      destruct H; openhyp; eauto.
    Qed.
    
  End TopSection.

End Make.
