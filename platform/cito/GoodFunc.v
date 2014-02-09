Set Implicit Arguments.

Section TopSection.

  Require Import Notations.
  Local Open Scope stmt.
  Require Import SyntaxFunc.

  Definition WellFormed : Stmt -> Prop.
    admit.
  Qed.

  Definition GoodFunc f := 
    NoDup (ArgVars f) /\ 
    WellFormed (Body f).

  Require Import GetLocalVars.
  Lemma GoodFunc_NoDup_vars : forall f, GoodFunc f -> forall s r, NoDup (ArgVars f ++ get_local_vars s (ArgVars f) r).
    admit.
  Qed.

  Definition agree_in vs vs' vars := List.Forall (fun x => sel vs x = sel vs' x) vars.

  Lemma agree_in_merge : forall vs vs' vars, agree_in vs (merge vs vs' vars) vars.
    admit.
  Qed.

  Lemma agree_in_comm : forall vs vs' vars, agree_in vs vs' vars -> agree_in vs' vs vars.
    admit.
  Qed.

End TopSection.

Require Import ADT.

Module Make (Import E : ADT).

  Module Import SafeMake := Safe.Make E.
  Import SafeMake.SemanticsMake.

  Section TopSection.

    Lemma GoodFunc_Safe : forall f, GoodFunc f -> let s := Body f in forall fs vs h, Safe fs s (vs, h) -> forall vs', agree_in vs vs' (ArgVars f) -> Safe fs s (vs', h).
      admit.
    Qed.

    Lemma GoodFunc_RunsTo : forall f, GoodFunc f -> let s := Body f in forall fs vs h v', RunsTo fs s (vs, h) v' -> forall vs', agree_in vs vs' (ArgVars f) -> RunsTo fs s (vs', h) v'.
      admit.
    Qed.
    
  End TopSection.

End Make.
