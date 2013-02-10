Require Import Bedrock PreAutoSep.


(** * Separation logic specifications for system calls *)

Definition abortS := SPEC reserving 0
  PREonly[_] Emp.


(** * More primitive operational semantics *)

Section OpSem.
  Variable stn : settings.
  Variable prog : program.

  Inductive sys_step : state' -> state' -> Prop :=
  | Normal : forall st st', step stn prog st = Some st'
    -> sys_step st st'
  | Abort : forall st, Labels stn ("sys", Global "abort") = Some (fst st)
    -> sys_step st st.

  Inductive sys_reachable : state' -> state' -> Prop :=
  | SR0 : forall st, sys_reachable st st
  | SR1 : forall st st' st'', sys_step st st'
    -> sys_reachable st' st''
    -> sys_reachable st st''.

  Definition sys_safe (st : state') :=
    forall st', sys_reachable st st' -> exists st'', sys_step st' st''.
End OpSem.
