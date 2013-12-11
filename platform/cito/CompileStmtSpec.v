Require Import Inv.
Require Import Syntax.

Set Implicit Arguments.

Section Spec.

  Variable layout : Layout.

  Variable vars : list string.

  Variable temp_size : nat.

  Variable s k : Stmt.

  Definition precond := inv layout vars temp_size (Seq s k).

  Definition postcond := inv layout vars temp_size k.

  Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

  Require Import FreeVars.
  Require Import Depth.
  Require Import StringSet.
  Require Import SetUtil.

  Local Open Scope nat.

  Definition in_scope s := 
    Subset (free_vars s) (to_set vars) /\
    depth s <= temp_size.

  Require Import WellFormed.

  (* syntactic_requirement *)
  Definition syn_req s := in_scope s /\ wellformed s.

  Definition verifCond pre := imply pre precond :: syn_req (Seq s k) :: nil.

End Spec.