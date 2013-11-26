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

  Definition verifCond pre := imply pre precond :: in_scope (Seq s k) :: nil.

End Spec.