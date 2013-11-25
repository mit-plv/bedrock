Require Import Inv.

Set Implicit Arguments.

Require Import ReservedNames.

Require Import FreeVars.
Require Import Depth.
Require Import TempNames.
Require Import StringSet.
Require Import SetUtil.

Definition in_scope vars temp_vars s := 
  Subset (free_vars s) (to_set vars) /\
  Subset (make_temp_names (depth s)) (to_set temp_vars).

Require Import Syntax.

Section Spec.

  Variable layout : Layout.

  Variable vars temp_vars : list string.

  Variable s k : Stmt.

  Definition precond := inv layout vars temp_vars (Seq s k).

  Definition postcond := inv layout vars temp_vars k.

  Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

  Definition verifCond pre := imply pre precond :: in_scope vars temp_vars (Seq s k) :: nil.

End Spec.