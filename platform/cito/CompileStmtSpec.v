Require Import Inv.
Require Import Syntax.

Set Implicit Arguments.

(* syntactic_requirement *)
Section SynReq.

  Variable vars : list string.

  Variable temp_size : nat.

  Variable s : Stmt.

  Require Import FreeVars.
  Require Import Depth.
  Require Import StringSet.
  Require Import SetUtil.

  Local Open Scope nat.

  Definition in_scope := 
    Subset (free_vars s) (to_set vars) /\
    depth s <= temp_size.

  Require Import WellFormed.

  Definition syn_req := in_scope /\ wellformed s.

End SynReq.

Module Make (Import M : RepInv.RepInv).

  Module Import InvMake := Inv.Make M.

  Section Spec.

    Variable vars : list string.

    Variable temp_size : nat.

    Variable s k : Stmt.

    Variable rv_postcond : W -> Semantics.State -> Prop.

    Definition precond := inv vars temp_size rv_postcond (Seq s k).

    Definition postcond := inv vars temp_size rv_postcond k.

    Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

    Definition verifCond pre := imply pre precond :: syn_req vars temp_size (Seq s k) :: nil.

  End Spec.

End Make.