Require Import SyntaxExpr.
Require Import SetArrow.
Require Import Equalities String.

Set Implicit Arguments.

Module Key <: MiniDecidableType.
  Definition t := string.
  Definition eq_dec := string_dec.
End Key.

Module MSet := SetArrow Key.
Import MSet.

Fixpoint free_vars expr:=
  match expr with
    |Var s => singleton s
    |Const w => empty
    |Binop op a b => union (free_vars a) (free_vars b)
    |TestE te a b => union (free_vars a) (free_vars b)
  end.

