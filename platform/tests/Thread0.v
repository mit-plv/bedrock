Require Import Thread.
Export Thread.


Module M.
  Open Scope Sep_scope.

  Definition globalInv (_ : W) : hpropB ((settings * state : Type)%type :: nil) := ^[Emp].
End M.

Module T := Make(M).

Import T.
Export T.

Notation sched := tq.

Ltac sep := T.sep ltac:(unfold M.globalInv in *).
Ltac sep_auto := sep auto_ext.
