Require Import Thread.
Export Thread.


Module M.
  Definition globalInv : HProp := Emp%Sep.
End M.

Module T := Make(M).

Import T.
Export T.

Notation sched := tq.

Ltac sep hints := unfold M.globalInv in *; T.sep hints.
Ltac sep_auto := sep auto_ext.
