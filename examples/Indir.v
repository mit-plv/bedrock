Require Import AutoSep.

(** Read from pointer in register *)

Definition indirS : assert := st ~> ExX, Ex v, ![ st#Sp =*> v * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = v |]).
Definition indir := bmodule "indir" {{
  bfunction "indir" [indirS] {
    Rv <- $[Sp];;
    Goto Rp
  }
}}.
Theorem indirOk : moduleOk indir.
  vcgen; try sep.
Abort.
