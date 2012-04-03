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
  vcgen; abstract (sep tt).
Qed.

Definition doubleIndirS : assert := st ~> ExX, Ex p, Ex v, ![ st#Sp =*> p * p =*> v * #0 ] st
  /\ st#Rp @@ (st' ~> [| st#Sp = st'#Sp /\ st'#Rv = v |] /\ ![ st'#Sp =*> p * p =*> v * #1 ] st').

Definition doubleIndir := bmodule "doubleIndir" {{
  bfunction "doubleIndir" [doubleIndirS] {
    Rv <- $[Sp];;
    Rv <- $[Rv];;
    Goto Rp
  }
}}.

Theorem doubleIndirOk : moduleOk doubleIndir.
  vcgen; abstract (sep tt).
Qed.
