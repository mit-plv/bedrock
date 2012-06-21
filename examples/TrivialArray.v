Require Import AutoSep.

(** * A trivial example to make sure the array proof automation isn't completely borked *)

Definition readS : assert := st ~> ExX, Ex ls, [| $3 < natToW (length ls) |]%word
  /\ ![ ^[array ls st#Rv] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = selN ls 3 |] /\ ![ ^[array ls st#Rv] * #1 ] st').

Definition arrays := bmodule "read" {{
  bfunction "read" [readS] {
    Rv <- $[Rv + 12];;
    Goto Rp
  }
}}.

Theorem arraysOk : moduleOk arrays.
(*TIME  Clear Timing Profile. *)
  vcgen; abstract sep_auto.
(*TIME  Print Timing Profile. *)
Qed.
