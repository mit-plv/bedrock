Require Import AutoSep.

(** * A trivial example to make sure the local variable proof automation isn't completely borked *)

Notation "'myLocals'" := ("a" :: "b" :: nil).

Definition readS : assert := st ~> ExX, Ex vs, ![ ^[locals myLocals vs st#Sp] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = Locals.sel vs "a" |]
    /\ ![ ^[locals myLocals vs st#Sp] * #1 ] st').

Definition m := bmodule "read" {{
  bfunction "read" [readS] {
    Rv <- $[Sp + 0];;
    Goto Rp
  }
}}.

Theorem mOk : moduleOk m.
(*TIME  Clear Timing Profile. *)
  vcgen; abstract sep_auto.
 (*TIME  Print Timing Profile. *)
Qed.
