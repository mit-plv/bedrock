Require Import AutoSep.

(** * A trivial example to make sure the local variable proof automation isn't completely borked *)

Notation myLocals := ("a" :: "b" :: "c" :: nil).

Definition readS : assert := st ~> ExX, Ex vs, ![ ^[locals myLocals vs 7 st#Sp] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = Locals.sel vs "a" /\ st'#Sp = Locals.sel vs "b" |]
    /\ ![ ^[locals myLocals vs 7 st#Sp] * #1 ] st').

Definition writeS : assert := st ~> ExX, Ex vs, ![ ^[locals myLocals vs 7 st#Sp] * #0 ] st
  /\ st#Rp @@ (st' ~> Ex vs', [| Locals.sel vs' "a" = 3 /\ Locals.sel vs' "b" = 8 |]
    /\ ![ ^[locals myLocals vs' 7 st#Sp] * #1 ] st').

Definition readBackS : assert := st ~> ExX, Ex vs, ![ ^[locals myLocals vs 7 st#Sp] * #0 ] st
  /\ st#Rp @@ (st' ~> Ex vs', [| st'#Rv = 42 |]
    /\ ![ ^[locals myLocals vs' 7 st#Sp] * #1 ] st').

Definition m := bmodule "m" {{
  bfunction "read" [readS] {
    Rv <- $[Sp + 0];;
    Sp <- $[Sp + 4];;
    Goto Rp
  } with bfunction "write" [writeS] {
    $[Sp + 0] <- 3;;
    $[Sp + 4] <- 8;;
    Goto Rp
  } with bfunction "readBack" [readBackS] {
    $[Sp + 0] <- 12;;
    $[Sp + 4] <- 28;;
    $[Sp + 8] <- $[Sp + 0] + $[Sp + 4];;
    Rv <- $[Sp + 8] + 2;;
    Goto Rp
  }
}}.

Theorem mOk : moduleOk m.
(*TIME  Clear Timing Profile. *)
  vcgen; abstract (sep_auto; auto).
(*TIME  Print Timing Profile. *)
Qed.
