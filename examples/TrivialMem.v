Require Import AutoSep.

(** * A trivial example to make sure the separation logic proof automation isn't completely borked *)

Definition readS : assert := st ~> ExX, Ex v, ![ $0 =*> v * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = v |] /\ ![ $0 =*> v * #1 ] st').

Definition read := bmodule "read" {{
  bfunction "read" [readS] {
    Rv <- $[0];;
    If (Rv = 0) {
      $[0] <- 0
    } else {
      $[0] <- $[0]
    } ;;
    Rv <- $[0];;
    Goto Rp
  }
}}.

Theorem readOk : moduleOk read.
  Clear Timing Profile.
  vcgen ; abstract sep_auto.
  Print Timing Profile.
Qed.
