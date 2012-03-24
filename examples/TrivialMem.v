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
      $[0] <- 0
    } ;;
    Rv <- $[0];;
    Goto Rp
  }
}}.

Theorem readOk : moduleOk read.
  vcgen. 
  Focus 7.
  sep.
  Print Ltac SEP.reflect_sexpr.
  sep_canceler ltac:(isConst) (@Provers.transitivityEqProverRec) the_cancel_simplifier tt.
  Print Ltac sep_canceler.
  chan
  sep_canceler.
  Print Ltac ho.
  ho.

  sep.
  
Qed.
