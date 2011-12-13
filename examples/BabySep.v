Require Import Bedrock.

Set Implicit Arguments.


(** * Let's read from memory! *)

Definition readS : assert := st ~> ExX, ![ 0 ==> 0 * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = 0 |]).

Definition read := bmodule "read" {{
  bfunction "read" [readS] {
    Rv <- $[0];;
    Goto Rp
  }
}}.

Theorem readOk : moduleOk read.
  structured; autorewrite with sepFormula in *; simpl in *.

  inBounds_contra.

  ho.
  admit.
Qed.
