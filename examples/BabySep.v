Require Import Bedrock.

Set Implicit Arguments.


(** * Let's read from memory! *)

Definition readS : assert := st ~> ExX, Ex v, ![ 0 ==> v * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = v |] /\ ![ 0 ==> v * #1 ] st).

Definition read := bmodule "read" {{
  bfunction "read" [readS] {
    Rv <- $[0];;
    Goto Rp
  }
}}.

Theorem readOk : moduleOk read.
  structured; autorewrite with sepFormula in *; simpl in *.

  auto.

  ho.
  sepRead.
  reflexivity.
Qed.
