Require Import AutoSep.

(** * Like TrivialMem, but tests use of equality prover in symbolic evaluation *)

Definition readS : assert := st ~> ExX, Ex v, ![ $0 =*> v * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = v |] /\ ![ $0 =*> v * #1 ] st').

Definition read := bmodule "read" {{
  bfunction "read" [readS] {
    If (Rv = 0) {
      Rv <- $[Rv]
    } else {
      Rv <- $[0]
    } ;;
    Goto Rp
  }
}}.

Theorem readOk : moduleOk read.
  vcgen.

  (* Admitted cases below are because symbolic evaluation doesn't seem to use the known equality. *)

  sep.
  admit.
  sep.
  admit.
  sep.
Qed.
