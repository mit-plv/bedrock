Require Import AutoSep.

(** Swapping two pointers *)

(* "Uh, argument conventions" *)

Definition swapS : assert := st ~> ExX, Ex v, Ex v', ![ st#Sp =*> v * (st#Sp ^+ $4) =*> v' * #0 ] st
  /\ st#Rp @@ (st' ~> [| st#Sp = st'#Sp |] /\ ![ st#Sp =*> v' * (st#Sp ^+ $4) =*> v * #1 ] st').

Definition swap := bmodule "swap" {{
  bfunction "swap" [swapS] {
    Rv <- $[Sp + $4];;
    $[Sp + $4] <- $[Sp];;
    $[Sp] <- Rv;;
    Goto Rp
  }
}}.

Theorem swapOk : moduleOk swap.
  vcgen; sep.
Qed.
