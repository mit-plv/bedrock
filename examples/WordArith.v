Require Import AutoSep.

(** Testing prover support for word arithmetic *)

Definition test1S : assert := st ~> ExX, Ex a, Ex b, Ex c, [| st#Rv = st#Sp ^+ $4 |]
  /\ ![ ^[st#Sp ==*> a, b, c] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = c |] /\ ![ ^[st#Sp ==*> a, b, c] * #1 ] st').

Definition test1 := bmodule "test" {{
  bfunction "indir" [test1S] {
    Return $[Rv+4]
  }
}}.

Theorem test1Ok : moduleOk test1.
  vcgen; abstract sep_auto.
Qed.


Definition test2S : assert := st ~> ExX, Ex a, [| st#Rv = st#Sp ^+ $4 |]
  /\ ![ st#Sp =*> a * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = a |] /\ ![ st#Sp =*> a * #1 ] st').

Definition test2 := bmodule "test" {{
  bfunction "indir" [test2S] {
    Rv <- Rv - 4;;
    Return $[Rv]
  }
}}.

Theorem test2Ok : moduleOk test2.
  vcgen; abstract sep_auto.
Qed.


Definition test3S : assert := st ~> ExX, Ex a, [| st#Rv = st#Sp ^- $4 |]
  /\ ![ st#Sp =*> a * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = a |] /\ ![ st#Sp =*> a * #1 ] st').

Definition test3 := bmodule "test" {{
  bfunction "indir" [test3S] {
    Return $[Rv+4]
  }
}}.

Theorem test3Ok : moduleOk test3.
  vcgen; abstract sep_auto.
Qed.
