Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Bool.Bool.

Module BoolDT <: DecidableType.
  Definition U := bool.
  Definition eq_dec := bool_dec.
End BoolDT.

Module Import BoolDED := DecidableEqDep BoolDT.

Lemma bool_irre (a b : bool) (H1 H2 : a = b) : H1 = H2.
Proof.
  eapply UIP.
Qed.

Require Import Coq.Bool.Sumbool.

Definition boolcase := sumbool_of_bool.
