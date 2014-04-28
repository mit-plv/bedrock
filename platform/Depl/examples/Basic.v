(** * Basic examples that define datatypes *)

Require Import Depl.


(** * The simplest example that defines (but does not use!) a datatype *)

Definition unused := dmodule "m" {{
  dtype "unit" = {{ #"tt"("dummy";) "this" = |^_, !tt| }}
  with dfunction "f" [
    ARGS()
    PRE Emp
    POST Emp
  ]
    Return 0
  end
}}.

Theorem unusedOk : moduleOk unused.
Proof.
  depl; auto.
Qed.


(** * Now, let's actually construct a value! *)

Definition unit := dmodule "m" {{
  dtype "unit" = {{ #"tt"("dummy";) "this" = |^_, !tt| }}
  with dfunction "f" [
    ARGS()
    PRE Emp
    POST #"unit"(|^_, !tt|, "result")
  ]
    Locals "ret" in
    "ret" <-- #"tt"(0);;
    Return "ret"
  end
}}.

Theorem unitOk : moduleOk unit.
Proof.
  depl; auto.
Qed.
