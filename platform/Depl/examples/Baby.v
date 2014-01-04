Require Import Depl.


(** * The simplest function possible *)

Definition nada := dmodule "m" {{
  dfunction "f" [
    ARGS()
    PRE Emp
    POST Emp
  ]
    Return 0
  end
}}.

Theorem nadaOk : moduleOk nada.
Proof.
  depl.
Qed.
