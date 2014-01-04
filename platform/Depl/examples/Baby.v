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


(** * Add an easy pure obligation. *)

Definition pure := dmodule "m" {{
  dfunction "f" [
    ARGS()
    PRE Emp
    POST |^_, (1 + 1 = 2)%nat|
  ]
    Return 0
  end
}}.

Theorem pureOk : moduleOk pure.
Proof.
  depl.
Qed.


(** * Use a contradictory assumption. *)

Definition contra := dmodule "m" {{
  dfunction "f" [
    ARGS()
    PRE |^_, False|
    POST |^_, (1 + 1 = 3)%nat|
  ]
    Return 0
  end
}}.

Theorem contraOk : moduleOk contra.
Proof.
  depl.
Qed.


(** * Use an assumption about spec variables. *)

Definition assum := dmodule "m" {{
  dfunction "f" [
    ARGS()
    AL "x", AL "y",
    PRE |^fE, fE "x" = fE "y"|
    POST |^fE, fE "y" = fE "x"|
  ]
    Return 0
  end
}}.

Theorem assumOk : moduleOk assum.
Proof.
  depl.
Qed.
