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


(** * A first test of reasoning about return values *)

Definition const := dmodule "m" {{
  dfunction "f" [
    ARGS()
    PRE Emp
    POST |^fE, fE "result" = !(natToW 0)|
  ]
    Return 0
  end
}}.

Theorem constOk : moduleOk const.
Proof.
  depl.
Qed.


(** * Return value dependent on actual arguments *)

Definition ident := dmodule "m" {{
  dfunction "f" [
    ARGS("x")
    PRE Emp
    POST |^fE, fE "result" = fE "x0"|
  ]
    Return "x"
  end
}}.

Theorem identOk : moduleOk ident.
Proof.
  depl.
Qed.


(** * Return value dependent on actual arguments, with an intermediate variable *)

Definition identTmp := dmodule "m" {{
  dfunction "f" [
    ARGS("x")
    PRE Emp
    POST |^fE, fE "result" = fE "x0"|
  ]
    Locals "y" in
    "y" <- "x";;
    Return "y"
  end
}}.

Theorem identTmpOk : moduleOk identTmp.
Proof.
  depl.
Qed.


(** * Generalization of the above *)

Definition identTmp' := dmodule "m" {{
  dfunction "f" [
    ARGS("x")
    PRE Emp
    POST |^fE, fE "result" = fE "x0"|
  ]
    Locals "y", "z" in
    "y" <- "x";;
    "z" <- "y";;
    Return "z"
  end
}}.

Theorem identTmp'Ok : moduleOk identTmp'.
Proof.
  depl.
Qed.


(** * Some star+pure tests *)

Definition starPure1 := dmodule "m" {{
  dfunction "f" [
    ARGS("x", "y", "z")
    PRE |^fE, fE "x0" = fE "y0"| * |^fE, fE "y0" = fE "z0"|
    POST |^fE, fE "result" = fE "z0"| * |^fE, fE "z0" = fE "x0"|
  ]
    Return "y"
  end
}}.

Theorem starPure1Ok : moduleOk starPure1.
Proof.
  depl.
Qed.

Definition starPure2 := dmodule "m" {{
  dfunction "f" [
    ARGS("x", "y", "z")
    PRE (|^fE, fE "x0" = !(natToW 0)| * |^fE, fE "y0" = !(natToW 1)|) * |^fE, fE "z0" = !(natToW 2)|
    POST |^fE, fE "z0" = !(natToW 2)| * (|^fE, fE "y0" = !(natToW 1)| * |^fE, fE "x0" = !(natToW 0)|)
  ]
    Return 0
  end
}}.

Theorem starPure2Ok : moduleOk starPure2.
Proof.
  depl.
Qed.


(** * Use an assumption about spec variables to reason about return value. *)

Definition assumRet := dmodule "m" {{
  dfunction "f" [
    ARGS("x")
    AL "y",
    PRE |^fE, fE "x0" = fE "y"|
    POST |^fE, fE "result" = fE "y"|
  ]
    Return "x"
  end
}}.

Theorem assumRetOk : moduleOk assumRet.
Proof.
  depl.
Qed.
