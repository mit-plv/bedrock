Require Import Depl.


Module D.
  Definition dom := Empty_set.
End D.

Module Import Depl := Depl.Make(D).

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
  depl; auto.
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
  depl; auto.
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
  depl; tauto.
Qed.


(** * Use an assumption about spec variables. *)

Definition assum := dmodule "m" {{
  dfunction "f" [
    ARGS()
    AL "x", AL "y",
    PRE "x" = "y"
    POST "y" = "x"
  ]
    Return 0
  end
}}.

Theorem assumOk : moduleOk assum.
Proof.
  depl; auto.
Qed.


(** * A first test of reasoning about return values *)

Definition const := dmodule "m" {{
  dfunction "f" [
    ARGS()
    PRE Emp
    POST "result" = 0
  ]
    Return 0
  end
}}.

Theorem constOk : moduleOk const.
Proof.
  depl; auto.
Qed.


(** * Return value dependent on actual arguments *)

Definition ident := dmodule "m" {{
  dfunction "f" [
    ARGS("x")
    PRE Emp
    POST "result" = "x0"
  ]
    Return "x"
  end
}}.

Theorem identOk : moduleOk ident.
Proof.
  depl; auto.
Qed.


(** * Return value dependent on actual arguments, with an intermediate variable *)

Definition identTmp := dmodule "m" {{
  dfunction "f" [
    ARGS("x")
    PRE Emp
    POST "result" = "x0"
  ]
    Locals "y" in
    "y" <- "x";;
    Return "y"
  end
}}.

Theorem identTmpOk : moduleOk identTmp.
Proof.
  depl; auto.
Qed.


(** * Generalization of the above *)

Definition identTmp' := dmodule "m" {{
  dfunction "f" [
    ARGS("x")
    PRE Emp
    POST "result" = "x0"
  ]
    Locals "y", "z" in
    "y" <- "x";;
    "z" <- "y";;
    Return "z"
  end
}}.

Theorem identTmp'Ok : moduleOk identTmp'.
Proof.
  depl; auto.
Qed.


(** * Some star+pure tests *)

Definition starPure1 := dmodule "m" {{
  dfunction "f" [
    ARGS("x", "y", "z")
    PRE ("x0" = "y0") * ("y0" = "z0")
    POST ("result" = "z0") * ("z0" = "x0")
  ]
    Return "y"
  end
}}.

Theorem starPure1Ok : moduleOk starPure1.
Proof.
  depl; intuition.
Qed.

Definition starPure2 := dmodule "m" {{
  dfunction "f" [
    ARGS("x", "y", "z")
    PRE (("x0" = 0) * ("y0" = 1)) * ("z0" = 2)
    POST ("z0" = 2) * (("y0" = 1) * ("x0" = 0))
  ]
    Return 0
  end
}}.

Theorem starPure2Ok : moduleOk starPure2.
Proof.
  depl; tauto.
Qed.


(** * Use an assumption about spec variables to reason about return value. *)

Definition assumRet := dmodule "m" {{
  dfunction "f" [
    ARGS("x")
    AL "y",
    PRE "x0" = "y"
    POST "result" = "y"
  ]
    Return "x"
  end
}}.

Theorem assumRetOk : moduleOk assumRet.
Proof.
  depl; auto.
Qed.
