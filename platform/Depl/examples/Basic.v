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
  depl.
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
  depl.
Qed.


(** * Lists with a degenerate specification *)

Definition list := dmodule "m" {{
  dtype "list" = {{ #"nil"("dummy";) "this" = |^_, !tt|
                    with #"cons"("hd";"tl") "this" = |^_, !tt| }}
  with dfunction "f" [
    ARGS()
    PRE Emp
    POST #"list"(|^_, !tt|, "result")
  ]
    Locals "ret" in
    "ret" <-- #"nil"(0);;
    "ret" <-- #"cons"(42, "ret");;
    "ret" <-- #"cons"(23, "ret");;
    Return "ret"
  end
}}.

Theorem listOk : moduleOk list.
Proof.
  depl.
Qed.


(** * Binary trees with a degenerate specification *)

Definition tree := dmodule "m" {{
  dtype "tree" = {{ #"leaf"("dummy";) "this" = |^_, !tt|
                    with #"node"("data";"left","right") "this" = |^_, !tt| }}
  with dfunction "f" [
    ARGS()
    PRE Emp
    POST #"tree"(|^_, !tt|, "result")
  ]
    Locals "left", "right", "ret" in
    "left" <-- #"leaf"(0);;
    "right" <-- #"leaf"(0);;
    "ret" <-- #"node"(42, "left", "right");;
    Return "ret"
  end
}}.

Theorem treeOk : moduleOk tree.
Proof.
  depl.
Qed.
