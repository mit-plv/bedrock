(** * Singly linked lists *)

Require Import Depl.


Module D.
  Definition dom := list W.
End D.

Module Import Depl := Depl.Make(D).

Definition dcons := worddynbin (@cons W).
Infix "!::" := dcons (right associativity, at level 60).


(** * Constructing a list *)

Definition empty := dmodule "m" {{
  dtype "list" = {{ #"nil"("dummy";) "this" == !nil
                    with #"cons"("hd";"tl") "this" == "hd" !:: "tl" }}
  with dfunction "f" [
    ARGS()
    PRE Emp
    POST #"list"(!nil, "result")
  ]
    Locals "ret" in
    "ret" <-- #"nil"(0);;
    Return "ret"
  end
}}.

Theorem emptyOk : moduleOk empty.
Proof.
  depl.
Qed.


(** * Constructing a one-element list *)

Definition one := dmodule "m" {{
  dtype "list" = {{ #"nil"("dummy";) "this" == !nil
                    with #"cons"("hd";"tl") "this" == "hd" !:: "tl" }}
  with dfunction "f" [
    ARGS()
    PRE Emp
    POST #"list"(!((42 : W) :: nil), "result")
  ]
    Locals "ret" in
    "ret" <-- #"nil"(0);;
    "ret" <-- #"cons"(42, "ret");;
    Return "ret"
  end
}}.

Theorem oneOk : moduleOk one.
Proof.
  depl.
Qed.


(** * Constructing a two-element list *)

Definition two := dmodule "m" {{
  dtype "list" = {{ #"nil"("dummy";) "this" == !nil
                    with #"cons"("hd";"tl") "this" == "hd" !:: "tl" }}
  with dfunction "f" [
    ARGS()
    PRE Emp
    POST #"list"(!((1 : W) :: (2 : W) :: nil), "result")
  ]
    Locals "ret" in
    "ret" <-- #"nil"(0);;
    "ret" <-- #"cons"(2, "ret");;
    "ret" <-- #"cons"(1, "ret");;
    Return "ret"
  end
}}.

Theorem twoOk : moduleOk two.
Proof.
  depl.
Qed.


(** * Constructing a two-element list with variable data *)

Definition twof := dmodule "m" {{
  dtype "list" = {{ #"nil"("dummy";) "this" == !nil
                    with #"cons"("hd";"tl") "this" == "hd" !:: "tl" }}
  with dfunction "f" [
    ARGS("a", "b")
    PRE Emp
    POST #"list"("a0" !:: "b0" !:: !nil, "result")
  ]
    Locals "ret" in
    "ret" <-- #"nil"(0);;
    "ret" <-- #"cons"("b", "ret");;
    "ret" <-- #"cons"("a", "ret");;
    Return "ret"
  end
}}.

Theorem twofOk : moduleOk twof.
Proof.
  depl.
Qed.
