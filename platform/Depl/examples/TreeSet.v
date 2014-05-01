(** * Simple trees representing finite sets *)

Require Import Depl.


Definition set := W -> Prop.
Definition empty : set := fun _ => False.
Definition mem (w : W) (s : set) : Prop := s w.
Definition add (s : set) (w : W) : set := fun w' => s w' \/ w' = w.
Definition union (s1 s2 : set) : set := fun w => s1 w \/ s2 w.
Definition equiv (s1 s2 : set) : Prop := forall w, s1 w <-> s2 w.

Ltac sets := unfold empty, mem, add, union, equiv; tauto.

Module D.
  Definition dom := set.
End D.

Module Import Depl := Depl.Make(D).

Definition dmem := worddynprop mem.
Infix "%in" := dmem (no associativity, at level 70).

Definition dadd := dynwordbin add.
Infix "%+" := dadd (left associativity, at level 50).

Definition dunion := dynbin union.
Infix "%U" := dunion (left associativity, at level 50).

Definition dequiv := dynprop equiv.
Infix "%=" := dequiv (no associativity, at level 70).

Ltac t :=
  unfold dynprop', dynwordbin'; intros;
  repeat match goal with
           | [ |- context[match ?A ?B with Word _ => _ | _ => _ end] ] =>
             destruct (A B); auto
         end; sets.


(** * Constructing the empty set *)

Definition empt := dmodule "m" {{
  dtype "tree" = {{ #"leaf"("dummy";) "this" == !empty
                    with #"node"("data";"left","right") "this" == "left" %U "right" %+ "data" }}
  with dfunction "f" [
    ARGS()
    PRE Emp
    POST #"tree"(!empty, "result")
  ]
    Locals "ret" in
    "ret" <-- #"leaf"(0);;
    Return "ret"
  end
}}.

Theorem emptOk : moduleOk empt.
Proof.
  depl.
Qed.


(** * Constructing a singleton set *)

Definition single := dmodule "m" {{
  dtype "tree" = {{ #"leaf"("dummy";) "this" == !empty
                    with #"node"("data";"left","right") "this" == "left" %U "right" %+ "data" }}
  with dfunction "f" [
    ARGS()
    PRE Emp
    POST EX "s", #"tree"("s", "result") * ("s" %= !empty %+ 42)
  ]
    Locals "ret", "left", "right" in
    "left" <-- #"leaf"(0);;
    "right" <-- #"leaf"(0);;
    "ret" <-- #"node"(42, "left", "right");;
    Return "ret"
  end
}}.

Theorem singleOk : moduleOk single.
Proof.
  depl; t.
Qed.


(** * Constructing a two-element set, with parameters *)

Definition double := dmodule "m" {{
  dtype "tree" = {{ #"leaf"("dummy";) "this" == !empty
                    with #"node"("data";"left","right") "this" == "left" %U "right" %+ "data" }}
  with dfunction "f" [
    ARGS("a", "b")
    PRE Emp
    POST EX "s", #"tree"("s", "result") * ("s" %= !empty %+ "a0" %+ "b0")
  ]
    Locals "ret", "left", "right" in
    "left" <-- #"leaf"(0);;
    "right" <-- #"leaf"(0);;
    "ret" <-- #"node"("a", "left", "right");;
    "left" <-- #"leaf"(0);;
    "ret" <-- #"node"("b", "left", "ret");;
    Return "ret"
  end
}}.

Theorem doubleOk : moduleOk double.
Proof.
  depl; t.
Qed.


(** * Adding an element to a set *)

Definition addit := dmodule "m" {{
  dtype "tree" = {{ #"leaf"("dummy";) "this" == !empty
                    with #"node"("data";"left","right") "this" == "left" %U "right" %+ "data" }}
  with dfunction "f" [
    AL "s",
    ARGS("x", "t")
    PRE #"tree"("s", "t0")
    POST EX "s'", #"tree"("s'", "result") * ("s'" %= "s" %+ "x0")
  ]
    Locals "ret", "left" in
    "left" <-- #"leaf"(0);;
    "ret" <-- #"node"("x", "left", "t");;
    Return "ret"
  end
}}.

Theorem additOk : moduleOk addit.
Proof.
  depl; t.
Qed.
