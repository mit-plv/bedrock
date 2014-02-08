(* Fixpoint doesn't have problem *)
Module Type Foo.
  Parameter t : Type.
  Parameter empty : t.
  Parameter inc : t -> t.
End Foo.

Module Make (F : Foo).
  Fixpoint t (n : nat) :=
    match n with
      | 0 => F.empty
      | S n' => F.inc (t n')
    end.
End Make.

Module Make1 (F : Foo).
  Module M := Make F.
  Definition t := M.t.
End Make1.

Module Make2 (F : Foo).
  Module M := Make F.
  Definition t := M.t.
End Make2.

Module Global (F : Foo).
  Module M1 := Make1 F.
  Module M2 := Make2 F.

  Lemma bar : M1.M.t = M2.M.t.
    reflexivity. (* fail here*)
  Qed.
End Global.



(* problem *)
Module Type Foo.
End Foo.

Module Make (F : Foo).
  Inductive t := .
  (* Definition t := nat. (* this one can work *)  *)
End Make.

Module Make1 (F : Foo).
  Module M := Make F.
  Definition t := M.t.
End Make1.

Module Make2 (F : Foo).
  Module M := Make F.
  Definition t := M.t.
End Make2.

Module Global (F : Foo).
  Module M1 := Make1 F.
  Module M2 := Make2 F.

  Lemma bar : M1.M.t = M2.M.t.
    reflexivity. (* fail here*)
  Qed.
End Global.



(* a solution *)
Module Type Foo.
End Foo.

Module Type MakeS (F : Foo).
  Parameter t : Type.
  (* Some axioms *)
End MakeS.

Module Make (F : Foo) <: MakeS F.
  Inductive t' := .
  Definition t := t'. (* rename because Coq currently doesn't accept inductive definition as an instantiation of a parameter *)
End Make.

Module Make1 (F : Foo) (M : MakeS F).
  Definition t := M.t.
End Make1.

Module Make2 (F : Foo) (M : MakeS F).
  Definition t := M.t.
End Make2.

Module Global (F : Foo).
  Module MM := Make F.
  Module M1 := Make1 F MM.
  Module M2 := Make2 F MM.

  Lemma bar : M1.t = M2.t.
    reflexivity. (* works! *)
  Qed.
End Global.