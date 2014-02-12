Set Implicit Arguments.

Require Import List.

Section TopSection.

  Variable A B : Type.

  Implicit Types ls : list A.
  Implicit Types f : A -> B.
  Implicit Types x y e a : A.
  
  Fixpoint flatten (ls : list (list A)) :=
    match ls with
      | nil => nil
      | x :: xs => x ++ flatten xs
    end.

  Lemma In_flatten : forall lsls x, In x (flatten lsls) -> exists ls, In x ls /\ In ls lsls.
    admit.
  Qed.

  Lemma In_flatten_intro : forall lsls ls e, In e ls -> In ls lsls -> In e (flatten lsls).
    admit.
  Qed.

  Lemma incl_map : forall f ls1 ls2, incl ls1 ls2 -> incl (map f ls1) (map f ls2).
    admit.
  Qed.

  Definition Disjoint A (ls1 ls2 : list A) := forall e : A, ~ (In e ls1 /\ In e ls2).

  Lemma NoDup_app : forall ls1 ls2, NoDup ls1 -> NoDup ls2 -> Disjoint ls1 ls2 -> NoDup (ls1 ++ ls2).
    admit.
  Qed.

  Lemma Disjoint_map : forall f ls1 ls2, Disjoint (map f ls1) (map f ls2) -> Disjoint ls1 ls2.
    admit.
  Qed.

  Lemma Disjoint_incl : forall ls1 ls2 ls1' ls2', Disjoint ls1 ls2 -> incl ls1' ls1 -> incl ls2' ls2 -> Disjoint ls1' ls2'.
    admit.
  Qed.

  Lemma Disjoint_symm : forall ls1 ls2, Disjoint ls1 ls2 -> Disjoint ls2 ls1.
    admit.
  Qed.

  Definition IsInjection f := forall x y, x <> y -> f x <> f y.

  Lemma Injection_NoDup : forall f ls, IsInjection f -> NoDup ls -> NoDup (map f ls).
    admit.
  Qed.

  Lemma NoDup_incl_2 : forall ls1 ls2, NoDup ls2 -> incl ls1 ls2 -> NoDup ls1.
    admit.
  Qed.

End TopSection.
