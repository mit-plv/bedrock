Require Import AutoSep.

Set Implicit Arguments.


(** The king of the abstract predicates *)

Module Type SINGLY_LINKED_LIST.
  Parameter sll : list W -> W -> HProp.

  Axiom sll_extensional : forall ls p, HProp_extensional (sll ls p).

  Axiom nil_fwd : forall ls (p : W), p = 0
    -> sll ls p ===> [| ls = nil |].

  Axiom nil_bwd : forall ls (p : W), p = 0
    -> [| ls = nil |] ===> sll ls p.

  Axiom cons_fwd : forall ls (p : W), p <> 0
    -> sll ls p ===> Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p'.

  Axiom cons_bwd : forall ls (p : W), p <> 0
    -> (Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p') ===> sll ls p.
End SINGLY_LINKED_LIST.

Module SinglyLinkedList : SINGLY_LINKED_LIST.
  Open Scope Sep_scope.

  Fixpoint sll (ls : list W) (p : W) : HProp :=
    match ls with
      | nil => [| p = 0 |]
      | x :: ls' => [| p <> 0 |] * Ex p', (p ==*> x, p') * sll ls' p'
    end.

  Theorem sll_extensional : forall ls (p : W), HProp_extensional (sll ls p).
    destruct ls; reflexivity.
  Qed.

  Theorem nil_fwd : forall ls (p : W), p = 0
    -> sll ls p ===> [| ls = nil |].
    destruct ls; sepLemma.
  Qed.

  Theorem nil_bwd : forall ls (p : W), p = 0
    -> [| ls = nil |] ===> sll ls p.
    destruct ls; sepLemma.
  Qed.

  Theorem cons_fwd : forall ls (p : W), p <> 0
    -> sll ls p ===> Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p'.
    destruct ls; sepLemma.
  Qed.

  Theorem cons_bwd : forall ls (p : W), p <> 0
    -> (Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p') ===> sll ls p.
    destruct ls; sepLemma;
      match goal with
        | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; intros; subst; reflexivity
      end.
  Qed.
End SinglyLinkedList.

Import SinglyLinkedList.
Hint Immediate sll_extensional.

Definition null A (ls : list A) : bool :=
  match ls with
    | nil => true
    | _ => false
  end.

Definition B2N (b : bool) : nat :=
  if b then 1 else 0.

Coercion B2N : bool >-> nat.

Definition nullS : assert := st ~> ExX, Ex ls, ![ ^[sll ls st#Rv] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = null ls |] /\ ![ ^[sll ls st#Rv] * #1 ] st').

Definition lengthS : assert := st ~> ExX, Ex ls, ![ ^[sll ls st#Rv] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = length ls |] /\ ![ ^[sll ls st#Rv] * #1 ] st').

Definition revS : assert := st ~> ExX, Ex a, Ex b, Ex ls, ![ (st#Sp ==*> a, b) * ^[sll ls st#Rv] * #0 ] st
  /\ st#Rp @@ (st' ~> Ex a', Ex b', ![ (st#Sp ==*> a', b') * ^[sll (rev ls) st'#Rv] * #1 ] st').

Definition sllM := bmodule "sll" {{
  bfunction "null" [nullS] {
    If (Rv = 0) {
      Return 1
    } else {
      Return 0
    }
  } with bfunction "length" [lengthS] {
    Sp <- 0;;
    [st ~> ExX, Ex ls, ![ ^[sll ls st#Rv] * #0 ] st
      /\ st#Rp @@ (st' ~> [| st'#Rv = st#Sp ^+ (length ls : W) |] /\ ![ ^[sll ls st#Rv] * #1 ] st')]
    While (Rv <> 0) {
      Sp <- Sp + 1;;
      Rv <- $[Rv + 4]
    };;
    Return Sp
  } with bfunction "rev" [revS] {
    $[Sp] <- 0;;
    [st ~> ExX, Ex p, Ex b, Ex ls, Ex acc, ![ (st#Sp ==*> p, b) * ^[sll ls st#Rv] * ^[sll acc p] * #0 ] st
      /\ st#Rp @@ (st' ~> Ex a, Ex b', Ex ls', [| ls' = rev_append ls acc |]
        /\ ![ (st#Sp ==*> a, b') * ^[sll ls' st'#Rv] * #1 ] st')]
    While (Rv <> 0) {
      $[Sp+4] <- $[Rv+4];;
      $[Rv + 4] <- $[Sp];;
      $[Sp] <- Rv;;
      Rv <- $[Sp+4]
    };;
    Return $[Sp]
  }
}}.

Definition hints_sll' : TacPackage.
  prepare1 (nil_fwd, cons_fwd) (nil_bwd, cons_bwd).
Defined.

Definition hints_sll : TacPackage.
  prepare2 hints_sll'.
Defined.

Lemma natToW_S : forall n, natToW (S n) = $1 ^+ natToW n.
  unfold natToW.
  intros.
  rewrite wplus_alt.
  unfold wplusN, wordBinN.
  simpl.
  rewrite roundTrip_1.
  destruct (wordToNat_natToWord 32 n); intuition.
  rewrite H0.
  replace (1 + (n - x * pow2 32)) with (1 + n - x * pow2 32) by omega.
  rewrite drop_sub; auto; omega.
Qed.

Ltac notConst x :=
  match x with
    | O => fail 1
    | S ?x' => notConst x'
    | _ => idtac
  end.

Ltac finish := repeat match goal with
                        | [ H : _ = _ |- _ ] => rewrite H
                      end; simpl;
               repeat match goal with
                        | [ |- context[natToW (S ?x)] ] =>
                          notConst x; rewrite (natToW_S x)
                      end; try rewrite <- rev_alt;
               congruence || W_eq || reflexivity || eauto.

Theorem sllMOk : moduleOk sllM.
  vcgen; try abstract (sep hints_sll; finish).

  (* This case needs manual work, because cancellation makes the wrong unification choices by default. *)

  evaluate hints_sll.
  descend.
  instantiate (2 := Regs x Rv).
  instantiate (4 := x6).
  repeat step hints_sll.
  repeat step hints_sll.
  repeat step hints_sll.
  finish.
(*Qed.*)
