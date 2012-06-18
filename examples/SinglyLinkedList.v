Require Import AutoSep.
Require Import List.

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

Definition hints' : TacPackage.
<<<<<<< local
(*TIME idtac "sll:prepare1". Time *)
  prepare1 (nil_fwd, cons_fwd) (nil_bwd, cons_bwd).
(*TIME Time *)Defined.
=======
  (*TIME idtac "prepare1". Time *)prepare1 (nil_fwd, cons_fwd) (nil_bwd, cons_bwd).
Defined.
>>>>>>> other

Definition hints : TacPackage.
<<<<<<< local
(*TIME idtac "sll:prepare2". Time *)
  prepare2 hints'.
(*TIME Time *)Defined.
=======
  (*TIME idtac "prepare2". Time *)prepare2 hints'.
Defined.
>>>>>>> other

Definition null A (ls : list A) : bool :=
  match ls with
    | nil => true
    | _ => false
  end.

Definition nullS : assert := st ~> ExX, Ex ls, ![ ^[sll ls st#Rv] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = null ls |] /\ ![ ^[sll ls st#Rv] * #1 ] st').

Definition lengthS : assert := st ~> ExX, Ex ls, ![ ^[sll ls st#Rv] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = length ls |] /\ ![ ^[sll ls st#Rv] * #1 ] st').

Definition revS : assert := st ~> ExX, Ex a, Ex b, Ex ls, ![ (st#Sp ==*> a, b) * ^[sll ls st#Rv] * #0 ] st
  /\ st#Rp @@ (st' ~> Ex a', Ex b', ![ (st#Sp ==*> a', b') * ^[sll (rev ls) st'#Rv] * #1 ] st').

Definition appendS : assert := st ~> ExX, Ex p1, Ex p2, Ex c, Ex ls1, Ex ls2,
  ![ (st#Sp ==*> p1, p2, c) * ^[sll ls1 p1] * ^[sll ls2 p2] * #0 ] st
  /\ st#Rp @@ (st' ~> Ex a, Ex b, Ex c', ![ (st#Sp ==*> a, b, c') * ^[sll (ls1 ++ ls2) st'#Rv] * #1 ] st').

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
  } with bfunction "append" [appendS] {
    If ($[Sp] = 0) {
      Return $[Sp+4]
    } else {
      $[Sp+8] <- $[Sp];;
      Rv <- $[Sp] + 4;;
      [st ~> ExX, Ex p1, Ex p1', Ex p2, Ex r, Ex x, Ex ls1, Ex ls2, [| p1 <> $0 /\ st#Rv = p1 ^+ $4 |]
        /\ ![ (st#Sp ==*> p1, p2, r) * p1 =*> x * (p1 ^+ $4) =*> p1' * ^[sll ls1 p1']
          * ^[sll ls2 p2] * #0 ] st
        /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp /\ st'#Rv = r |]
          /\ Ex a, Ex b, Ex c', Ex ls, [| ls = x :: ls1 ++ ls2 |]
          /\ ![ (st'#Sp ==*> a, b, c') * ^[sll ls p1] * #1 ] st')]
      While ($[Rv] <> 0) {
        $[Sp] <- $[Rv];;
        Rv <- $[Sp] + 4
      };;

      $[Rv] <- $[Sp+4];;
      Return $[Sp+8]
    }
  }
}}.

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
               congruence || W_eq || reflexivity || tauto || eauto.

Theorem sllMOk : moduleOk sllM.
(*TIME Clear Timing Profile. *)
<<<<<<< local
(*TIME idtac "sll:verify". Time *) vcgen; abstract (sep hints; finish).
=======
  (*TIME idtac "verify". Time *)vcgen; abstract (sep hints; finish).
>>>>>>> other
(*TIME Print Timing Profile. *)
(*TIME Time *)Qed.
