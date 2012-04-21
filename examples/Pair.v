Require Import AutoSep.

(** A very basic abstract predicate: pairs of words *)

Module Type PAIR.
  Parameter pair : W -> W -> W -> HProp.

  Axiom pair_extensional : forall a b p, HProp_extensional (pair a b p).

  Axiom pair_fwd : forall a b p,
    pair a b p ===> p =*> a * (p ^+ $4) =*> b.

  Axiom pair_bwd : forall a b p,
    p =*> a * (p ^+ $4) =*> b ===> pair a b p.
End PAIR.

Module Pair : PAIR.
  Open Scope Sep_scope.

  Definition pair (a b p : W) : HProp :=
    p =*> a * (p ^+ $4) =*> b.

  Theorem pair_extensional : forall a b p, HProp_extensional (pair a b p).
    reflexivity.
  Qed.

  Theorem pair_fwd : forall a b p,
    pair a b p ===> p =*> a * (p ^+ $4) =*> b.
    sepLemma. 
  Qed.

  Theorem pair_bwd : forall a b p,
    p =*> a * (p ^+ $4) =*> b ===> pair a b p.
    sepLemma.
  Qed.
End Pair.

Import Pair.
Hint Immediate pair_extensional.

Definition firstS : assert := st ~> ExX, Ex a, Ex b, ![ ^[pair a b st#Rv] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = a |] /\ ![ ^[pair a b st#Rv] * #1 ] st').

Definition pair := bmodule "pair" {{
  bfunction "first" [firstS] {
    Return $[Rv]
  }
}}.

Definition hints_pair' : TacPackage.
  prepare1 pair_fwd pair_bwd.
Defined.

Definition hints_pair : TacPackage.
  prepare2 hints_pair'.
Defined.

Theorem pairOk : moduleOk pair.
  vcgen; abstract (sep hints_pair).
Qed.
