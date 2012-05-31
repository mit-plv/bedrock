Require Import AutoSep.
Require Import Malloc.

Set Implicit Arguments.


Definition set := W -> Prop.

Definition mem (w : W) (s : set) := s w.
Infix "\in" := mem (at level 70, no associativity).

Definition propToWord (P : Prop) (b : W) :=
  IF P then b = 1 else b = 0.
Infix "\is" := (propToWord) (at level 71, no associativity).

Definition empty : set := fun _ => True.

Definition equiv (s1 s2 : set) := forall w, s1 w <-> s2 w.
Infix "%=" := equiv (at level 70, no associativity).

Definition add (s : set) (w : W) : set := fun w' => w' = w \/ s w'.
Infix "%+" := add (at level 50, left associativity).

Definition less (s : set) (w : W) : set := fun w' => w' < w /\ s w'.
Definition greater (s : set) (w : W) : set := fun w' => w' > w /\ s w'.
Infix "%<" := less (at level 40, left associativity).
Infix "%>" := greater (at level 40, left associativity).

Inductive tree :=
| Leaf
| Node : tree -> tree -> tree.

Module Type BST.
  Parameter bst' : set -> tree -> W -> HProp.
  Parameter bst : set -> W -> HProp.

  Axiom bst'_extensional : forall s t p, HProp_extensional (bst' s t p).
  Axiom bst_extensional : forall s p, HProp_extensional (bst s p).

  Axiom bst_fwd : forall s p, bst s p ===> Ex t, bst' s t p.
  Axiom bst_bwd : forall s p, Ex t, bst' s t p ===> bst s p.

  Axiom nil_bwd : forall s t (p : W), p = 0 -> [| s %= empty /\ t = Leaf |] ===> bst' s t p.
End BST.

Module Bst : BST.
  Open Scope Sep_scope.

  Fixpoint bst' (s : set) (t : tree) (p : W) : HProp :=
    match t with
      | Leaf => [| p = 0 /\ s %= empty |]
      | Node t1 t2 => [| p <> 0 |] * Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2)
        * bst' (s %< v) t1 p1
        * bst' (s %> v) t2 p2
        * [| v \in s |]
    end.

  Definition bst (s : set) (p : W) := Ex t, bst' s t p.

  Theorem bst'_extensional : forall s t p, HProp_extensional (bst' s t p).
    destruct t; reflexivity.
  Qed.

  Theorem bst_extensional : forall s p, HProp_extensional (bst s p).
    reflexivity.
  Qed.

  Theorem bst_fwd : forall s p, bst s p ===> Ex t, bst' s t p.
    unfold bst; sepLemma.
  Qed.

  Theorem bst_bwd : forall s p, Ex t, bst' s t p ===> bst s p.
    unfold bst; sepLemma.
  Qed.

  Theorem nil_bwd : forall s t (p : W), p = 0 -> [| s %= empty /\ t = Leaf |] ===> bst' s t p.
    destruct t; sepLemma.
  Qed.
End Bst.

Import Bst.
Export Bst.

Hint Immediate bst_extensional.

Definition hints' : TacPackage.
  prepare1 (bst_fwd) (bst_bwd, nil_bwd).
Defined.

Definition hints : TacPackage.
  prepare2 hints'.
Defined.

Definition initS : assert := st ~> ExX, ![ ^[mallocHeap] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp |] /\ ![ ^[bst empty st'#Rv] * ^[mallocHeap] * #1 ] st').

Definition bstM := bmodule "bst" {{
  bfunction "init" [initS] {
    Return 0
  }
}}.

Hint Extern 1 (_ %= _) => hnf; intuition.

Theorem bstMOk : moduleOk bstM.
  vcgen; sep hints.
Qed.
