Require Import AutoSep.
Require Import Malloc.

Set Implicit Arguments.


Definition set := W -> Prop.

Definition mem (w : W) (s : set) := s w.
Infix "\in" := mem (at level 70, no associativity).

Definition empty : set := fun _ => False.

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

  Axiom bst_fwd : forall s p, bst s p ===> Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r.
  Axiom bst_bwd : forall s p, (Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r) ===> bst s p.

  Axiom nil_fwd : forall s t (p : W), p = 0 -> bst' s t p ===> [| s %= empty /\ t = Leaf |].
  Axiom nil_bwd : forall s t (p : W), p = 0 -> [| s %= empty /\ t = Leaf |] ===> bst' s t p.

  Axiom cons_fwd : forall s t (p : W), p <> 0 -> bst' s t p ===>
    Ex t1, Ex t2, Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2) * bst' (s %< v) t1 p1* bst' (s %> v) t2 p2
    * [| t = Node t1 t2 /\ v \in s |].

  Axiom cons_bwd : forall s t (p : W), p <> 0 ->
    (Ex t1, Ex t2, Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2) * bst' (s %< v) t1 p1* bst' (s %> v) t2 p2
    * [| t = Node t1 t2 /\ v \in s |]) ===> bst' s t p.
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

  Definition bst (s : set) (p : W) := Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r.

  Theorem bst'_extensional : forall s t p, HProp_extensional (bst' s t p).
    destruct t; reflexivity.
  Qed.

  Theorem bst_extensional : forall s p, HProp_extensional (bst s p).
    reflexivity.
  Qed.

  Theorem bst_fwd : forall s p, bst s p ===> Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r.
    unfold bst; sepLemma.
  Qed.

  Theorem bst_bwd : forall s p, (Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r) ===> bst s p.
    unfold bst; sepLemma.
  Qed.

  Theorem nil_fwd : forall s t (p : W), p = 0 -> bst' s t p ===> [| s %= empty /\ t = Leaf |].
    destruct t; sepLemma.
  Qed.

  Theorem nil_bwd : forall s t (p : W), p = 0 -> [| s %= empty /\ t = Leaf |] ===> bst' s t p.
    destruct t; sepLemma.
  Qed.

  Theorem cons_fwd : forall s t (p : W), p <> 0 -> bst' s t p ===>
    Ex t1, Ex t2, Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2) * bst' (s %< v) t1 p1* bst' (s %> v) t2 p2
    * [| t = Node t1 t2 /\ v \in s |].
    destruct t; sepLemma.
  Qed.

  Theorem cons_bwd : forall s t (p : W), p <> 0 ->
    (Ex t1, Ex t2, Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2) * bst' (s %< v) t1 p1* bst' (s %> v) t2 p2
    * [| t = Node t1 t2 /\ v \in s |]) ===> bst' s t p.
    destruct t; sepLemma;
      match goal with
        | [ H : Node _ _ = Node _ _ |- _ ] => injection H; sepLemma
      end.
  Qed.
End Bst.

Import Bst.
Export Bst.
Hint Immediate bst_extensional bst'_extensional.

Definition hints' : TacPackage.
  prepare1 (bst_fwd, nil_fwd, cons_fwd) (bst_bwd, nil_bwd, cons_bwd).
Defined.

Definition hints : TacPackage.
  prepare2 hints'.
Defined.

Definition initS : assert := st ~> ExX, ![ ^[st#Sp =?> 3] * ^[mallocHeap] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp |]
    /\ ![ ^[st#Sp =?> 3] * ^[bst empty st'#Rv] * ^[mallocHeap] * #1 ] st').

Definition lookupS : assert := st ~> ExX, Ex s, Ex p, Ex w,
  ![ (st#Sp ==*> p, w) * ^[bst s p] * ^[mallocHeap] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp /\ (w \in s) \is st'#Rv |]
    /\ ![ ^[st#Sp =?> 2] * ^[bst s p] * ^[mallocHeap] * #1 ] st').

Definition bstM := bimport [[ "malloc"!"malloc" @ [mallocS] ]]
  bmodule "bst" {{
  bfunction "init" [initS] {
    $[Sp] <- Rp;;
    $[Sp+4] <- 0;;
    Sp <- Sp + 4;;
    Call "malloc"!"malloc"
    [st ~> ExX, Ex rp, ![ (st#Sp ^- $4) =*> rp * ^[st#Sp =?> 2] * ^[st#Rv =?> 2] * ^[mallocHeap] * #0 ] st
      /\ rp @@ (st' ~> [| st'#Sp = st#Sp ^- $4 |]
        /\ Ex r, Ex junk, ![ ^[st'#Sp =?> 3] * (st'#Rv ==*> r, junk) * ^[bst' empty Leaf r]
          * ^[mallocHeap] * #1 ] st')];;
    Sp <- Sp - 4;;
    $[Rv] <- 0;;
    Rp <- $[Sp];;
    Return Rv
  } with bfunction "lookup" [lookupS] {
    Rv <- $[Sp];;
    $[Sp] <- $[Rv];;

    [st ~> ExX, Ex s, Ex t, Ex p, Ex w,
      ![ (st#Sp ==*> p, w) * ^[bst' s t p] * ^[mallocHeap] * #0 ] st
      /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp /\ (w \in s) \is st'#Rv |]
        /\ ![ ^[st#Sp =?> 2] * ^[bst' s t p] * ^[mallocHeap] * #1 ] st')]
    While ($[Sp] <> 0) {
      Rv <- $[Sp];;
      If ($[Rv+4] = $[Sp+4]) {
        (* Key matches! *)
        Return 1
      } else {
        Rv <- Rv;; (* This shouldn't be necessary, but symbolic evaluation misses some info otherwise. *)
        If ($[Sp+4] < $[Rv+4]) {
          (* Searching for a lower key *)
          $[Sp] <- $[Rv]
        } else {
          (* Searching for a higher key *)
          $[Sp] <- $[Rv+8]
        }
      }
    };;
    Return 0
  }
}}.

Ltac sets := unfold equiv, empty, mem, add, less, greater in *; firstorder.

Hint Extern 5 (_ %= _) => sets.
Hint Extern 5 (_ \in _) => sets.
Hint Extern 5 (~ _ \in _) => sets.
Hint Extern 5 (_ <-> _) => sets.

Lemma exhausted_cases : forall a b : W, a <> b
  -> ~(a < b)
  -> a > b.
  unfold wlt; intros.
  assert (wordToN a <> wordToN b) by (generalize wordToN_inj; firstorder).
  nomega.
Qed.

Local Hint Resolve exhausted_cases.

Theorem bstMOk : moduleOk bstM.
  vcgen.

  sep hints.

  sep hints.
  auto.
  replace (Regs st Sp ^+ $4) with (Regs x Sp ^+ $8) by words.
  step hints.
  descend.
  replace (Regs b Sp ^- $4) with (Regs x Sp) by words.
  step hints.
  words.
  replace (x7#Sp) with (Regs x Sp) by words.
  step hints.

  sep hints.

  sep hints.
  replace (Regs x Sp ^+ $4) with (Regs st Sp ^+ $8) by words.
  replace (Regs x Sp) with (Regs st Sp ^+ $4) by words.
  step hints.

  Ltac t := abstract (sep hints; auto).
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.

  (*vcgen; abstract (sep hints; auto).*)
Qed.
