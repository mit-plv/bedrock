Require Import AutoSep.
Require Import Malloc Sets.

Set Implicit Arguments.


Local Hint Extern 3 (himp _ _ _) => apply himp_star_frame.
Local Hint Extern 3 (himp _ _ _) => apply himp_star_frame_comm.

Inductive tree :=
| Leaf
| Node : tree -> tree -> tree.

Module Type BST.
  Parameter bst' : set -> tree -> W -> HProp.
  Parameter bst : set -> W -> HProp.

  Axiom bst'_extensional : forall s t p, HProp_extensional (bst' s t p).
  Axiom bst_extensional : forall s p, HProp_extensional (bst s p).

  Axiom bst'_set_extensional : forall t s s' p, s %= s' -> bst' s t p ===> bst' s' t p.

  Axiom bst_fwd : forall s p, bst s p ===> [| freeable p 2 |]
    * Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r.
  Axiom bst_bwd : forall s p, ([| freeable p 2 |]
    * Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r) ===> bst s p.

  Axiom nil_fwd : forall s t (p : W), p = 0 -> bst' s t p ===> [| s %= empty /\ t = Leaf |].
  Axiom nil_bwd : forall s t (p : W), p = 0 -> [| s %= empty /\ t = Leaf |] ===> bst' s t p.

  Axiom cons_fwd : forall s t (p : W), p <> 0 -> bst' s t p ===>
    Ex t1, Ex t2, Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2) * bst' (s %< v) t1 p1* bst' (s %> v) t2 p2
    * [| freeable p 3 /\ t = Node t1 t2 /\ v %in s |].

  Axiom cons_bwd : forall s t (p : W), p <> 0 ->
    (Ex t1, Ex t2, Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2) * bst' (s %< v) t1 p1* bst' (s %> v) t2 p2
      * [| freeable p 3 /\ t = Node t1 t2 /\ v %in s |]) ===> bst' s t p.
End BST.

Module Bst : BST.
  Open Scope Sep_scope.

  Fixpoint bst' (s : set) (t : tree) (p : W) : HProp :=
    match t with
      | Leaf => [| p = 0 /\ s %= empty |]
      | Node t1 t2 => [| p <> 0 /\ freeable p 3 |] * Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2)
        * bst' (s %< v) t1 p1
        * bst' (s %> v) t2 p2
        * [| v %in s |]
    end.

  Definition bst (s : set) (p : W) := [| freeable p 2 |]
    * Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r.

  Theorem bst'_extensional : forall s t p, HProp_extensional (bst' s t p).
    destruct t; reflexivity.
  Qed.

  Theorem bst_extensional : forall s p, HProp_extensional (bst s p).
    reflexivity.
  Qed.

  Theorem bst'_set_extensional : forall t s s' p, s %= s' -> bst' s t p ===> bst' s' t p.
    induction t; sepLemma.
  Qed.

  Theorem bst_fwd : forall s p, bst s p ===> [| freeable p 2 |]
    * Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r.
    unfold bst; sepLemma.
  Qed.

  Theorem bst_bwd : forall s p, ([| freeable p 2 |]
    * Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r) ===> bst s p.
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
    * [| freeable p 3 /\ t = Node t1 t2 /\ v %in s |].
    destruct t; sepLemma.
  Qed.

  Theorem cons_bwd : forall s t (p : W), p <> 0 ->
    (Ex t1, Ex t2, Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2) * bst' (s %< v) t1 p1* bst' (s %> v) t2 p2
    * [| freeable p 3 /\ t = Node t1 t2 /\ v %in s |]) ===> bst' s t p.
    destruct t; sepLemma;
      match goal with
        | [ H : Node _ _ = Node _ _ |- _ ] => injection H; sepLemma
      end.
  Qed.
End Bst.

Import Bst.
Export Bst.
Hint Immediate bst_extensional bst'_extensional.

(*TIME Clear Timing Profile. *)

Definition hints : TacPackage.
(*TIME idtac "tree-set:prepare1". Time *)
  prepare auto_ext tt tt  (bst_fwd, nil_fwd, cons_fwd) (bst_bwd, nil_bwd, cons_bwd).
(*TIME Time *)Defined.

Definition initS : assert := st ~> ExX, ![ ^[st#Sp =?> 3] * ^[mallocHeap] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp |]
    /\ ![ ^[st#Sp =?> 3] * ^[bst empty st'#Rv] * ^[mallocHeap] * #1 ] st').

Definition lookupS : assert := st ~> ExX, Ex s, Ex p, Ex w,
  ![ (st#Sp ==*> p, w) * ^[bst s p] * ^[mallocHeap] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp /\ (w %in s) \is st'#Rv |]
    /\ ![ ^[st#Sp =?> 2] * ^[bst s p] * ^[mallocHeap] * #1 ] st').

Definition addS : assert := st ~> ExX, Ex s, Ex p, Ex w,
  ![ (st#Sp ==*> p, w) * ^[(st#Sp ^+ $8) =?> 3] * ^[bst s p] * ^[mallocHeap] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp |]
    /\ ![ ^[st#Sp =?> 5] * ^[bst (s %+ w) p] * ^[mallocHeap] * #1 ] st').

Definition removeMinS : assert := st ~> ExX, Ex s, Ex t, Ex p, Ex p' : W, [| p' <> 0 |]
  /\ ![ st#Sp =*> p * ^[(st#Sp ^+ $4) =?> 3] * p =*> p' * ^[bst' s t p'] * ^[mallocHeap] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp /\ st'#Rv %in s /\ s %< st'#Rv %= empty |]
    /\ Ex t', Ex p'', ![ ^[st#Sp =?> 4] * p =*> p'' * ^[bst' (s %- st'#Rv) t' p''] * ^[mallocHeap] * #1 ] st').

Definition removeMaxS : assert := st ~> ExX, Ex s, Ex t, Ex p, Ex p' : W, [| p' <> 0 |]
  /\ ![ st#Sp =*> p * ^[(st#Sp ^+ $4) =?> 3] * p =*> p' * ^[bst' s t p'] * ^[mallocHeap] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp /\ st'#Rv %in s /\ s %> st'#Rv %= empty |]
    /\ Ex t', Ex p'', ![ ^[st#Sp =?> 4] * p =*> p'' * ^[bst' (s %- st'#Rv) t' p''] * ^[mallocHeap] * #1 ] st').

Definition removeS : assert := st ~> ExX, Ex s, Ex p, Ex w,
  ![ (st#Sp ==*> p, w) * ^[(st#Sp ^+ $8) =?> 4] * ^[bst s p] * ^[mallocHeap] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp |]
    /\ ![ ^[st#Sp =?> 6] * ^[bst (s %- w) p] * ^[mallocHeap] * #1 ] st').

Definition bstM := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "bst" {{
  bfunction "init" [initS] {
    $[Sp] <- Rp;;
    $[Sp+4] <- 0;;
    Sp <- Sp + 4;;
    Call "malloc"!"malloc"
    [st ~> ExX, Ex rp, [| freeable st#Rv 2 |]
      /\ ![ (st#Sp ^- $4) =*> rp * ^[st#Sp =?> 2] * ^[st#Rv =?> 2] * #0 ] st
      /\ rp @@ (st' ~> [| st'#Rv = st#Rv /\ st'#Sp = st#Sp ^- $4 |]
        /\ Ex r, Ex junk, ![ ^[st'#Sp =?> 3] * (st'#Rv ==*> r, junk) * ^[bst' empty Leaf r] * #1 ] st')];;
    Sp <- Sp - 4;;
    $[Rv] <- 0;;
    Rp <- $[Sp];;
    Return Rv
  } with bfunction "lookup" [lookupS] {
    Rv <- $[Sp];;
    $[Sp] <- $[Rv];;

    [st ~> ExX, Ex s, Ex t, Ex p, Ex w,
      ![ (st#Sp ==*> p, w) * ^[bst' s t p] * ^[mallocHeap] * #0 ] st
      /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp /\ (w %in s) \is st'#Rv |]
        /\ ![ ^[st#Sp =?> 2] * ^[bst' s t p] * ^[mallocHeap] * #1 ] st')]
    While ($[Sp] <> 0) {
      Rv <- $[Sp];;
      If ($[Rv+4] = $[Sp+4]) {
        (* Key matches! *)
        Return 1
      } else {
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
  } with bfunction "add" [addS] {
    $[Sp+8] <- Rp;;
    Rv <- $[Sp];;
    $[Sp+12] <- Rv;;
    $[Sp] <- $[Rv];;

    [st ~> ExX, Ex s, Ex t, Ex ans, Ex w, Ex rp, Ex p, Ex v,
      ![ (st#Sp ==*> p, w, rp, ans, v) * ans =*> p * ^[bst' s t p] * ^[mallocHeap] * #0 ] st
      /\ rp @@ (st' ~> [| st'#Sp = st#Sp |]
        /\ Ex t', Ex p', ![ ^[st#Sp =?> 5] * ans =*> p' * ^[bst' (s %+ w) t' p'] * ^[mallocHeap] * #1 ] st')]
    While ($[Sp] <> 0) {
      Rv <- $[Sp];;
      If ($[Rv+4] = $[Sp+4]) {
        (* Key matches!  No need for changes. *)
        Rp <- $[Sp+8];;
        Return 0
      } else {
        If ($[Sp+4] < $[Rv+4]) {
          (* Searching for a lower key *)
          Skip
        } else {
          (* Searching for a higher key *)
          Rv <- Rv + 8
        };;
        $[Sp+12] <- Rv;;
        $[Sp] <- $[Rv]
      }
    };;

    (* Found a spot for a new node.  Allocate and initialize it. *)

    $[Sp] <- $[Sp+12];;
    Sp <- Sp + 12;;
    $[Sp] <- 1;;
    Call "malloc"!"malloc"
    [st ~> ExX, Ex ans, Ex w, Ex rp, Ex v1, Ex v2, [| st#Rv <> 0 /\ freeable st#Rv 3 |]
      /\ ![ ((st#Sp ^- $12) ==*> ans, w, rp, v1, v2) * ans =*> 0 * ^[st#Rv =?> 3] * #0 ] st
      /\ rp @@ (st' ~> [| st'#Sp = st#Sp ^- $12 |]
        /\ ![ ^[st'#Sp =?> 5] * ans =*> st#Rv * (st#Rv ==*> $0, w, $0) * #1 ] st')];;
    Sp <- Sp - 12;;
    $[Rv] <- 0;;
    $[Rv+4] <- $[Sp+4];;
    $[Rv+8] <- 0;;
    Rp <- $[Sp];;
    $[Rp] <- Rv;;
    Rp <- $[Sp+8];;
    Return 0
  } with bfunction "removeMin" [removeMinS] {
    Rv <- $[Sp];;
    $[Sp+4] <- Rv;;
    $[Sp] <- $[Rv];; 

    [st ~> ExX, Ex s, Ex t, Ex p : W, Ex pointerHere, [| p <> 0 |]
      /\ ![ (st#Sp ==*> p, pointerHere) * ^[(st#Sp ^+ $8) =?> 2] * pointerHere =*> p
        * ^[bst' s t p] * ^[mallocHeap] * #0 ] st
      /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp /\ st'#Rv %in s /\ s %< st'#Rv %= empty |]
        /\ Ex t', Ex p', ![ ^[st#Sp =?> 4] * pointerHere =*> p'
          * ^[bst' (s %- st'#Rv) t' p'] * ^[mallocHeap] * #1 ] st')]
    While (1 = 1) {
      Rv <- $[Sp];;

      If ($[Rv] <> 0) {
        $[Sp+4] <- Rv;;
        $[Sp] <- $[Rv]
      } else {
        $[Sp+8] <- $[Rv+8];;
        Rv <- $[Sp+4];;
        $[Rv] <- $[Sp+8];;

        Rv <- $[Sp];;
        $[Sp] <- Rp;;
        $[Sp+4] <- $[Rv+4];;
        $[Sp+8] <- Rv;;
        $[Sp+12] <- 1;;
        Sp <- Sp + 8;;
        Call "malloc"!"free"
        [st ~> ExX, Ex rp, Ex rv, ![ ((st#Sp ^- $8) ==*> rp, rv) * #0 ] st
          /\ rp @@ (st' ~> [| st'#Sp = st#Sp ^- $8 /\ st'#Rv = rv |]
            /\ ![ ^[(st#Sp ^- $8) =?> 2] * #1 ] st')];;
        Sp <- Sp - 8;;
        Rp <- $[Sp];;
        Return $[Sp+4]
      }
    };;
    
    Fail (* Unreachable! *)
  } with bfunction "removeMax" [removeMaxS] {
    Rv <- $[Sp];;
    $[Sp+4] <- Rv;;
    $[Sp] <- $[Rv];; 

    [st ~> ExX, Ex s, Ex t, Ex p : W, Ex pointerHere, [| p <> 0 |]
      /\ ![ (st#Sp ==*> p, pointerHere) * ^[(st#Sp ^+ $8) =?> 2] * pointerHere =*> p
        * ^[bst' s t p] * ^[mallocHeap] * #0 ] st
      /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp /\ st'#Rv %in s /\ s %> st'#Rv %= empty |]
        /\ Ex t', Ex p', ![ ^[st#Sp =?> 4] * pointerHere =*> p'
          * ^[bst' (s %- st'#Rv) t' p'] * ^[mallocHeap] * #1 ] st')]
    While (1 = 1) {
      Rv <- $[Sp];;

      If ($[Rv+8] <> 0) {
        $[Sp+4] <- Rv+8;;
        $[Sp] <- $[Rv+8]
      } else {
        $[Sp+8] <- $[Rv];;
        Rv <- $[Sp+4];;
        $[Rv] <- $[Sp+8];;

        Rv <- $[Sp];;
        $[Sp] <- Rp;;
        $[Sp+4] <- $[Rv+4];;
        $[Sp+8] <- Rv;;
        $[Sp+12] <- 1;;
        Sp <- Sp + 8;;
        Call "malloc"!"free"
        [st ~> ExX, Ex rp, Ex rv, ![ ((st#Sp ^- $8) ==*> rp, rv) * #0 ] st
          /\ rp @@ (st' ~> [| st'#Sp = st#Sp ^- $8 /\ st'#Rv = rv |]
            /\ ![ ^[(st#Sp ^- $8) =?> 2] * #1 ] st')];;
        Sp <- Sp - 8;;
        Rp <- $[Sp];;
        Return $[Sp+4]
      }
    };;
    
    Fail (* Unreachable! *)
  } with bfunction "remove" [removeS] {
    Rv <- $[Sp];;
    $[Sp+8] <- Rv;;
    $[Sp] <- $[Rv];;

    [st ~> ExX, Ex s, Ex t, Ex ans, Ex w, Ex p,
      ![ (st#Sp ==*> p, w, ans) * ^[(st#Sp ^+ $12) =?> 3] * ans =*> p * ^[bst' s t p] * ^[mallocHeap] * #0 ] st
      /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp |]
        /\ Ex t', Ex p', ![ ^[st#Sp =?> 6] * ans =*> p' * ^[bst' (s %- w) t' p'] * ^[mallocHeap] * #1 ] st')]
    While ($[Sp] <> 0) {
      Rv <- $[Sp];;
      If ($[Rv+4] = $[Sp+4]) {
        (* Key matches!  Now the hard part: pulling another node's data value up here (if possible),
         * and then deleting this node. *)
        If ($[Rv] <> 0) {
          (* Nonempty left subtree.  Find and remove its rightmost node. *)
            $[Sp+8] <- Rv;;
            $[Sp] <- Rp;;
            $[Sp+4] <- Rv+4;;
            Sp <- Sp + 8;;
            Call "bst"!"removeMax"
            [st ~> ExX, Ex rp, Ex rv, ![((st#Sp ^- $8) ==*> rp, rv) * ^[st#Sp =?> 4] * ^[rv =?> 1] * #0] st
              /\ rp @@ (st' ~> [| st'#Sp = st#Sp ^- $8 |]
                /\ ![ ^[(st#Sp ^- $8) =?> 6] * rv =*> st#Rv * #1] st')];;

            Sp <- Sp - 8;;
            Rp <- $[Sp+4];;
            $[Rp] <- Rv;;
            Rp <- $[Sp];;
            Goto Rp
        } else {
          If ($[Rv+8] <> 0) {
            (* Nonempty right subtree.  Find and remove its leftmost node. *)
            $[Sp+8] <- Rv+8;;
            $[Sp] <- Rp;;
            $[Sp+4] <- Rv+4;;
            Sp <- Sp + 8;;
            Call "bst"!"removeMin"
            [st ~> ExX, Ex rp, Ex rv, ![((st#Sp ^- $8) ==*> rp, rv) * ^[st#Sp =?> 4] * ^[rv =?> 1] * #0] st
              /\ rp @@ (st' ~> [| st'#Sp = st#Sp ^- $8 |]
                /\ ![ ^[(st#Sp ^- $8) =?> 6] * rv =*> st#Rv * #1] st')];;

            Sp <- Sp - 8;;
            Rp <- $[Sp+4];;
            $[Rp] <- Rv;;
            Rp <- $[Sp];;
            Goto Rp
          } else {
            (* Both subtrees empty.  Easy case!  Can just delete this node. *)

            (* Zero out pointer to the node. *)
            Rv <- $[Sp+8];;
            $[Rv] <- 0;;

            (* Free the node. *)
            $[Sp+4] <- 1;;
            Goto "malloc"!"free"
          }
        }
      } else {
        If ($[Sp+4] < $[Rv+4]) {
          (* Searching for a lower key *)
          Skip
        } else {
          (* Searching for a higher key *)
          Rv <- Rv + 8
        };;
        $[Sp+8] <- Rv;;
        $[Sp] <- $[Rv]
      }
    };;

    (* Key not found!  So deletion is an easy no-op. *)
    Return 0
  }
}}.

Lemma exhausted_cases : forall a b : W, a <> b
  -> ~(a < b)
  -> a > b.
  intros.
  assert (wordToN a <> wordToN b) by (generalize wordToN_inj; firstorder).
  nomega.
Qed.

Local Hint Resolve exhausted_cases.
Local Hint Extern 5 (@eq W _ _) => words.
Local Hint Extern 3 (himp _ _ _) => apply bst'_set_extensional.

Theorem bstMOk : moduleOk bstM.
(*TIME idtac "tree-set:verify". Time *)
  vcgen; abstract (sep hints; auto).
(*TIME Time *)Qed.

(*TIME Print Timing Profile. *)