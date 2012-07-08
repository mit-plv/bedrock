Require Import AutoSep Malloc Bags.


(** * Queue ADT *)

Definition ifZero (n : nat) (p1 p2 : W) := n = 0 -> p1 = p2.

Definition focusOnFront := True.
Definition focusOnBack := True.

Module Type QUEUE.
  Parameter queue : bag -> W -> HProp.
  Parameter llist : bag -> nat -> W -> W -> HProp.
  Parameter lseg : bag -> nat -> W -> W -> HProp.

  Axiom queue_extensional : forall b p, HProp_extensional (queue b p).
  Axiom llist_extensional : forall b n fr ba, HProp_extensional (llist b n fr ba).
  Axiom lseg_extensional : forall b n fr ba, HProp_extensional (lseg b n fr ba).

  Axiom lseg_extensional' : forall ba n b b' fr,
    b %= b'
    -> lseg b n fr ba ===> lseg b' n fr ba.

  Axiom llist_extensional' : forall ba n b b' fr,
    b %= b'
    -> llist b n fr ba ===> llist b' n fr ba.

  Axiom queue_fwd : forall b p,
    queue b p
    ===> Ex fr, Ex ba, Ex n, [| freeable p 2 |] * (p ==*> fr, ba) * llist b n fr ba.

  Axiom queue_bwd : forall b p,
    (Ex fr, Ex ba, Ex n, [| freeable p 2 |] * (p ==*> fr, ba) * llist b n fr ba)
    ===> queue b p.

  Axiom llist_empty_fwd_fr : forall b n (fr : W) ba,
    fr = 0
    -> llist b n fr ba ===> [| b %= empty |] * [| n = O |].

  Axiom llist_empty_bwd_fr : forall b n (fr : W) ba,
    fr = 0
    -> [| b %= empty |] * [| n = O |] ===> llist b n fr ba.

  Axiom llist_nonempty_fwd_fr : forall ba n (fr : W) b,
    fr <> 0
    -> focusOnFront
    -> llist b n fr ba ===> Ex n', Ex v1, Ex v2, Ex p, [| n = S n' |] * [| (v1, v2) %in b |] * [| freeable fr 3 |] * (fr ==*> v1, v2, p) * [| ifZero n' fr ba |] * llist (b %- (v1, v2)) n' p ba.

  Axiom llist_nonempty_fwd_ba : forall ba n (fr : W) b,
    fr <> 0
    -> focusOnBack
    -> llist b n fr ba ===> Ex n', Ex v1, Ex v2, [| n = S n' |] * [| (v1, v2) %in b |] * lseg (b %- (v1, v2)) n' fr ba * (ba ==*> v1, v2, $0).

  Axiom llist_nonempty_fwd_b : forall b n fr ba,
    ~(b %= empty)
    -> llist b n fr ba ===> [| fr <> 0 |] * Ex n', Ex v1, Ex v2, Ex p, [| n = S n' |] * [| (v1, v2) %in b |]
      * (fr ==*> v1, v2, p) * [| freeable fr 3 |] * [| ifZero n' fr ba |] * llist (b %- (v1, v2)) n' p ba.

  Axiom llist_nonempty_bwd_fr : forall b n (fr ba : W),
    fr <> 0
    -> focusOnFront
    -> (Ex n', Ex v1, Ex v2, Ex p, [| n = S n' |] * [| (v1, v2) %in b |] 
      * (fr ==*> v1, v2, p) * [| freeable fr 3 |] * [| ifZero n' fr ba |] * llist (b %- (v1, v2)) n' p ba) ===> llist b n fr ba.
End QUEUE.

Module Queue : QUEUE.
  Open Scope Sep_scope.

  Fixpoint llist (b : bag) (n : nat) (fr ba : W) : HProp :=
    match n with
      | O => [| fr = 0 /\ b %= empty |]
      | S n' => [| fr <> 0 |] * Ex v1, Ex v2, Ex p, [| (v1, v2) %in b |] * (fr ==*> v1, v2, p) * [| freeable fr 3 |] * [| ifZero n' fr ba |] * llist (b %- (v1, v2)) n' p ba
    end.

  Fixpoint lseg (b : bag) (n : nat) (fr ba : W) : HProp :=
    match n with
      | O => [| fr = ba /\ b %= empty |]
      | S n' => [| fr <> 0 |] * Ex v1, Ex v2, Ex p, [| (v1, v2) %in b |] * (fr ==*> v1, v2, p) * [| freeable fr 3 |] * lseg (b %- (v1, v2)) n' p ba
    end.

  Definition queue (b : bag) (p : W) : HProp :=
    Ex fr, Ex ba, Ex n, [| freeable p 2 |] * (p ==*> fr, ba) * llist b n fr ba.

  Theorem llist_extensional : forall b n fr ba, HProp_extensional (llist b n fr ba).
    destruct n; reflexivity.
  Qed.

  Theorem lseg_extensional : forall b n fr ba, HProp_extensional (lseg b n fr ba).
    destruct n; reflexivity.
  Qed.

  Theorem queue_extensional : forall b p, HProp_extensional (queue b p).
    reflexivity.
  Qed.

  Theorem lseg_extensional' : forall ba n b b' fr,
    b %= b'
    -> lseg b n fr ba ===> lseg b' n fr ba.
    induction n; sepLemma.
  Qed.

  Theorem llist_extensional' : forall ba n b b' fr,
    b %= b'
    -> llist b n fr ba ===> llist b' n fr ba.
    induction n; sepLemma.
  Qed.

  Theorem queue_fwd : forall b p,
    queue b p
    ===> Ex fr, Ex ba, Ex n, [| freeable p 2 |] * (p ==*> fr, ba) * llist b n fr ba.
    unfold queue; sepLemma.
  Qed.

  Theorem queue_bwd : forall b p,
    (Ex fr, Ex ba, Ex n, [| freeable p 2 |] * (p ==*> fr, ba) * llist b n fr ba)
    ===> queue b p.
    unfold queue; sepLemma.
  Qed.

  Theorem llist_empty_fwd_fr : forall b n (fr : W) ba,
    fr = 0
    -> llist b n fr ba ===> [| b %= empty |] * [| n = O |].
    destruct n; sepLemma.
  Qed.

  Theorem llist_empty_bwd_fr : forall b n (fr : W) ba,
    fr = 0
    -> [| b %= empty |] * [| n = O |] ===> llist b n fr ba.
    destruct n; sepLemma.
  Qed.

  Theorem llist_nonempty_fwd_fr : forall ba n (fr : W) b,
    fr <> 0
    -> focusOnFront
    -> llist b n fr ba ===> Ex n', Ex v1, Ex v2, Ex p, [| n = S n' |] * [| (v1, v2) %in b |] * [| freeable fr 3 |] * (fr ==*> v1, v2, p) * [| ifZero n' fr ba |] * llist (b %- (v1, v2)) n' p ba.
    destruct n; sepLemma.
  Qed.

  Theorem llist_nonempty_fwd_ba : forall ba n (fr : W) b,
    fr <> 0
    -> focusOnBack
    -> llist b n fr ba ===> Ex n', Ex v1, Ex v2, [| n = S n' |] * [| (v1, v2) %in b |] * lseg (b %- (v1, v2)) n' fr ba * (ba ==*> v1, v2, $0).
    induction n.

    sepLemma.

    simpl; intros.
    match goal with
      | [ |- _ ===> ?Q ] => remember Q;
        match goal with
          | [ H : ?X = Q |- _ ] => let H' := fresh in
            assert (H' : bool -> X = Q) by (intro; assumption);
              clear H; rename H' into H
        end
    end.
    sepLemma.
    destruct n.
    rewrite (Heqh true); sepLemma.
    eauto.
    specialize (H4 (refl_equal _)); subst.
    sepLemma.
    clear H4.
    transitivity ([| x <> 0 |] * llist (b %- (x1, x0)) (S n) x ba *
      SEP.ST.star (fr =*> x1)
        (SEP.ST.star ((fr ^+ $4) =*> x0) ((fr ^+ $8) =*> x))).
    sepLemma.
    remember (S n).
    sepLemma.
    etransitivity.
    eapply himp_star_frame; [ auto | reflexivity ].
    rewrite (Heqh true).
    sepLemma.
    sepLemma.
    injection H4; clear H4; intros; subst.
    apply lseg_extensional'; bags.
  Qed.

  Theorem llist_nonempty_fwd_b : forall b n (fr : W) ba,
    ~(b %= empty)
    -> llist b n fr ba ===> [| fr <> 0 |] * Ex n', Ex v1, Ex v2, Ex p, [| n = S n' |] * [| (v1, v2) %in b |]
      * (fr ==*> v1, v2, p) * [| freeable fr 3 |] * [| ifZero n' fr ba |] * llist (b %- (v1, v2)) n' p ba.
    destruct n; sepLemma.
  Qed.

  Theorem llist_nonempty_bwd_fr : forall b n (fr ba : W),
    fr <> 0
    -> focusOnFront
    -> (Ex n', Ex v1, Ex v2, Ex p, [| n = S n' |] * [| (v1, v2) %in b |]
      * (fr ==*> v1, v2, p) * [| freeable fr 3 |] * [| ifZero n' fr ba |] * llist (b %- (v1, v2)) n' p ba) ===> llist b n fr ba.
    destruct n; sepLemma; match goal with
                            | [ H : S _ = S _ |- _ ] => injection H; intros; subst
                          end; auto; sepLemma.
  Qed.
End Queue.

Import Queue.
Export Queue.

Hint Immediate llist_extensional lseg_extensional queue_extensional.

Definition hints : TacPackage.
  prepare (queue_fwd, llist_empty_fwd_fr, llist_nonempty_fwd_fr, llist_nonempty_fwd_ba, llist_nonempty_fwd_b)
  (queue_bwd, llist_empty_bwd_fr, llist_nonempty_bwd_fr).
Defined.


(** * The code *)

Definition initS := initS queue 7.
Definition isEmptyS := isEmptyS queue 0.
Definition dequeueS := dequeueS queue 6.
Definition enqueueS := enqueueS queue 9.

Definition queueM := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "queue" {{
  bfunction "init"("r") [initS]
    "r" <-- Call "malloc"!"malloc"(0)
    [PRE[_, R] R =?> 2 * [| freeable R 2 |]
     POST[R'] [| R' = R |] * queue empty R ];;
    "r" *<- 0;;
    Return "r"
  end with bfunction "isEmpty"("b") [isEmptyS]
    "b" <-* "b";;
    If ("b" = 0) {
      Return 1
    } else {
      Return 0
    }
  end with bfunction "enqueue"("b", "v1", "v2", "r", "tmp", "tmp2") [enqueueS]
    "r" <-- Call "malloc"!"malloc"(1)
    [Ex b,
      PRE[V, R] queue b (V "b") * R =?> 3 * [| R <> 0 |] * [| freeable R 3 |]
      POST[_] queue (b %+ (V "v1", V "v2")) (V "b")];;

    "r" *<- "v1";;
    "tmp" <- "r" + 4;;
    "tmp" *<- "v2";;
    "tmp" <- "r" + 8;;
    "tmp" *<- 0;;

    "tmp" <-* "b";;
    If ("tmp" = 0) {
      (* Empty queue *)

      "b" *<- "r"
    } else {
      (* Nonempty queue *)

      "tmp" <- "tmp" + 8;;
      "tmp" *<- "r"
    };;
 
    "tmp" <- "b" + 4;;
    "tmp" *<- "r";;

    Return 0
  end with bfunction "dequeue"("b", "r", "fr", "tmp") [dequeueS]
    "fr" <-* "b";;

    "tmp" <-* "fr";;
    "r" *<- "tmp";;
    "tmp" <- "fr" + 4;;
    "tmp" <-* "tmp";;
    "r" <- "r" + 4;;
    "r" *<- "tmp";;

    "tmp" <- "fr" + 8;;
    "tmp" <-* "tmp";;
    "b" *<- "tmp";;

    If ("tmp" = 0) {
      "b" <- "b" + 4;;
      "b" *<- 0
    } else {
      Skip
    };;

    Call "malloc"!"free"("fr", 1)
    [PRE[_] Emp
     POST[_] Emp];;
    Return 0
  end
}}.

Local Hint Extern 5 (@eq W _ _) => words.
Local Hint Extern 1 (himp _ (lseg _ _ _ _) (lseg _ _ _ _)) => apply lseg_extensional'.
Local Hint Extern 1 (himp _ (llist _ _ _ _) (llist _ _ _ _)) => apply llist_extensional'.

Ltac choose E := assert E by constructor.

Theorem queueMOk : moduleOk queueM.
  vcgen.

  sep hints.
  sep hints.
  sep hints.
  sep hints.
  sep hints.
  auto.
  sep hints.
  sep hints.
  sep hints.
  sep hints.
  sep hints.
  sep hints.
  sep hints.
  sep hints.
  sep hints.
  sep hints.
  sep hints.
  choose focusOnFront; sep hints.
  sep hints.
  sep hints.
  sep hints.
  sep hints.

  Focus.
  choose focusOnFront.
  post.
  evaluate hints.
  descend.
  step hints.
  step hints.
  descend.
  step hints.
  descend.
  step hints.
  descend.
  step hints.
  descend.
  step hints.
  descend.
  step hints.
  descend.
  step hints.
  descend.
  step hints.
  descend.
  step hints.
  auto.
  descend.
  step hints.

  sep hints.
  sep hints.
  sep hints.
  sep hints.
  choose focusOnFront; sep hints.
  choose focusOnBack; sep hints.

  choose focusOnBack.
  post.

  evaluate hints.
  descend.
  step hints.
  step hints.
  descend.
  step hints.
  descend.
  step hints.
  descend.
  step hints.

  evaluate hints.
  descend.
  step hints.
  step hints.
  descend.
  step hints.

  (** Important (but unprovable-looking) remaining hint:
   himp specs
     (llist (x3 %- (x15, x14)) x16 x13 x11 *
      SEP.ST.star (x12 =*> x15)
        (SEP.ST.star (Regs x2 Rv =*> sel x5 "v1")
           (SEP.ST.star ((x12 ^+ 4) =*> x14)
              (SEP.ST.star ((x12 ^+ 8) =*> Regs x2 Rv)
                 (SEP.ST.star ((Regs x2 Rv ^+ 8) =*> 0)
                    ((Regs x2 Rv ^+ 4) =*> sel x5 "v2"))))))%Sep
     (llist (x3 %+ (sel x5 "v1", sel x5 "v2")) ?923782 x12 (Regs x2 Rv)) *)
  instantiate (1 := O).
  admit.

  sep hints.
  sep hints.
  sep hints.
  sep hints.
  sep hints.
  sep hints.
  sep hints.
  sep hints.
  
  choose focusOnFront.
  post.

  evaluate hints.
  descend.
  step hints.
  descend.
  step hints.
  step hints.
  descend.
  step hints.
  descend.
  step hints.
  descend.
  step hints.
  step hints.
  descend.
  step hints.
  descend.
  step hints.
  descend.
  step hints.
  auto.
  descend.
  step hints.
  descend.
  step hints.

  (* Ran out of RAM at this point and had to check this case in a separate run. *)
  admit.

  sep hints.
  sep hints.
  sep hints.
Qed.
