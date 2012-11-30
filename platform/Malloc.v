Require Import AutoSep Util.
Require Import Arith List.

Set Implicit Arguments.

Local Hint Extern 1 (himp _ (allocated _ _ _) (allocated _ _ _)) => apply allocated_shift_base.


(** * A free-list heap managed by the malloc library *)

Definition noWrapAround (p : W) (sz : nat) :=
  forall n, (n < 4 * sz)%nat -> p ^+ $(n) <> $0.

Record freeable (p : W) (sz : nat) : Prop := {
  BigEnough : (sz >= 2)%nat;
  SmallEnough : noWrapAround p sz
}.

Hint Immediate BigEnough SmallEnough.
Hint Constructors freeable.

Module Type FREE_LIST.
  Parameter freeList : nat (* number of elements in list *) -> W -> HProp.
  Parameter mallocHeap : W -> HProp.

  Axiom freeList_extensional : forall n p, HProp_extensional (freeList n p).
  Axiom mallocHeap_extensional : forall p, HProp_extensional (mallocHeap p).

  Axiom mallocHeap_fwd : forall p, mallocHeap p ===> Ex n, Ex p', p =*> p' * freeList n p'.
  Axiom mallocHeap_bwd : forall p, (Ex n, Ex p', p =*> p' * freeList n p') ===> mallocHeap p.

  Axiom nil_bwd : forall n p, p = 0 -> [| n = 0 |] ===> freeList n p.
  Axiom cons_bwd : forall n (p : W), p <> 0
    -> (Ex n', Ex sz, Ex p', [| n = S n' |]
      * [| noWrapAround p (2 + wordToNat sz) |]
      * (p ==*> sz, p') * (p ^+ $8) =?> wordToNat sz * freeList n' p')
    ===> freeList n p.

  Axiom cons_fwd : forall n (p : W), p <> 0
    -> freeList n p
    ===> Ex n', Ex sz, Ex p', [| n = S n' |]
    * [| noWrapAround p (2 + wordToNat sz) |]
    * (p ==*> sz, p')  * (p ^+ $8) =?> wordToNat sz * freeList n' p'.
End FREE_LIST.

Module FreeList : FREE_LIST.
  Open Scope Sep_scope.

  Fixpoint freeList (n : nat) (p : W) : HProp :=
    match n with
      | O => [| p = 0 |]
      | S n' => [| p <> 0 |] * Ex sz, Ex p',
        [| noWrapAround p (2 + wordToNat sz) |]
        * (p ==*> sz, p') * (p ^+ $8) =?> wordToNat sz * freeList n' p'
    end.

  Definition mallocHeap (p : W) := Ex n, Ex p', p =*> p' * freeList n p'.

  Theorem freeList_extensional : forall n p, HProp_extensional (freeList n p).
    destruct n; reflexivity.
  Qed.

  Theorem mallocHeap_extensional : forall p, HProp_extensional (mallocHeap p).
    reflexivity.
  Qed.

  Theorem mallocHeap_fwd : forall p, mallocHeap p ===> Ex n, Ex p', p =*> p' * freeList n p'.
    unfold mallocHeap; sepLemma.
  Qed.

  Theorem mallocHeap_bwd : forall p, (Ex n, Ex p', p =*> p' * freeList n p') ===> mallocHeap p.
    unfold mallocHeap; sepLemma.
  Qed.

  Theorem nil_bwd : forall n p, p = 0 -> [| n = 0 |] ===> freeList n p.
    destruct n; sepLemma.
  Qed.

  Theorem cons_bwd : forall n (p : W), p <> 0
    -> (Ex n', Ex sz, Ex p', [| n = S n' |]
      * [| noWrapAround p (2 + wordToNat sz) |]
      * (p ==*> sz, p') * (p ^+ $8) =?> wordToNat sz * freeList n' p')
    ===> freeList n p.
    destruct n; sepLemma; match goal with
                            | [ H : S _ = S _ |- _ ] => injection H
                          end; sepLemma.
  Qed.

  Theorem cons_fwd : forall n (p : W), p <> 0
    -> freeList n p
    ===> Ex n', Ex sz, Ex p', [| n = S n' |]
    * [| noWrapAround p (2 + wordToNat sz) |]
    * (p ==*> sz, p') * (p ^+ $8) =?> wordToNat sz * freeList n' p'.
    destruct n; sepLemma.
  Qed.
End FreeList.

Import FreeList.
Export FreeList.
Hint Immediate freeList_extensional mallocHeap_extensional.

Ltac expose := intros w ?; case_eq (wordToNat w); [ intro Heq;
  apply (f_equal (natToWord 32)) in Heq; rewrite natToWord_wordToNat in Heq;
    subst; elimtype False; auto
  | intros n Heq; repeat (destruct n; [
    apply (f_equal (natToWord 32)) in Heq; rewrite natToWord_wordToNat in Heq;
      subst; elimtype False; auto
    | eauto ]) ].

Lemma expose2N : forall n,
  (n >= 2)%nat
  -> exists n', n = S (S n').
  destruct n as [ | [ | ] ]; eauto; intros; omega.
Qed.

Lemma expose2' : forall w : W,
  $2 <= w
  -> exists n', wordToNat w = S (S n').
  expose.
Qed.

Lemma expose3' : forall (w : W),
  w >= $3
  -> exists n, wordToNat w = S (S (S n)).
  expose.
Qed.

Inductive fwd : Prop := Fwd.
Inductive bwd : Prop := Bwd.
Hint Constructors fwd bwd.

Lemma freeable_fwd : forall p sz,
  freeable p sz
  -> fwd
  -> p =?> sz ===> Ex u, Ex v, p =*> u * (p ^+ $4) =*> v * (p ^+ $8) =?> (sz-2).
  intuition idtac; destruct (expose2N BigEnough0) as [? Heq];
    rewrite Heq; sepLemma; apply allocated_shift_base; omega || words.
Qed.

Lemma expose2_bwd : forall p (sz : W),
  $2 <= sz
  -> bwd
  -> (Ex u, Ex v, p =*> u * (p ^+ $4) =*> v * (p ^+ $8) =?> (wordToNat sz-2)) ===> p =?> wordToNat sz.
  intros; destruct (expose2' H) as [? Heq];
    rewrite Heq; sepLemma; apply allocated_shift_base; omega || words.
Qed.

Lemma expose3_fwd : forall p (sz : W),
  sz >= $3
  -> p =?> wordToNat sz ===> Ex u, Ex v, Ex w, p =*> u * (p ^+ $4) =*> v * (p ^+ $8) =*> w * (p ^+ $12) =?> (wordToNat sz-3).
  intros; destruct (expose3' H) as [? Heq]; rewrite Heq; sepLemma;
    apply allocated_shift_base; omega || words.
Qed.

Definition hints : TacPackage.
  prepare (mallocHeap_fwd, cons_fwd, freeable_fwd, expose3_fwd)
  (mallocHeap_bwd, nil_bwd, cons_bwd, expose2_bwd).
Defined.

Definition initS : spec := SPEC("base", "size") reserving 0
  PRE[V] [| $3 <= V "size" |]
    * [| noWrapAround (V "base") (wordToNat (V "size")) |]
    * V "base" =?> wordToNat (V "size")
  POST[_] mallocHeap (V "base").

Definition freeS : spec := SPEC("base", "p", "n") reserving 1
  PRE[V] [| V "p" <> 0 |] * [| freeable (V "p") (wordToNat (V "n")) |]
    * V "p" =?> wordToNat (V "n") * mallocHeap (V "base")
  POST[_] mallocHeap (V "base").

Definition mallocS : spec := SPEC("base", "n") reserving 4
  PRE[V] [| V "n" >= $2 |] * mallocHeap (V "base")
  POST[R] [| R <> 0 |] * [| freeable R (wordToNat (V "n")) |]
    * R =?> wordToNat (V "n") * mallocHeap (V "base").

Definition m := bmodule "malloc" {{
  bfunction "init"("base", "size") [initS]
    "base" *<- "base" + 4;;
    "base" + 4 *<- "size" - 3;;
    "base" + 8 *<- 0;;
    Return 0
  end with bfunction "free"("base", "p", "n", "tmp") [freeS]
    Note [fwd];;
    "p" *<- "n" - 2;;
    "tmp" <-* "base";;
    "base" *<- "p";;
    "p" + 4 *<- "tmp";;
    Return 0
  end with bfunction "malloc"("base", "n", "cur", "prev", "tmp", "tmp2") [mallocS]
    "cur" <-* "base";;
    "prev" <- "base";;

    [Al len,
      PRE[V] [| (V "n" >= $2)%word |] * V "prev" =*> V "cur" * freeList len (V "cur")
      POST[R] Ex p, Ex len', [| R <> 0 |] * [| freeable R (wordToNat (V "n")) |] * R =?> wordToNat (V "n")
        * V "prev" =*> p * freeList len' p]
    While ("cur" <> 0) {
      "tmp" <-* "cur";;
      "tmp" <- "tmp" + 2;;
      If ("tmp" = "n") {
        (* Exact size match on the current free list block *)
        Note [bwd];;

        "tmp" <-* "cur" + 4;;
        "prev" *<- "tmp";;
        Return "cur"
      } else {
        "tmp2" <-* "cur";;
        If ("n" < "tmp2") {
          (* This free list block is large enough to split in two. *)

          (* Calculate starting address of a suffix of this free block to return to caller. *)
          "tmp" <- "tmp2" - "n";;
          "tmp" <- "tmp" + 2;;
          "tmp" <- 4 * "tmp";;
          "tmp" <- "cur" + "tmp";;

          (* Decrement size of free list block to reflect deleted suffix. *)
          "tmp2" <- "tmp2" - "n";;
          "cur" *<- "tmp2";;

          (* Return suffix starting address. *)
          Return "tmp"
        } else {
          (* Current block too small; continue to next. *)
          "prev" <- "cur" + 4;;
          "cur" <-* "prev"
        }
      }
    };;

    Diverge (* out of memory! *)
  end
}}.

Local Hint Extern 1 (@eq (word _) _ _) => words.
Local Hint Extern 5 (@eq nat _ _) => omega.
Local Hint Extern 5 (_ <= _)%nat => omega.

Lemma three_le : forall w : W,
  $3 <= w
  -> (wordToNat w >= 3)%nat.
  intros; destruct (le_lt_dec (wordToNat w) 3); auto.
  pre_nomega.
  change (wordToNat (natToWord _ 3)) with 3 in H.
  omega.
Qed.

Lemma noWrapAround_plus4 : forall p (sz : W),
  noWrapAround p (wordToNat sz)
  -> $3 <= sz
  -> p ^+ $4 <> $0.
  intros.
  intro.
  eapply H.
  2: eassumption.
  apply three_le in H0.
  omega.
Qed.

Lemma noWrapAround_weaken : forall p sz p' sz',
  noWrapAround p sz
  -> (sz' <= sz)%nat
  -> p' = p ^+ $(4 * (sz - sz'))
  -> noWrapAround p' sz'.
  unfold noWrapAround; intros; subst.
  intro.
  rewrite <- wplus_assoc in H1.
  rewrite <- natToW_plus in H1.
  eapply H; [ | eassumption ].
  omega.
Qed.

Local Hint Extern 1 (noWrapAround _ _) =>
  eapply noWrapAround_weaken; [ eassumption | | ].

Lemma weq_cong : forall (w : W) n m,
  n = m
  -> w ^+ $(n) = w ^+ $(m).
  intros; subst; W_eq.
Qed.

Lemma weq_0 : forall (w w' : W) n,
  w = w'
  -> n = 0
  -> w = w' ^+ $(n).
  intros; subst; W_eq.
Qed.

Local Hint Resolve weq_0 weq_cong.

Lemma two_ge : forall w : W,
  (wordToNat w >= 2)%nat
  -> w >= $2.
  intros.
  intro.
  red in H0.
  pre_nomega.
  change (wordToNat (natToWord _ 2)) with 2 in *.
  omega.
Qed.

Lemma wminus0 : forall (w : W),
  (wordToNat w >= 2)%nat
  -> wordToNat (w ^- $2) = wordToNat w - 2.
  intros; rewrite wordToNat_wminus; auto.
  apply two_ge; auto.
Qed.

Hint Rewrite wminus0 using assumption : sepFormula.

Lemma sub2 : forall w w' : W,
  w' ^+ $2 = w
  -> $2 <= w
  -> wordToNat w - 2 = wordToNat w'.
  intros; apply (f_equal (fun x => x ^- $2)) in H.
  replace (w' ^+ $2 ^- $2) with w' in H by W_eq.
  subst.
  symmetry; apply wordToNat_wminus; auto.
Qed.

Lemma two_le : forall w : W,
  $2 <= w
  -> (2 <= wordToNat w)%nat.
  intros.
  destruct (le_lt_dec 2 (wordToNat w)); auto.
  elimtype False; apply H.
  pre_nomega.
  change (wordToNat (natToWord _ 2)) with 2 in *.
  omega.
Qed.

Lemma four_times_wordToNat : forall w : W,
  $(4 * wordToNat w) = $4 ^* w.
  intros; rewrite wmult_alt; auto.
Qed.

Lemma noWrapAround_weaken' : forall p sz sz',
  noWrapAround p sz
  -> (sz' <= sz)%nat
  -> noWrapAround p sz'.
  unfold noWrapAround; auto.
Qed.

Lemma the_ole_switcheroo : forall a b : W,
  a ^+ natToW 8 ^+ $(4 * wordToNat b) = a ^+ natToW 4 ^* (b ^+ natToW 2) ^+ $0.
  intros; replace (natToW 4 ^* (b ^+ natToW 2)) with ($4 ^* b ^+ $8) by words;
    rewrite four_times_wordToNat; words.
Qed.

Section ok.
  Ltac t := sep hints; eauto;
    match goal with
      | [ H1 : noWrapAround _ (wordToNat ?sz), H2 : _ <= ?sz |- _ ] =>
        specialize (noWrapAround_plus4 H1 H2); intro
      | [ H : _ |- _ ] => apply sub2 in H; [ | solve [ auto ] ]
    end; sep hints;
    repeat match goal with
             | [ H : _ <= _ |- _ ] => apply three_le in H
             | [ H : _ |- _ ] => apply two_le in H
           end; change (wordToNat (natToW 3)) with 3 in *;
    change (wordToNat (natToWord _ 3)) with 3 in *; eauto.

  Theorem ok : moduleOk m.
    vcgen; try t.

    Opaque mult.

    sep hints.

    Hint Rewrite wordToNat_wminus using nomega : N.

    Focus 4.
    eapply Himp_trans; [ eapply allocated_split | sepLemma ].
    nomega.
    apply allocated_shift_base.
    repeat match goal with
             | H:_ = _ |- _ => rewrite H
           end.
    apply the_ole_switcheroo.
    nomega.

    rewrite H9.
    rewrite <- four_times_wordToNat.
    apply H17.
    rewrite wordToNat_wplus.
    rewrite wordToNat_wminus.
    nomega.
    nomega.
    rewrite wordToNat_wminus by nomega.
    apply (goodSize_weaken (wordToNat x7)).
    apply goodSize_wordToNat.
    nomega.

    rewrite H9.
    split.
    pre_nomega.
    change (wordToNat (natToW 2)) with 2 in *.
    omega.

    eapply noWrapAround_weaken.
    eassumption.
    nomega.
    f_equal.
    rewrite (mult_comm 4).
    rewrite natToW_times4.
    rewrite wmult_comm.
    f_equal.
    transitivity (natToW (wordToNat x7 - wordToNat (sel x4 "n") + 2)).

    change 2 with (wordToNat (natToW 2)) at 2.
    match goal with
      | [ |- ?X ^+ _ = _ ] => rewrite <- (natToWord_wordToNat X)
    end.
    rewrite <- natToW_plus.
    rewrite wordToNat_wminus.
    auto.
    nomega.

    f_equal.
    Opaque minus.
    nomega.

    eapply noWrapAround_weaken'; [ eassumption | nomega ].
  Qed.
End ok.
