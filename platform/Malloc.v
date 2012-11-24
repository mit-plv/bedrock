Require Import AutoSep.
Require Import Arith List.

Set Implicit Arguments.

Local Hint Extern 1 (himp _ (allocated _ _ _) (allocated _ _ _)) => apply allocated_shift_base.


(** * A free-list heap managed by the malloc library *)

Definition noWrapAround (p sz : W) :=
  goodSize (wordToNat p + 4 * wordToNat sz).

Definition freeable (p sz : W) :=
  (wordToNat sz >= 2)%nat
  /\ noWrapAround p sz.

Module Type FREE_LIST.
  Parameter freeList : nat (* number of elements in list *) -> W -> HProp.
  Parameter mallocHeap : W -> HProp.

  Axiom freeList_extensional : forall n p, HProp_extensional (freeList n p).
  Axiom mallocHeap_extensional : forall p, HProp_extensional (mallocHeap p).

  Axiom mallocHeap_fwd : forall p, mallocHeap p ===> Ex n, Ex p', p =*> p' * freeList n p'.
  Axiom mallocHeap_bwd : forall p, (Ex n, Ex p', p =*> p' * freeList n p') ===> mallocHeap p.

  Axiom nil_bwd : forall n p, p = 0 -> [| n = 0 |] ===> freeList n p.
  Axiom cons_bwd : forall n (p : W), p <> 0
    -> (Ex n', Ex sz, Ex p', [| n = S n' |] * [| noWrapAround (p ^+ $8) sz |]
      * (p ==*> sz, p') * (p ^+ $8) =?> wordToNat sz * freeList n' p')
    ===> freeList n p.

  Axiom cons_fwd : forall n (p : W), p <> 0
    -> freeList n p
    ===> Ex n', Ex sz, Ex p', [| n = S n' |] * [| noWrapAround (p ^+ $8) sz |]
    * (p ==*> sz, p')  * (p ^+ $8) =?> wordToNat sz * freeList n' p'.
End FREE_LIST.

Module FreeList : FREE_LIST.
  Open Scope Sep_scope.

  Fixpoint freeList (n : nat) (p : W) : HProp :=
    match n with
      | O => [| p = 0 |]
      | S n' => [| p <> 0 |] * Ex sz, Ex p', [| noWrapAround (p ^+ $8) sz |]
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
    -> (Ex n', Ex sz, Ex p', [| n = S n' |] * [| noWrapAround (p ^+ $8) sz |]
      * (p ==*> sz, p') * (p ^+ $8) =?> wordToNat sz * freeList n' p')
    ===> freeList n p.
    destruct n; sepLemma; match goal with
                            | [ H : S _ = S _ |- _ ] => injection H
                          end; sepLemma.
  Qed.

  Theorem cons_fwd : forall n (p : W), p <> 0
    -> freeList n p
    ===> Ex n', Ex sz, Ex p', [| n = S n' |] * [| noWrapAround (p ^+ $8) sz |]
    * (p ==*> sz, p') * (p ^+ $8) =?> wordToNat sz * freeList n' p'.
    destruct n; sepLemma.
  Qed.
End FreeList.

Import FreeList.
Export FreeList.
Hint Immediate freeList_extensional mallocHeap_extensional.

Definition splitMe cur full (_ : nat) := (cur =?> full)%Sep.

Lemma malloc_split : forall cur full init,
  (init <= full)%nat
  -> splitMe cur full init ===> cur =?> init
  * (cur ^+ $ (init * 4)) =?> (full - init).
  intros; eapply Himp_trans; [
    eapply allocated_split; eauto
    | sepLemma; apply allocated_shift_base; [
      rewrite mult_comm; simpl; unfold natToW; W_eq
      | reflexivity ] ].
Qed.

Ltac expose := intros w ?; case_eq (wordToNat w); [ intro Heq;
  apply (f_equal (natToWord 32)) in Heq; rewrite natToWord_wordToNat in Heq;
    subst; elimtype False; auto
  | intros n Heq; repeat (destruct n; [
    apply (f_equal (natToWord 32)) in Heq; rewrite natToWord_wordToNat in Heq;
      subst; elimtype False; auto
    | eauto ]) ].

Lemma expose2' : forall (w : W),
  w >= $2
  -> exists n, wordToNat w = S (S n).
  expose.
Qed.

Lemma expose3' : forall (w : W),
  w >= $3
  -> exists n, wordToNat w = S (S (S n)).
  expose.
Qed.

Lemma expose2_fwd : forall p (sz : W),
  sz >= $2
  -> p =?> wordToNat sz ===> Ex u, Ex v, p =*> u * (p ^+ $4) =*> v * (p ^+ $8) =?> (wordToNat sz-2).
  intros; destruct (expose2' H) as [? Heq]; rewrite Heq; sepLemma;
    apply allocated_shift_base; omega || words.
Qed.

Lemma expose2_bwd : forall p (sz : W),
  sz >= $2
  -> (Ex u, Ex v, p =*> u * (p ^+ $4) =*> v * (p ^+ $8) =?> (wordToNat sz-2)) ===> p =?> wordToNat sz.
  intros; destruct (expose2' H) as [? Heq]; rewrite Heq; sepLemma;
    apply allocated_shift_base; omega || words.
Qed.

Lemma expose3_fwd : forall p (sz : W),
  sz >= $3
  -> p =?> wordToNat sz ===> Ex u, Ex v, Ex w, p =*> u * (p ^+ $4) =*> v * (p ^+ $8) =*> w * (p ^+ $12) =?> (wordToNat sz-3).
  intros; destruct (expose3' H) as [? Heq]; rewrite Heq; sepLemma;
    apply allocated_shift_base; omega || words.
Qed.

Definition hints : TacPackage.
  prepare (mallocHeap_fwd, cons_fwd, malloc_split, expose2_fwd, expose3_fwd)
  (mallocHeap_bwd, nil_bwd, cons_bwd, expose2_bwd).
Defined.

Definition initS : spec := SPEC("base", "size") reserving 0
  PRE[V] [| $3 <= V "size" |] * [| noWrapAround (V "base") (V "size") |]
    * V "base" =?> wordToNat (V "size")
  POST[_] mallocHeap (V "base").

Definition freeS : spec := SPEC("base", "p", "n") reserving 1
  PRE[V] [| V "p" <> 0 |] * [| freeable (V "p") (V "n") |]
    * V "p" =?> wordToNat (V "n") * mallocHeap (V "base")
  POST[_] mallocHeap (V "base").

Definition mallocS : spec := SPEC("base", "n") reserving 4
  PRE[V] [| V "n" >= $2 |] * mallocHeap (V "base")
  POST[R] [| R <> 0 |] * [| freeable R (V "n") |]
    * R =?> wordToNat (V "n") * mallocHeap (V "base").

Definition mallocM := bmodule "malloc" {{
  bfunction "init"("base", "size") [initS]
    "base" *<- "base" + 4;;
    "base" + 4 *<- "size" - 3;;
    "base" + 8 *<- 0;;
    Return 0
  end (*with bfunction "free"("p", "n", "tmp") [freeS]
    "p" *<- "n";;
    "tmp" <-* 0;;
    0 *<- "p";;
    "p" <- "p" + 4;;
    "p" *<- "tmp";;
    Return 0
  end with bfunction "malloc"("n", "cur", "prev", "tmp", "tmp2") [mallocS]
    "cur" <-* 0;;
    "prev" <- 0;;

    [Al sz, Al len,
      PRE[V] [| V "n" = $(sz) |] * [| goodSize (sz+2) |] * V "prev" =*> V "cur" * freeList len (V "cur")
      POST[R] Ex p, Ex len', [| R <> 0 |] * [| freeable R (sz+2) |] * R =?> (sz + 2)
        * V "prev" =*> p * freeList len' p]
    While ("cur" <> 0) {
      "tmp" <-* "cur";;
      If ("tmp" = "n") {
        (* Exact size match on the current free list block *)
        "tmp" <- "cur" + 4;;
        "tmp" <-* "tmp";;
        "prev" *<- "tmp";;
        Return "cur"
      } else {
        "tmp" <- "n" + 2;;
        "tmp2" <-* "cur";;
        If ("tmp" < "tmp2") {
          (* This free list block is large enough to split in two. *)

          (* Calculate starting address of a suffix of this free block to return to caller. *)
          "tmp" <- "tmp2" - "n";;
          "tmp" <- 4 * "tmp";;
          "tmp" <- "cur" + "tmp";;

          (* Decrement size of free list block to reflect deleted suffix. *)
          "tmp2" <- "tmp2" - "n";;
          "tmp2" <- "tmp2" - 2;;
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
  end*)
}}.

Lemma four_neq_zero : natToW 4 <> natToW 0.
  discriminate.
Qed.

Lemma cancel8 : forall x y z,
  (z + 2 <= y)%nat
  -> x ^+ $8 ^+ ($(y) ^- $(z + 2)) ^* $4 = x ^+ $4 ^* ($(y) ^- natToW z).
  intros.
  autorewrite with sepFormula.
  rewrite natToW_plus.
  unfold natToW.
  W_eq.
Qed.

Local Hint Extern 1 (@eq (word _) _ _) => words.
Local Hint Extern 5 (@eq nat _ _) => omega.
Local Hint Extern 5 (_ <= _)%nat => omega.

Lemma wordToNat_wminus : forall sz (w u : word sz),
  u <= w
  -> wordToNat (w ^- u) = wordToNat w - wordToNat u.
  intros.
  eapply natToWord_inj; try eapply wordToNat_bound.
  2: generalize (wordToNat_bound w); omega.
  rewrite natToWord_wordToNat.
  unfold wminus.
  rewrite wneg_alt.
  unfold wnegN.
  pattern w at 1.
  rewrite <- (natToWord_wordToNat w).
  rewrite <- natToWord_plus.
  specialize (wordToNat_bound u); intro.
  destruct (le_lt_dec (wordToNat u) (wordToNat w)).
  replace (wordToNat w + (pow2 sz - wordToNat u))
    with (pow2 sz + (wordToNat w - wordToNat u)) by omega.
  rewrite natToWord_plus.
  rewrite natToWord_pow2.
  apply wplus_unit.
  elimtype False; apply H.
  nomega.
Qed.

Hint Rewrite wordToNat_wminus using assumption : sepFormula.

Lemma Nle_out : forall n m, (n <= m)%N -> (N.to_nat n <= N.to_nat m)%nat.
  intros; apply N.lt_eq_cases in H; intuition.
  apply Nlt_out in H0; auto.
Qed.

Lemma noWrapAround_plus4 : forall p sz,
  noWrapAround p sz
  -> $3 <= sz
  -> p ^+ $4 <> $0.
  intros; rewrite <- (natToWord_wordToNat p); rewrite <- natToW_plus;
    intro; apply natToW_inj in H1; auto; try omega.
  eapply goodSize_weaken; eauto.
  match goal with
    | [ |- (?X <= ?Y)%nat ] => destruct (le_lt_dec X Y)
  end; auto.
  elimtype False; apply H0.
  red.
  apply Nlt_in.
  autorewrite with N.
  rewrite wordToNat_natToWord_idempotent; auto.
  reflexivity.
Qed.

Lemma wordToNat_wplus : forall (w u : W),
  goodSize (wordToNat w + wordToNat u)
  -> wordToNat (w ^+ u) = wordToNat w + wordToNat u.
  intros.
  rewrite wplus_alt; unfold wplusN, wordBinN.
  apply wordToNat_natToWord_idempotent; auto.
Qed.

Lemma wordToNat_wmult : forall (w u : W),
  goodSize (wordToNat w * wordToNat u)
  -> wordToNat (w ^* u) = wordToNat w * wordToNat u.
  intros.
  rewrite wmult_alt; unfold wmultN, wordBinN.
  apply wordToNat_natToWord_idempotent; auto.
Qed.

Lemma wle_le : forall (n sz : W),
  n <= sz
  -> (wordToNat n <= wordToNat sz)%nat.
  intros; destruct (le_lt_dec (wordToNat n) (wordToNat sz)); auto.
  elimtype False; apply H.
  nomega.
Qed.

Lemma noWrapAround_weaken : forall p sz p' n,
  noWrapAround p sz
  -> n <= sz
  -> p' = p ^+ $4 ^* n
  -> noWrapAround p' (sz ^- n).
  unfold noWrapAround; intros; subst.
  rewrite wordToNat_wminus by auto.
  apply wle_le in H0.
  rewrite wordToNat_wplus.
  rewrite wordToNat_wmult.
  change (wordToNat (natToWord 32 4)) with 4.
  eapply goodSize_weaken; eauto.
  change (wordToNat (natToWord 32 4)) with 4.
  eapply goodSize_weaken; eauto.
  rewrite wordToNat_wmult.
  change (wordToNat (natToWord 32 4)) with 4.
  eapply goodSize_weaken; eauto.
  change (wordToNat (natToWord 32 4)) with 4.
  eapply goodSize_weaken; eauto.
Qed.

Local Hint Extern 1 (noWrapAround _ _) => eapply noWrapAround_weaken; [ eassumption | | ].

Section mallocOk.
  Hint Rewrite natToW_times4 cancel8 natToW_minus using solve [ auto ] : sepFormula.

  Theorem mallocMOk : moduleOk mallocM.
    vcgen.

    sep hints.
    sep hints.
    sep hints.
    sep hints.
    sep hints.

    match goal with
      | [ H1 : noWrapAround _ ?sz, H2 : _ <= ?sz |- _ ] =>
        specialize (noWrapAround_plus4 H1 H2); intro
    end.

    sep hints.
  Qed.
End mallocOk.
