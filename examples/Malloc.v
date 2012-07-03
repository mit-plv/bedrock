Require Import AutoSep.
Require Import Arith List.

Set Implicit Arguments.

Local Hint Extern 1 (himp _ (allocated _ _ _) (allocated _ _ _)) => apply allocated_shift_base.

Lemma wplus_lt_lift : forall sz n m o : nat,
  (N.of_nat (n + m) < Npow2 sz)%N
  -> (N.of_nat o < Npow2 sz)%N
  -> natToWord sz (n + m) < natToWord sz o
  -> (n + m < o)%nat.
  unfold wlt; intros.
  unfold wplusN, wordBinN in *.
  repeat rewrite wordToNat_natToWord_idempotent in * by nomega.
  repeat rewrite wordToN_nat in *.
  repeat rewrite wordToNat_natToWord_idempotent in * by nomega.
  nomega.
Qed.

Local Hint Extern 1 (_ <= _)%nat => match goal with
                                      | [ H : _ < _ |- _ ] =>
                                        apply wplus_lt_lift in H;
                                          [ omega | solve [ eauto ] | solve [ eauto ] ]
                                    end.

Lemma goodSize_plus2 : forall n,
  goodSize (n + 2)
  -> goodSize n.
  intros; eapply goodSize_plus_l; eauto.
Qed.

Lemma goodSize_diff : forall x y z,
  (N.of_nat (x + 2) < z)%N
  -> (N.of_nat (x - y - 2 + 2) < z)%N.
  intros; nomega.
Qed.

Local Hint Resolve goodSize_plus2.
Local Hint Extern 1 (_ < _)%N => apply goodSize_plus2.
Local Hint Extern 1 (goodSize (_ - _ - _ + _ )) => apply goodSize_diff.


(** * A free-list heap managed by the malloc library *)

Module Type FREE_LIST.
  Parameter freeable : W -> nat -> Prop.

  Axiom goodSize_freeable : forall p sz,
    freeable p sz
    -> goodSize sz.

  Axiom freeable_narrow : forall a sz sz',
    freeable a sz
    -> (sz' <= sz)%nat
    -> freeable a sz'.

  Axiom freeable_split : forall a b x y,
    freeable a (x + 2)
    -> $(y + 2) < natToW x
    -> goodSize (y + 2)
    -> b = a ^+ $4 ^* ($(x) ^- $(y))
    -> freeable b (y + 2).

  Axiom it's_not_zero : forall x y a b b',
    x = y ^+ $4 ^* ($(a) ^- b)
    -> freeable y (a + 2)
    -> b ^+ $2 < natToW a
    -> b = natToW b'
    -> goodSize (b' + 2)
    -> x <> $0.

  Parameter freeList : nat (* number of elements in list *) -> W -> HProp.
  Parameter mallocHeap : HProp.

  Axiom freeList_extensional : forall n p, HProp_extensional (freeList n p).
  Axiom mallocHeap_extensional : HProp_extensional mallocHeap.

  Axiom mallocHeap_fwd : mallocHeap ===> Ex n, Ex p, 0 =*> p * freeList n p.
  Axiom mallocHeap_bwd : (Ex n, Ex p, 0 =*> p * freeList n p) ===> mallocHeap.

  Axiom nil_bwd : forall n p, p = 0 -> [| n = 0 |] ===> freeList n p.
  Axiom cons_bwd : forall n (p : W), p <> 0
    -> (Ex n', Ex sz, Ex p', [| n = S n' /\ freeable p (sz+2) |] * (p ==*> $(sz), p')
      * (p ^+ $8) =?> sz * freeList n' p')
    ===> freeList n p.

  Axiom cons_fwd : forall n (p : W), p <> 0
    -> freeList n p
    ===> Ex n', Ex sz, Ex p', [| n = S n' /\ freeable p (sz+2) |] * (p ==*> $(sz), p')
    * (p ^+ $8) =?> sz * freeList n' p'.
End FREE_LIST.

Module FreeList : FREE_LIST.
  Definition noWrapAround (p : W) (sz : nat) :=
    forall n, (n < sz * 4)%nat -> p ^+ $(n) <> $0.

  Definition freeable (p : W) (sz : nat) := goodSize sz /\ noWrapAround p sz.

  Lemma goodSize_narrow : forall sz sz' q,
    (N.of_nat sz < q)%N
    -> (sz' <= sz)%nat
    -> (N.of_nat sz' < q)%N.
    intros; nomega.
  Qed.

  Lemma freeable_narrow : forall a sz sz',
    freeable a sz
    -> (sz' <= sz)%nat
    -> freeable a sz'.
    unfold freeable; intuition eauto.
    eapply goodSize_narrow; eauto.

    do 2 intro.
    apply H2.
    omega.
  Qed.

  Lemma goodSize_freeable : forall p sz,
    freeable p sz
    -> goodSize sz.
    unfold freeable; tauto.
  Qed.

  Lemma it's_not_zero : forall x y a b b',
    x = y ^+ $4 ^* ($(a) ^- b)
    -> freeable y (a + 2)
    -> b ^+ $2 < natToW a
    -> b = natToW b'
    -> goodSize (b' + 2)
    -> x <> $0.
    intros; subst.
    destruct H0.
    intro.
    apply (H0 (4 * (a - b'))).
    auto.
    rewrite mult_comm.
    rewrite natToW_times4.
    rewrite natToW_minus.
    rewrite wmult_comm.
    assumption.
    rewrite <- natToWord_plus in H1.
    auto.
  Qed.

  Lemma freeable_split : forall a b x y,
    freeable a (x + 2)
    -> $(y + 2) < natToW x
    -> goodSize (y + 2)
    -> b = a ^+ $4 ^* ($(x) ^- $(y))
    -> freeable b (y + 2).
    destruct 1; split; auto; subst.
    do 2 intro.
    specialize (H0 (4 * (x - y) + n)).
    intro.
    apply H0.
    auto.
    rewrite natToW_plus.
    rewrite mult_comm.
    rewrite natToW_times4.
    rewrite natToW_minus.
    rewrite wmult_comm.
    rewrite wplus_assoc.
    assumption.
    auto.
  Qed.

  Open Scope Sep_scope.

  Fixpoint freeList (n : nat) (p : W) : HProp :=
    match n with
      | O => [| p = 0 |]
      | S n' => [| p <> 0 |] * Ex sz, Ex p', [| freeable p (sz+2) |] * (p ==*> $(sz), p')
        * (p ^+ $8) =?> sz * freeList n' p'
    end.

  Definition mallocHeap := Ex n, Ex p, 0 =*> p * freeList n p.

  Theorem freeList_extensional : forall n p, HProp_extensional (freeList n p).
    destruct n; reflexivity.
  Qed.

  Theorem mallocHeap_extensional : HProp_extensional mallocHeap.
    reflexivity.
  Qed.

  Theorem mallocHeap_fwd : mallocHeap ===> Ex n, Ex p, 0 =*> p * freeList n p.
    unfold mallocHeap; sepLemma.
  Qed.

  Theorem mallocHeap_bwd : (Ex n, Ex p, 0 =*> p * freeList n p) ===> mallocHeap.
    unfold mallocHeap; sepLemma.
  Qed.

  Theorem nil_bwd : forall n p, p = 0 -> [| n = 0 |] ===> freeList n p.
    destruct n; sepLemma.
  Qed.

  Theorem cons_bwd : forall n (p : W), p <> 0
    -> (Ex n', Ex sz, Ex p', [| n = S n' /\ freeable p (sz+2) |] * (p ==*> $(sz), p')
      * (p ^+ $8) =?> sz * freeList n' p')
    ===> freeList n p.
    destruct n; sepLemma; match goal with
                            | [ H : S _ = S _ |- _ ] => injection H
                          end; sepLemma.
  Qed.

  Theorem cons_fwd : forall n (p : W), p <> 0
    -> freeList n p
    ===> Ex n', Ex sz, Ex p', [| n = S n' /\ freeable p (sz+2) |] * (p ==*> $(sz), p')
    * (p ^+ $8) =?> sz * freeList n' p'.
    destruct n; sepLemma.
  Qed.
End FreeList.

Import FreeList.
Export FreeList.
Hint Immediate freeList_extensional mallocHeap_extensional.

Lemma malloc_split' : forall cur full init,
  (init < full)%nat
  -> cur =?> full ===> cur =?> init * allocated cur (init * 4) (full - init).
  intros.
  replace (init * 4) with (4 * init) by omega.
  assert (Hle : (init <= full)%nat) by omega.
  apply (@allocated_split cur init full 0 Hle).
Qed.

Definition splitMe cur full (_ : nat) := (cur =?> full)%Sep.

Local Hint Immediate goodSize_plus_l.
Local Hint Resolve wplus_lt_lift.

Lemma malloc_split'' : forall cur full init,
  goodSize (init + 2)
  -> goodSize (full + 2)
  -> natToW (init + 2) < natToW full
  -> splitMe cur full init ===> cur =?> (full - init - 2) * allocated cur ((full - (init + 2)) * 4) (init + 2).
  intros.
  replace (full - init - 2) with (full - (init + 2)) by omega.
  replace (allocated cur ((full - (init + 2)) * 4) (init + 2))
    with (allocated cur ((full - (init + 2)) * 4) (full - (full - (init + 2)))).
  apply malloc_split'; eauto.
  apply wplus_lt_lift in H1.
  2: eauto.
  2: eauto.
  f_equal.
  omega.
Qed.

Lemma malloc_split''' : forall cur full init,
  goodSize (init + 2)
  -> goodSize (full + 2)
  -> natToW (init + 2) < natToW full
  -> splitMe cur full init ===> cur =?> (full - init - 2) * (cur ^+ $ ((full - (init + 2)) * 4)%nat) =?> (init + 2).
  intros; eapply Himp_trans.
  apply malloc_split''; auto.
  sepLemma.
  apply allocated_shift_base; auto.
  autorewrite with sepFormula.
  repeat rewrite natToW_times4.
  W_eq.
Qed.

Local Hint Resolve goodSize_freeable.

Lemma malloc_split : forall cur full init,
  (*goodSize (init + 2)
  -> goodSize (full + 2)
  ->*) (init <= full)%nat
  -> splitMe cur full init ===> cur =?> init
  * (cur ^+ $ (init * 4)) =?> (full - init).
  intros; eapply Himp_trans.
  eapply allocated_split.
  eauto.
  sepLemma.
  apply allocated_shift_base.
  rewrite mult_comm; simpl.
  unfold natToW.
  W_eq.
  auto.
Qed.

(*TIME Clear Timing Profile. *)

Definition hints : TacPackage.
(*TIME idtac "malloc:prepare". Time *)
  prepare (mallocHeap_fwd, cons_fwd, malloc_split) (mallocHeap_bwd, nil_bwd, cons_bwd).
(*TIME Time *)Defined.

Definition initS : spec := SPEC("size") reserving 0
  Ex n,
  PRE[V] [| V("size") = $(n) |] * [| freeable 4 (n+2) |] * 0 =?> (3 + n)
  POST[_] mallocHeap.

Definition freeS : spec := SPEC("p", "n") reserving 1
  Ex n,
  PRE[V] [| V "n" = $(n) |] * [| V "p" <> 0 |] * [| freeable (V "p") (n+2) |] * V "p" =?> (2 + n) * mallocHeap
  POST[_] mallocHeap.

Definition mallocS : spec := SPEC("n") reserving 4
  Ex sz,
  PRE[V] [| V "n" = $(sz) |] * [| goodSize (sz+2) |] * mallocHeap
  POST[R] [| R <> 0 |] * [| freeable R (sz+2) |] * R =?> (2 + sz) * mallocHeap.

Definition mallocM := bmodule "malloc" {{
  (*bfunction "init"("size") [initS]
    0 *<- 4;;
    4 *<- "size";;
    8 *<- 0;;
    Return 0
  end with bfunction "free"("p", "n", "tmp") [freeS]
    "p" *<- "n";;
    "tmp" <-* 0;;
    0 *<- "p";;
    "p" <- "p" + 4;;
    "p" *<- "tmp";;
    Return 0
  end with*) bfunction "malloc"("n", "cur", "prev", "tmp", "tmp2") [mallocS]
    "cur" <-* 0;;
    "prev" <- 0;;

    [Ex sz, Ex len,
      PRE[V] [| V "n" = $(sz) |] * [| goodSize (sz+2) |] * V "prev" =*> V "cur" * freeList len (V "cur")
      POST[R] Ex p, Ex len', [| R <> 0 |] * [| freeable R (sz+2) |] * R =?> (2 + sz)
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
  end
}}.

Lemma four_neq_zero : natToW 4 <> natToW 0.
  discriminate.
Qed.

Local Hint Extern 2 (@eq (word _) _ _) =>
  match goal with
    | _ => W_eq
    | [ H : _ = _ |- _ ] => rewrite <- H; W_eq
  end.

Local Hint Resolve natToW_inj.

Lemma cancel8 : forall x y z,
  (z + 2 <= y)%nat
  -> x ^+ $8 ^+ ($(y) ^- $(z + 2)) ^* $4 = x ^+ $4 ^* ($(y) ^- natToW z).
  intros.
  autorewrite with sepFormula.
  rewrite natToW_plus.
  unfold natToW.
  W_eq.
Qed.

Local Hint Extern 1 False => eapply it's_not_zero; eassumption.
Local Hint Extern 1 (freeable _ _) => eapply freeable_narrow; [ eassumption | omega ].
Local Hint Extern 1 (freeable _ _) => eapply freeable_split; eassumption.

Section mallocOk.
  Hint Rewrite natToW_times4 cancel8 natToW_minus using solve [ auto ] : sepFormula.

  Theorem mallocMOk : moduleOk mallocM.
    vcgen.

    (*sep hints.
    sep hints.
    sep_auto; auto.
    sep hints.
    sep hints.
    auto.
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
    
    Lemma they're_the_same : forall a b c,
      natToW a = b
      -> b = natToW c
      -> goodSize a
      -> goodSize c
      -> a = c.
      intros; subst; match goal with
                       | [ H : _ |- _ ] => apply natToW_inj in H; assumption
                     end.
    Qed.

    match goal with
      | [ _ : natToW ?a = ?b, _ : ?b = natToW ?c |- _ ] =>
        assert (a = c) by (eapply they're_the_same; eauto); subst
    end.
    congruence.

    match goal with
      | [ _ : natToW ?a = ?b, _ : ?b = natToW ?c |- _ ] =>
        assert (a = c) by (eapply they're_the_same; eauto); subst
    end.
    eauto.

    sep hints.
    sep hints.
    sep hints.*)

    Focus 15.

    post.
    evaluate hints.
    repeat match goal with
             | [ H : True |- _ ] => clear H
             | [ H : ?X, H' : ?X |- _ ] => clear H'
           end.
    match goal with
      | [ _ : ?x ^+ natToW 2 < natToW ?full,
          _ : ?x = natToW ?x',
          H : context[(?base =?> ?full)%Sep],
          H' : freeable _ (?full + 2) |- _ ] =>
        change (base =?> full)%Sep with (splitMe base full (full - (x' + 2))) in H(*;
          generalize (goodSize_freeable H')*)
    end.

    assert (x8 - (x2 + 2) <= x8)%nat by omega.
    evaluate hints.
    repeat match goal with
             | [ H : True |- _ ] => clear H
             | [ H : ?X, H' : ?X |- _ ] => clear H'
           end.

    Lemma split_bound : forall x a x',
      x ^+ natToW 2 < natToW a
      -> x = natToW x'
      -> goodSize (x' + 2)
      -> goodSize a
      -> (x' + 2 <= a)%nat.
      intros; subst.
      rewrite <- natToW_plus in H.
      apply Nlt_out in H.
      repeat rewrite wordToN_nat in H.
      repeat rewrite Nat2N.id in H.
      repeat rewrite wordToNat_natToWord_idempotent in H by auto.
      omega.
    Qed.

    assert (x2 + 2 <= x8)%nat by (eapply split_bound; eauto).
    replace (x8 - (x8 - (x2 + 2))) with (2 + x2) in H5 by omega.
    simpl in H5.
    replace (x8 - (x2 + 2)) with (x8 - x2 - 2) in H5 by omega.

    descend.
    step hints.
    step hints.
    descend.
    step hints.
    
    Axiom freeable_split : forall a b x y y',
      freeable a (x + 2)
      -> y ^+ $2 < natToW x
      -> y = natToW y'
      -> goodSize (y' + 2)
      -> b = a ^+ $4 ^* ($(x) ^- y)
      -> freeable b (y' + 2).

    eapply freeable_split; eassumption.

    step hints.
    rewrite H2.
    repeat rewrite <- natToW_minus.
    replace (x8 - (x2 + 2)) with (x8 - x2 - 2) by omega.
    step hints.

    Lemma split_bound : forall x a x',
      x ^+ natToW 2 < natToW a
      -> x = natToW x'
      -> goodSize (x' + 2)
      -> goodSize a
      -> (x' + 2 <= a)%nat.
      intros; subst.
      rewrite <- natToW_plus in H.
      apply Nlt_out in H.
      repeat rewrite wordToN_nat in H.
      repeat rewrite Nat2N.id in H.
      repeat rewrite wordToNat_natToWord_idempotent in H by auto.
      omega.
    Qed.

    assert (x2 + 2 <= x8)%nat by (eapply split_bound; eauto).

    replace (x8 - (x8 - x2 - 2)) with (2 + x2) by omega.
    descend.
    step hints.


    Lemma split_bound : forall x a x',
      x ^+ natToW 2 < natToW a
      -> x = natToW x'
      -> goodSize (x' + 2)
      -> goodSize a
      -> (x' + 2 <= a)%nat.
      intros; subst.
      rewrite <- natToW_plus in H.
      apply Nlt_out in H.
      repeat rewrite wordToN_nat in H.
      repeat rewrite Nat2N.id in H.
      repeat rewrite wordToNat_natToWord_idempotent in H by auto.
      omega.
    Qed.

    eapply split_bound.
    eassumption.
    eassumption.
    eassumption.
    eauto.

    evaluate hints.
    
    descend.
    step hints.
    step hints.
    descend.
    step hints.

    Axiom freeable_split : forall a b x y y',
      freeable a (x + 2)
      -> y ^+ $2 < natToW x
      -> y = natToW y'
      -> goodSize (y' + 2)
      -> b = a ^+ $4 ^* ($(x) ^- y)
      -> freeable b (y' + 2).

    eapply freeable_split; eassumption.

    step hints.
    
    


    Ltac t := solve [ generalize four_neq_zero; sep hints; eauto; cancel hints
      | sep_auto; auto (* extra case needed to compensate for some hint-triggered bug in tactics *) ].

    t.
    t.
    t.
    t.
    t.
  Qed.

    post.
    evaluate auto_ext.
    evaluate hints.
    

    t.
    

    sep_auto.
    auto.
    auto.

    t.
    

    t.
    t.
    t.
    t.
    t.

(*TIME idtac "malloc:verify". Time *)
   vcgen; abstract solve [ generalize four_neq_zero; sep hints; auto;
      try match goal with
            | [ H : _ = _ |- _ ] => apply natToW_inj in H; [ congruence | | ]
          end; eauto
      | post; evaluate hints;
        match goal with
          | [ _ : natToW ?init ^+ natToW 2 < natToW ?full,
            H' : freeable _ (?full + 2),
            H : context[(?base =?> ?full)%Sep] |- _ ] =>
          change (base =?> full)%Sep with (splitMe base full init) in H;
            generalize (goodSize_freeable H')
        end; sep hints ].

(*TIME Time *)Qed.

(*TIME Print Timing Profile. *)
End mallocOk.
