Require Import AutoSep.
Require Import Arith List.

Set Implicit Arguments.


(** * Allocated memory regions with unknown contents *)

Lemma allocated_shift_base' : forall base base' len offset offset',
  base ^+ $(offset) = base' ^+ $(offset')
  -> allocated base offset len ===> allocated base' offset' len.
  induction len; sepLemma.

  match goal with
    | [ |- context[(?X =*> _)%Sep] ] =>
      assert (X = base ^+ natToW offset)
  end.
  destruct offset; auto.
  W_eq.
  rewrite H0; clear H0.

  match goal with
    | [ |- context[(?X =*> ?Y)%Sep] ] =>
      is_evar Y;
      assert (X = base' ^+ natToW offset')
  end.
  destruct offset'; auto.
  W_eq.
  rewrite H0; clear H0.

  match goal with
    | [ H : ?X = _ |- context[(?Y =*> _)%Sep] ] => change Y with X; rewrite H
  end.
  sepLemma.
  apply IHlen.
  repeat match goal with
           | [ |- context[S (S (S (S ?N)))] ] =>
             match N with
               | O => fail 1
               | _ => change (S (S (S (S N)))) with (4 + N)
             end
         end.
  repeat rewrite natToW_plus.
  transitivity ($4 ^+ (base ^+ $(offset))).
  simpl; unfold natToW; W_eq.
  transitivity ($4 ^+ (base' ^+ $(offset'))).
  unfold natToW in *.
  congruence.
  simpl; unfold natToW; W_eq.
Qed.

Theorem allocated_shift_base : forall base base' len len' offset offset',
  base ^+ $(offset) = base' ^+ $(offset')
  -> len = len'
  -> allocated base offset len ===> allocated base' offset' len'.
  intros; subst; apply allocated_shift_base'; auto.
Qed.

Local Hint Extern 1 (himp _ (allocated _ _ _) (allocated _ _ _)) => apply allocated_shift_base.

Theorem allocated_split : forall base len' len offset,
  (len' <= len)%nat
  -> allocated base offset len ===> allocated base offset len' * allocated base (offset + 4 * len') (len - len').
  induction len'; simpl; inversion 1; sepLemma.
  rewrite plus_0_r; sepLemma.
  rewrite minus_diag; sepLemma.
  specialize (IHlen' m (S (S (S (S offset))))).
  assert (len' <= m)%nat by omega.
  intuition.
  match goal with
    | [ _ : forall specs, himp _ _ (_ * allocated _ ?X _)%Sep |- himp _ _ (_ * allocated _ ?Y _)%Sep ] =>
      replace Y with X by omega
  end.
  auto.
Qed.

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

  Axiom it's_not_zero : forall x y a b,
    x = y ^+ $4 ^* ($(a) ^- $(b))
    -> x = $0
    -> freeable y (a + 2)
    -> $(b + 2) < natToW a
    -> goodSize (b + 2)
    -> False.

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

  Lemma it's_not_zero : forall x y a b,
    x = y ^+ $4 ^* ($(a) ^- $(b))
    -> x = $0
    -> freeable y (a + 2)
    -> $(b + 2) < natToW a
    -> goodSize (b + 2)
    -> False.
    intros; subst.
    destruct H1.
    apply (H1 (4 * (a - b))).
    auto.
    rewrite mult_comm.
    rewrite natToW_times4.
    rewrite natToW_minus.
    rewrite wmult_comm.
    assumption.
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
  goodSize (init + 2)
  -> goodSize (full + 2)
  -> natToW (init + 2) < natToW full
  -> splitMe cur full init ===> cur =?> (full - init - 2)
  * (Ex v, (cur ^+ $ ((full - (init + 2)) * 4)%nat) =*> v)
  * (Ex v, (cur ^+ $ ((full - (init + 2)) * 4) ^+ $4) =*> v)
  * allocated (cur ^+ $ ((full - (init + 2)) * 4)) 8 init.
  intros; eapply Himp_trans.
  apply malloc_split'''; eauto.
  autorewrite with sepFormula; auto.
  rewrite plus_comm; simpl.
  sepLemma.
Qed.

(*TIME Clear Timing Profile. *)

Definition hints : TacPackage.
(*TIME idtac "malloc:prepare". Time *)
  prepare auto_ext tt tt (mallocHeap_fwd, cons_fwd, malloc_split) (mallocHeap_bwd, nil_bwd, cons_bwd).
(*TIME Time *)Defined.

Definition initS : assert := st ~> ExX, Ex n, [| st#Rv = $(n) /\ freeable 4 (n+2) |]
  /\ ![ ^[0 =?> (3 + n)] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp |] /\ ![ ^[mallocHeap] * #1 ] st').

Definition freeS : assert := st ~> ExX, Ex p : W, Ex n, [| p <> 0 /\ freeable p (n+2) |]
  /\ ![ (st#Sp ==*> p, $(n)) * ^[p =?> (2 + n)] * ^[mallocHeap] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp |] /\ ![ (st#Sp ==*> p, $(n)) * ^[mallocHeap] * #1 ] st').

Definition mallocS : assert := st ~> ExX, Ex sz, Ex v, [| goodSize (sz+2) |]
  /\ ![ (st#Sp ==*> $(sz), v) * ^[mallocHeap] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp /\ st'#Rv <> 0 /\ freeable st'#Rv (sz+2) |]
    /\ Ex a, Ex b, ![ (st#Sp ==*> a, b) * ^[st'#Rv =?> (2 + sz)] * ^[mallocHeap] * #1 ] st').

Definition mallocM := bmodule "malloc" {{
  bfunction "init" [initS] {
    $[0] <- 4;;
    $[4] <- Rv;;
    $[8] <- 0;;
    Return 0
  } with bfunction "free" [freeS] {
    Rv <- $[Sp];;
    $[Rv] <- $[Sp+4];;
    $[Rv+4] <- $[0];;
    $[0] <- Rv;;
    Return 0
  } with bfunction "malloc" [mallocS] {
    Rv <- $[0];;
    $[Sp+4] <- Rp;;
    Rp <- 0;;

    [st ~> ExX, Ex sz, Ex ret, Ex n, [| goodSize (sz+2) |]
      /\ ![ (st#Sp ==*> $(sz), ret) * st#Rp =*> st#Rv * ^[freeList n st#Rv] * #0 ] st
      /\ ret @@ (st' ~> [| st'#Sp = st#Sp /\ st'#Rv <> 0 /\ freeable st'#Rv (sz+2) |]
        /\ Ex a, Ex b, Ex n', Ex p,
        ![ (st#Sp ==*> a, b) * ^[st'#Rv =?> (2 + sz)] * st#Rp =*> p * ^[freeList n' p] * #1 ] st')]
    While (Rv <> 0) {
      If ($[Rv] = $[Sp]) {
        (* Exact size match on the current free list block *)
        $[Rp] <- $[Rv+4];;
        Rp <- $[Sp+4];;
        Return Rv
      } else {
        Rp <- $[Sp] + 2;;
        If (Rp < $[Rv]) {
          (* This free list block is large enough to split in two. *)

          (* Calculate starting address of a suffix of this free block to return to caller. *)
          Rp <- $[Rv] - $[Sp];;
          Rp <- 4 * Rp;;
          Rp <- Rv + Rp;;

          (* Decrement size of free list block to reflect deleted suffix. *)
          $[Rv] <- $[Rv] - $[Sp];;
          $[Rv] <- $[Rv] - 2;;

          (* Return suffix starting address. *)
          Rv <- Rp;;
          Rp <- $[Sp+4];;
          Return Rv
        } else {
          (* Current block too small; continue to next. *)
          Rp <- Rv+4;;
          Rv <- $[Rv+4]
        }
      }
    };;

    Diverge (* out of memory! *)
  }
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
