Require Import AutoSep.

Set Implicit Arguments.


Definition copyS : spec := SPEC("dst", "src", "sz") reserving 3
  Ex src, Ex dst,
  PRE[V] array src (V "src") * array dst (V "dst")
    * [| V "sz" = length src |] * [| V "sz" = length dst |]
  POST[_] array src (V "src") * array src (V "dst").

Definition agreeUpTo (a b : list W) (i : nat) :=
  exists c, length c = i
    /\ exists a', a = c ++ a'
    /\ exists b', b = c ++ b'.

Definition array := bmodule "array" {{
  bfunction "copy"("dst", "src", "sz", "i", "to", "from") [copyS]
    "i" <- 0;;

    [Ex src, Ex dst, Ex n : nat,
      PRE[V] array src (V "src") * array dst (V "dst")
        * [| V "sz" = length src |] * [| V "sz" = length dst |]
        * [| V "i" = n |]
        * [| agreeUpTo dst src n |]
      POST[_] array src (V "src") * array src (V "dst")]
    While ("i" < "sz") {
      "to" <- 4 * "i";;
      "to" <- "dst" + "to";;

      "from" <- 4 * "i";;
      "from" <- "src" + "from";;

      "from" <-* "from";;
      "to" *<- "from";;

      "i" <- "i" + 1
    };;

    Return 0
  end
}}.

Lemma agreeUpTo_0 : forall a b, agreeUpTo a b 0.
  unfold agreeUpTo; exists nil; simpl; eauto.
Qed.

Local Hint Extern 1 (agreeUpTo _ _ 0) => apply agreeUpTo_0.

Hint Rewrite roundTrip_0 : sepFormula.

Theorem arrayOk : moduleOk array.
  vcgen.

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  auto.
  sep_auto.

  post.
  evaluate auto_ext.
  descend.
  step auto_ext.
  auto.

  Lemma next : forall (x : W) (i : nat),
    x = i
    -> x ^+ $1 = $(i + 1).
    intros; subst; symmetry; apply natToW_plus.
  Qed.

  Hint Extern 1 (_ ^+ _ = _) => apply next; eassumption.
  auto.

  Lemma updN_app : forall b v a,
    Array.updN (a ++ b) (Datatypes.length a) v
    = a ++ Array.updN b 0 v.
    induction a; simpl; intuition.
  Qed.

  Lemma upd_app : forall a b v,
    goodSize (Datatypes.length a)
    -> Array.upd (a ++ b) (Datatypes.length a) v
    = a ++ Array.upd b 0 v.
    unfold Array.upd.
    intros.
    rewrite roundTrip_0.
    rewrite wordToNat_natToWord_idempotent by assumption.
    apply updN_app.
  Qed.

  Lemma agreeUpTo_split : forall A (a b : list A),
    (length a < length (a ++ b))%nat
    -> exists h, exists t, b = h :: t.
    intros.
    rewrite app_length in H.
    assert (length b > 0)%nat by omega.
    destruct b; simpl in *; eauto; omega.
  Qed.

  Lemma goodSize_plus_l : forall n m,
    goodSize (n + m)
    -> goodSize n.
    unfold goodSize; generalize (Npow2 32); intros; nomega.
  Qed.

  Lemma goodSize_plus_r : forall n m,
    goodSize (n + m)
    -> goodSize m.
    unfold goodSize; generalize (Npow2 32); intros; nomega.
  Qed.

  Hint Immediate goodSize_plus_l goodSize_plus_r.

  Lemma agreeUpTo_S : forall a b n, agreeUpTo a b n
    -> (n < length a)%nat
    -> (n < length b)%nat
    -> goodSize (length a)
    -> agreeUpTo (Array.upd a (natToW n) (Array.sel b (natToW n))) b (n + 1).
    unfold agreeUpTo; intros.
    destruct H; intuition; subst.
    destruct H4; intuition; subst.
    destruct H4; subst.
    rewrite app_length in H2.
    exists (x ++ Array.sel (x ++ x1) (length x) :: nil).
    destruct (agreeUpTo_split _ _ H0) as [ ? [ ] ]; subst.
    rewrite app_length; intuition.
    rewrite upd_app by eauto.

    Lemma upd0 : forall w ws v,
      Array.upd (w :: ws) 0 v = v :: ws.
      intros; unfold Array.upd.
      rewrite roundTrip_0.
      reflexivity.
    Qed.

    rewrite upd0.
    exists x3.
    rewrite DepList.pf_list_simpl; intuition.
    destruct (agreeUpTo_split _ _ H1) as [ ? [ ] ]; subst.
    exists x4.
    rewrite DepList.pf_list_simpl.

    Lemma goodSize_S : forall n,
      goodSize (S n)
      -> goodSize n.
      unfold goodSize; generalize (Npow2 32); intros; nomega.
    Qed.

    Hint Immediate goodSize_S.

    Lemma selN_app : forall w ws' ws,
      goodSize (length ws)
      -> Array.selN (ws ++ w :: ws') (length ws) = w.
      induction ws; simpl; intuition.
    Qed.

    Lemma sel_app : forall ws w ws',
      goodSize (length ws)
      -> Array.sel (ws ++ w :: ws') (length ws) = w.
      unfold Array.sel; intros.
      rewrite wordToNat_natToWord_idempotent by auto.
      apply selN_app; auto.
    Qed.

    rewrite sel_app; eauto.
  Qed.

  rewrite H10.
  apply agreeUpTo_S; auto.

  Lemma agreeUpTo_goodSize : forall a b n,
    agreeUpTo a b n
    -> (n <= length a)%nat.
    unfold agreeUpTo; firstorder; subst.
    rewrite app_length; omega.
  Qed.

  Hint Immediate agreeUpTo_goodSize.

  Hint Rewrite Npow2_nat : N.

  rewrite H9 in H7.
  rewrite H10 in H7.
  apply Nlt_out in H7.
  repeat rewrite wordToN_nat in H7.
  repeat rewrite Nat2N.id in H7.
  
  Lemma lt_wordToNat : forall sz n m,
    (n < pow2 sz)%nat
    -> (m < pow2 sz)%nat
    -> (wordToNat (natToWord sz n) < wordToNat (natToWord sz m))%nat
    -> (n < m)%nat.
    intros.
    repeat rewrite wordToNat_natToWord_idempotent in H1 by nomega.
    auto.
  Qed.

  Lemma lt_wordToN : forall n m,
    goodSize n
    -> goodSize m
    -> (wordToNat (natToW n) < wordToNat (natToW m))%nat
    -> (n < m)%nat.
    unfold goodSize; intros;
      eapply lt_wordToNat; eauto;
        apply Nlt_out in H; apply Nlt_out in H0;
          autorewrite with N in *; auto.
  Qed.

  Theorem containsArray_goodSize : forall cs P stn ls st,
    interp cs (![P] (stn, st))
    -> containsArray P ls
    -> goodSize (length ls).
    unfold goodSize; intros.
    apply Nlt_in.
    autorewrite with N.
    eauto.
  Qed.

  Hint Resolve containsArray_goodSize.
  
  Lemma goodSize_le : forall n m,
    goodSize n
    -> (m <= n)%nat
    -> goodSize m.
    unfold goodSize; generalize (Npow2 32); intros; nomega.
  Qed.

  Hint Resolve goodSize_le lt_wordToN.
  apply lt_wordToN; eauto 8.

  rewrite H8 in H7.
  rewrite H10 in H7.
  apply Nlt_out in H7.
  repeat rewrite wordToN_nat in H7.
  repeat rewrite Nat2N.id in H7.
  apply lt_wordToN; eauto 8.

  eauto 8.
  
  step auto_ext.
  descend.
  step auto_ext.
  descend.
  step auto_ext.
  descend.
  step auto_ext.
  
  sep auto_ext.
  sep auto_ext.
  sep auto_ext.

  Lemma agreeUpTo_done : forall a b n,
    (length a <= n)%nat
    -> (length b <= n)%nat
    -> agreeUpTo a b n
    -> a = b.
    unfold agreeUpTo; firstorder; subst.
    rewrite app_length in *.
    assert (length x0 = 0) by omega.
    destruct x0; simpl in *; try omega.
    destruct x1; simpl in *; try omega.
    auto.
  Qed.

  erewrite (@agreeUpTo_done x1 x0).
  4: eassumption.

  reflexivity.

  Lemma goodSize_next : forall n,
    goodSize n
    -> goodSize (S n) \/ n = pred (pow2 32).
    unfold goodSize; intros.
    rewrite <- Npow2_nat in *.
    generalize dependent (Npow2 32).
    intros.
    Require Import Arith.
    rewrite Nat2N.inj_succ.
    destruct (eq_nat_dec n (pred (N.to_nat n0))); auto.
    left.
    nomega.
  Qed.
  
  Lemma le_wordToN : forall n m,
    goodSize n
    -> goodSize m
    -> natToW n <= natToW m
    -> (n <= m)%nat.
    intros.
    destruct (le_lt_dec n m); auto.
    elimtype False; apply H1; clear H1.
    red.
    repeat rewrite wordToN_nat.
    repeat rewrite wordToNat_natToWord_idempotent by auto.
    clear H H0; nomega.
  Qed.

  rewrite H10 in H7.
  rewrite H9 in H7.
  eapply le_wordToN; eauto 8.

  rewrite H10 in H7.
  rewrite H8 in H7.
  eapply le_wordToN; eauto 8.
Qed.
