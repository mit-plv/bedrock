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

    [Ex src, Ex dst,
      PRE[V] array src (V "src") * array dst (V "dst")
        * [| V "sz" = length src |] * [| V "sz" = length dst |]
        * [| agreeUpTo dst src (wordToNat (V "i")) |]
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

Hint Rewrite wordToN_nat Npow2_nat : N.

Hint Rewrite roundTrip_0 roundTrip_1 wordToNat_natToWord_idempotent using assumption : Arr.

Lemma next : forall sz (w : word (S sz)) bound,
  w < bound
  -> wordToNat w + 1 = wordToNat (w ^+ $1).
  intros; rewrite wplus_alt; unfold wplusN, wordBinN.
    autorewrite with Arr.
  symmetry; apply wordToNat_natToWord_idempotent.
  apply Nlt_out in H; apply Nlt_in.
  autorewrite with N in *.
  specialize (wordToNat_bound bound).
  omega.
Qed.

Hint Resolve next.

Lemma updN_app : forall b v a,
  Array.updN (a ++ b) (Datatypes.length a) v
  = a ++ Array.updN b 0 v.
  induction a; simpl; intuition.
Qed.

Hint Rewrite updN_app : Arr.

Lemma upd_app : forall a b v,
  goodSize (length a)
  -> Array.upd (a ++ b) (length a) v
  = a ++ Array.upd b 0 v.
  unfold Array.upd; intros; autorewrite with Arr; auto.
Qed.

Hint Rewrite app_length using solve [ auto ] : Arr.

Lemma goodSize_wordToNat : forall (w : W),
  goodSize (wordToNat w).
  intros; specialize (wordToNat_bound w); intros; unfold goodSize.
  unfold W in *; generalize dependent 32; intros; nomega.
Qed.

Lemma upd_app' : forall a b v w,
  length a = wordToNat w
  -> Array.upd (a ++ b) w v
  = a ++ Array.upd b 0 v.
  intros; assert (natToWord 32 (length a) = natToWord 32 (wordToNat w)) by congruence;
    rewrite natToWord_wordToNat in *; subst; apply upd_app.
  rewrite H; apply goodSize_wordToNat.
Qed.

Hint Rewrite upd_app' using assumption : Arr.

Lemma agreeUpTo_split : forall A (a b : list A),
  (length a < length (a ++ b))%nat
  -> exists h, exists t, b = h :: t.
  intros; autorewrite with Arr in *;
    assert (length b > 0)%nat by omega;
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

Lemma goodSize_S : forall n,
  goodSize (S n)
  -> goodSize n.
  unfold goodSize; generalize (Npow2 32); intros; nomega.
Qed.

Hint Immediate goodSize_S.

Lemma selN_middle : forall w ws' ws,
  goodSize (length ws)
  -> Array.selN (ws ++ w :: ws') (length ws) = w.
  induction ws; simpl; intuition.
Qed.

Hint Rewrite selN_middle using solve [ auto ] : Arr.

Lemma sel_middle : forall ws w ws',
  goodSize (length ws)
  -> Array.sel (ws ++ w :: ws') (length ws) = w.
  unfold Array.sel; intros; autorewrite with Arr; reflexivity.
Qed.

Hint Rewrite sel_middle using solve [ auto ] : Arr.

Hint Rewrite natToWord_wordToNat DepList.pf_list_simpl : Arr.
Hint Rewrite <- plus_n_O : Arr.

Lemma sel_middle' : forall ws w ws' n,
  length ws = wordToNat n  
  -> Array.sel (ws ++ w :: ws') n = w.
  intros; assert (natToWord 32 (length ws) = natToWord 32 (wordToNat n)) by congruence;
    autorewrite with Arr in *; subst.
  rewrite H; autorewrite with Arr.
  apply sel_middle.
  rewrite H; apply goodSize_wordToNat.
Qed.

Hint Rewrite sel_middle' using assumption : Arr.

Lemma upd0 : forall w ws v,
  Array.upd (w :: ws) 0 v = v :: ws.
  intros; unfold Array.upd; autorewrite with Arr; reflexivity.
Qed.

Hint Rewrite upd0 natToWord_wordToNat DepList.pf_list_simpl : Arr.
Hint Rewrite <- plus_n_O : Arr.

Lemma agreeUpTo_S : forall a b n, agreeUpTo a b (wordToNat n)
  -> n < natToW (length a)
  -> n < natToW (length b)
  -> goodSize (length a)
  -> agreeUpTo (Array.upd a n (Array.sel b n)) b (wordToNat (n ^+ $1)).
  unfold agreeUpTo; intros;
    repeat match goal with
             | [ H : Logic.ex _ |- _ ] => destruct H; intuition; subst
           end; autorewrite with Arr in *.

  exists (x ++ Array.sel (x ++ x1) n :: nil).

  autorewrite with Arr; simpl.
  rewrite H3; intuition eauto.

  destruct x1; simpl in *.
  rewrite H3 in H1.
  unfold natToW in H1; autorewrite with Arr in H1; generalize H1; clear; intros; nomega.

  destruct x0; simpl in *.
  rewrite H3 in H0.
  unfold natToW in H0; autorewrite with Arr in H0; generalize H0; clear; intros; nomega.

  exists x0; autorewrite with Arr; intuition.
  exists x1; autorewrite with Arr; intuition.
Qed.

Hint Extern 1 (_ < _) => congruence.
Hint Resolve agreeUpTo_S.

Lemma agreeUpTo_done : forall a b n,
  agreeUpTo a b n
  -> (length a <= n)%nat
  -> (length b <= n)%nat
  -> a = b.
  unfold agreeUpTo; firstorder; subst.
  rewrite app_length in *.
  assert (length x0 = 0) by omega.
  destruct x0; simpl in *; try omega.
  destruct x1; simpl in *; try omega.
  auto.
Qed.

Require Import Arith.

Lemma le_wordToN : forall (n : nat) (w w' : W),
  w' <= w
  -> w' = n
  -> goodSize n
  -> (n <= wordToNat w)%nat.
  intros; subst.
  destruct (le_lt_dec n (wordToNat w)); auto.
  elimtype False; apply H; clear H.
  red.
  repeat rewrite wordToN_nat.
  rewrite wordToNat_natToWord_idempotent by auto.
  clear H1; nomega.
Qed.

Hint Resolve le_wordToN.

Theorem arrayOk : moduleOk array.
  vcgen; abstract (sep_auto;
    match goal with
      | [ |- himp _ (Array.array ?A _) (Array.array ?B _) ] =>
        replace B with A by (eapply agreeUpTo_done; eauto 10); reflexivity
      | _ => eauto 10
    end).
Qed.
