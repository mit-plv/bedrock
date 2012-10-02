Require Import Nomega NArith Word PropX PropXTac Memory SepIL IL.

Require Import sep.Array.

Lemma updN_length : forall ls a v,
  length (updN ls a v) = length ls.
  induction ls; simpl; intuition.
  destruct a0; simpl; auto.
Qed.

Lemma upd_length : forall ls a v,
  length (upd ls a v) = length ls.
  intros; apply updN_length.
Qed.

Hint Resolve upd_length updN_length.
Hint Rewrite upd_length updN_length : sepFormula.

Inductive containsArray : HProp -> list W -> Prop :=
| CABase : forall ls p, containsArray (array ls p) ls
| CALeft : forall P Q ls, containsArray P ls
  -> containsArray (SEP.ST.star P Q) ls
| CARight : forall P Q ls, containsArray Q ls
  -> containsArray (SEP.ST.star P Q) ls
| CAUpd : forall P ls a v, containsArray P (upd ls a v)
  -> containsArray P ls.

Hint Constructors containsArray.

Theorem containsArray_bound' : forall cs P stn ls,
  containsArray P ls
  -> forall st, interp cs (P stn st)
    -> (length ls < pow2 32)%nat.
  induction 1; intros.
  eapply array_bound; eauto.
  propxFo; eauto.
  propxFo; eauto.
  rewrite upd_length in *; eauto.
Qed.

Theorem containsArray_bound : forall cs P stn ls st,
  interp cs (![P] (stn, st))
  -> containsArray P ls
  -> (length ls < pow2 32)%nat.
  rewrite sepFormula_eq; intros; eapply containsArray_bound'; eauto.
Qed.

Hint Resolve containsArray_bound.

Theorem containsArray_goodSize : forall cs P stn ls st,
  interp cs (![P] (stn, st))
  -> containsArray P ls
  -> goodSize (length ls).
  intros; unfold goodSize.
  apply Nlt_in.
  rewrite Npow2_nat.
  rewrite Nat2N.id.
  eapply containsArray_bound; eauto.
Qed.

Hint Resolve containsArray_goodSize.

Require Import NArith Nomega.

Lemma bound_N_nat : forall n,
  (n < pow2 32)%nat
  -> (N.of_nat n < Npow2 32)%N.
  intros; apply Nlt_in; rewrite Npow2_nat; repeat rewrite Nat2N.id; assumption.
Qed.

Hint Resolve bound_N_nat.

Lemma sel_selN : forall ls (a : nat),
  (a < pow2 32)%nat
  -> sel ls (natToW a) = selN ls a.
  unfold sel; intros; rewrite wordToNat_natToWord_idempotent; auto.
Qed.

Lemma upd_updN : forall ls (a : nat) v,
  (a < pow2 32)%nat
  -> upd ls (natToW a) v = updN ls a v.
  unfold upd; intros; rewrite wordToNat_natToWord_idempotent; auto.
Qed.

Lemma pow2_pos : forall sz, (0 < pow2 sz)%nat.
  induction sz; simpl; intuition.
Qed.

Hint Immediate pow2_pos.

Hint Extern 1 (_ < _)%nat => omega.

Hint Rewrite roundTrip_0 roundTrip_1 wordToNat_natToWord_idempotent using assumption : Arr.

Section next.
  Hint Rewrite wordToN_nat Npow2_nat : N.

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
End next.

Hint Resolve next.

Require Import List.

Lemma updN_app : forall b v a,
  Array.updN (a ++ b) (Datatypes.length a) v
  = a ++ Array.updN b 0 v.
  induction a; simpl; intuition congruence.
Qed.

Hint Rewrite updN_app : Arr.

Lemma upd_app : forall a b v,
  goodSize (length a)
  -> Array.upd (a ++ b) (natToW (length a)) v
  = a ++ Array.upd b (natToW 0) v.
  unfold Array.upd; intros; autorewrite with Arr; auto.
Qed.

Hint Rewrite app_length using solve [ auto ] : Arr.

Section goodSize_wordToNat.
  Hint Rewrite wordToN_nat Npow2_nat : N.

  Lemma goodSize_wordToNat : forall (w : W),
    goodSize (wordToNat w).
    intros; specialize (wordToNat_bound w); intros; unfold goodSize.
    unfold W in *; generalize dependent 32; intros; nomega.
  Qed.
End goodSize_wordToNat.

Hint Resolve goodSize_wordToNat.

Lemma upd_app' : forall a b v w,
  length a = wordToNat w
  -> Array.upd (a ++ b) w v
  = a ++ Array.upd b (natToW 0) v.
  intros; assert (natToWord 32 (length a) = natToWord 32 (wordToNat w)) by congruence;
    rewrite natToWord_wordToNat in *; subst; apply upd_app.
  rewrite H; auto.
Qed.

Hint Rewrite upd_app' using assumption : Arr.

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
  -> Array.sel (ws ++ w :: ws') (natToW (length ws)) = w.
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
  Array.upd (w :: ws) (natToW 0) v = v :: ws.
  intros; unfold Array.upd; autorewrite with Arr; reflexivity.
Qed.

Hint Rewrite upd0 natToWord_wordToNat DepList.pf_list_simpl : Arr.
Hint Rewrite <- plus_n_O : Arr.

Require Import Arith.

Lemma le_wordToN : forall (n : nat) (w w' : W),
  w' <= w
  -> w' = natToW n
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
