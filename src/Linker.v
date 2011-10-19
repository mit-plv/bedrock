(* Laying out labels, and generally coming up with final "machine code" programs *)

Require Import NArith.

Require Import Nomega Word IL LabelMap XCAP.

Set Implicit Arguments.


Definition labelsOf' (M : LabelMap.t (assert * block)) (acc : (W * ((label -> option W) * (W -> option block))))
  : (label -> option W) * (W -> option block) :=
  snd (LabelMap.fold (fun k (v : assert * block) p => let (_, bl) := v in let '(w, (labels, prog)) := p in
    (natToWord _ 1 ^+ w,
      ((fun k' => if LabelKey.eq_dec k' k then Some w else labels k'),
        (fun w' => if weq w' w then Some bl else prog w'))))
  M acc).

Definition labelsOf (M : LabelMap.t (assert * block)) : (label -> option W) * (W -> option block) :=
  labelsOf' M (wzero _, (fun _ => None, fun _ => None)).

Lemma lt_trans : forall n m o, (n < o)%N -> m = n -> (m < o)%N.
  congruence.
Qed.

Lemma labelsOf'_inj : forall M l1 l2 w w' labels prog,
  let labels' := fst (labelsOf' M (w', (labels, prog))) in
    labels' l1 = Some w
    -> labels' l2 = Some w
    -> (forall l1' l2' w'', labels l1' = Some w'' -> labels l2' = Some w'' -> l1' = l2')
    -> (forall l w'', labels l = Some w'' -> (wordToNat w'' < wordToNat w')%nat)
    -> (wordToN w' + N_of_nat (LabelMap.cardinal M) < Npow2 32)%N
    -> l1 = l2.
  unfold labelsOf'; simpl; intros.
  rewrite LabelMap.fold_1 in *.
  rewrite LabelMap.cardinal_1 in *.
  generalize dependent prog.
  generalize dependent labels.
  generalize dependent w'.
  induction (LabelMap.elements M); simpl; intuition.
  eauto.
  simpl in *.
  eapply IHl; clear IHl; try (apply H || apply H0); simpl; intuition.
  generalize H3; clear.
  unfold wplus, wordBin.
  match goal with
    | [ |- context[wordToN ?N] ] =>
      match N with
        | _~1 => change (wordToN N) with 1%N
      end
  end.
  intro; eapply lt_trans; eauto.
  replace (Npos (P_of_succ_nat (length l))) with (1 + N_of_nat (length l))%N in *.
  replace (wordToN (NToWord 32 (1 + wordToN w'))) with (1 + wordToN w')%N.
  ring.
  rewrite NToWord_nat.
  assert (1 + wordToN w' < 4294967296)%N.

  Lemma lt_rearrange : forall n p m k,
    (n + (p + m) < k)%N
    -> (p + n < k)%N.
    intros; nomega.
  Qed.
  
  eapply lt_rearrange; eauto.

  rewrite nat_of_Nplus.
  change (nat_of_N 1) with 1.
  repeat rewrite wordToN_nat.
  rewrite nat_of_N_of_nat.
  destruct (wordToNat_natToWord 32 (1 + wordToNat w')); intuition.
  rewrite H1.
  rewrite N_of_minus.
  rewrite N_of_plus.
  rewrite N_of_mult.
  change (N_of_nat 1) with 1%N.
  destruct x.
  change (N_of_nat 0) with 0%N.
  rewrite Nmult_0_l.
  clear.
  nomega.
  elimtype False.
  clear H1.

  Lemma contra : forall x b n,
    (n < b)%nat
    -> (S x * b <= n)%nat
    -> False.
    simpl; intros.
    assert (b <= n)%nat.
    generalize dependent (x * b)%nat.
    intros; omega.
    omega.
  Qed.

  eapply contra; [ | eassumption ].
  generalize H; clear; intro.
  rewrite <- Npow2_nat.
  change 1 with (nat_of_N 1) at 1.
  rewrite <- (nat_of_N_of_nat (wordToNat w')).
  rewrite <- nat_of_Nplus.
  apply Nlt_out.
  rewrite wordToN_nat in H.
  apply H.
  clear.
  apply nat_of_N_eq.
  change (nat_of_N (Npos (P_of_succ_nat (length l)))) with (nat_of_P (P_of_succ_nat (length l))).
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ.
  rewrite nat_of_Nplus.
  simpl.
  autorewrite with N; reflexivity.
  
  repeat match goal with
           | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
           | [ H : LabelKey.eq _ _ |- _ ] => hnf in H; subst
         end; auto.
  elimtype False.
  injection H5; clear H5; intro; subst.
  apply H2 in H4; omega.
  elimtype False.
  injection H4; clear H4; intro; subst.
  apply H2 in H5; omega.
  eauto.

  repeat match goal with
           | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
           | [ H : LabelKey.eq _ _ |- _ ] => hnf in H; subst
         end; auto.
  injection H4; clear H4; intro; subst.
  generalize H3; clear; intros.
  apply Nlt_out in H3.
  autorewrite with N in *.
  change (nat_of_N (Npos (P_of_succ_nat (length l)))) with (nat_of_P (P_of_succ_nat (length l))) in H3.
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ in H3.
  rewrite wordToN_nat in H3.
  autorewrite with N in *.
  unfold wplus, wordBin.
  match goal with
    | [ |- context[wordToN ?N] ] =>
      match N with
        | _~1 => change (wordToN N) with 1%N
      end
  end.
  rewrite NToWord_nat.
  rewrite nat_of_Nplus.
  change (nat_of_N 1) with 1.
  rewrite wordToN_nat.
  autorewrite with N.
  destruct (wordToNat_natToWord 32 (1 + wordToNat w'')); intuition.
  rewrite H0; clear H0.
  destruct x.
  omega.
  elimtype False.
  change 4294967296%N with (Npow2 32) in *.
  rewrite Npow2_nat in *.
  eapply contra; [ | eassumption ].
  generalize H3; clear; intro.
  generalize dependent (pow2 32).
  intros; omega.

  apply H2 in H4.
  generalize H3 H4; clear; intros.
  change 4294967296%N with (Npow2 32) in *.  
  unfold wplus, wordBin.
  rewrite NToWord_nat.
  match goal with
    | [ |- context[wordToN ?N] ] =>
      match N with
        | _~1 => change (wordToN N) with 1%N
      end
  end.
  rewrite nat_of_Nplus.
  change (nat_of_N 1) with 1.
  rewrite wordToN_nat.
  autorewrite with N.  
  destruct (wordToNat_natToWord 32 (1 + wordToNat w')); intuition.
  rewrite H0; clear H0.
  destruct x.
  omega.
  elimtype False.
  eapply contra; [ | eassumption ].
  generalize H3; clear; intro.
  apply Nlt_out in H3.
  autorewrite with N in *.
  change (nat_of_N (Npos (P_of_succ_nat (length l)))) with (nat_of_P (P_of_succ_nat (length l))) in H3.  
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ in H3.
  rewrite wordToN_nat in H3.
  autorewrite with N in *.
  rewrite Npow2_nat in *.
  generalize dependent (pow2 32).
  intros; omega.
Qed.

Theorem labelsOf_inj : forall M l1 l2 w, fst (labelsOf M) l1 = Some w
  -> fst (labelsOf M) l2 = Some w
  -> (N_of_nat (LabelMap.cardinal M) < Npow2 32)%N
  -> l1 = l2.
  intros; eapply labelsOf'_inj; eauto; simpl; intuition; discriminate.
Qed.
