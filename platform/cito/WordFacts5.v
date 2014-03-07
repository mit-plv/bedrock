Set Implicit Arguments.

Require Import WordFacts WordFacts2 WordFacts3 WordFacts4.

Lemma wmult_natToW_comm : forall a b, $ a ^* $ b = natToW (a * b).
  symmetry.
  eapply natToWord_mult.
Qed.

Lemma wle_0_eq : forall w : W, w <= $0 -> w = $0.
  intros.
  unfold wlt in *.
  destruct (N.eq_0_gt_0_cases (wordToN w)).
  change (0)%N with (wordToN (natToW 0)) in H0.
  eapply wordToN_inj in H0.
  eauto.
  change (wordToN ($ 0)) with 0%N in H.
  intuition.
Qed.