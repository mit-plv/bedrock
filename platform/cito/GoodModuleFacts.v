Set Implicit Arguments.

Section TopSection.

  Require Import GoodModule.

  Open Scope bool_scope.
  Notation "! b" := (negb b) (at level 35).

  Definition GoodModuleName_bool s := ! (prefix "_" s).

  Lemma GoodModuleName_bool_sound : forall s, GoodModuleName_bool s = true -> IsGoodModuleName s.
    unfold IsGoodModuleName, GoodModuleName_bool.
    intros.
    Require Import Bool.
    eapply negb_true_iff in H; eauto.
  Qed.

End TopSection.
