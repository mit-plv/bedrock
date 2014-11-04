Set Implicit Arguments.

Section TopSection.

  Require Import GoodModule.

  Open Scope bool_scope.
  Notation "! b" := (negb b) (at level 35).

  Definition is_good_module_name s := ! (prefix "_" s).

  Lemma is_good_module_name_sound : forall s, is_good_module_name s = true -> IsGoodModuleName s.
    unfold IsGoodModuleName, is_good_module_name.
    intros.
    Require Import Bool.
    eapply negb_true_iff in H; eauto.
  Qed.

End TopSection.
