Set Implicit Arguments.

Require Import FreeVars.
Require Import StringSet.
Import StringSet.
Require Import Equalities.
Module SK_as_UDT := Make_UDT StringKey.
Require Import FSetFacts1.
Module Import SF1 := UWFacts_fun SK_as_UDT StringSet.
Import P FM.

Definition get_local_vars stmt arg_vars ret_var := 
  elements (diff (add ret_var (free_vars stmt)) (of_list arg_vars)).

Require Import SetoidListFacts.
Require Import GeneralTactics2.

Lemma ret_in_vars : forall arg_vars s r, List.In r (arg_vars ++ get_local_vars s arg_vars r).
  intros; apply List.in_or_app.
  destruct (List.In_dec String.string_dec r arg_vars); try solve [intuition]; intros.
  right.
  unfold get_local_vars; simpl.
  eapply InA_eq_In_iff.
  eapply elements_1.
  eapply diff_iff.
  split.
  eapply add_iff; eauto.
  not_not.
  eapply of_list_spec; eauto.
Qed.
