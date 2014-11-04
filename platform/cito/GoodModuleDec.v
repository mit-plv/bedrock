Set Implicit Arguments.

Section TopSection.

  Require Import IsGoodModule.

  Notation MName := SyntaxModule.Name.
  Notation FName := SyntaxFunc.Name.
  Notation Funcs := SyntaxModule.Functions.

  Require Import GoodModule.

  Open Scope bool_scope.
  Notation "! b" := (negb b) (at level 35).

  Require Import List.

  Require Import SyntaxModule.

  Local Open Scope N_scope.

  Definition is_good_size (n : nat) :=
    match N.of_nat n ?= Npow2 32 with
      | Datatypes.Lt => true
      | _ => false
    end. 

  Fixpoint is_arg_len_ok s :=
    match s with
      | Syntax.Call _ _ args => is_good_size (2 + length args)
      | Syntax.Skip => true
      | Syntax.Seq a b => is_arg_len_ok a && is_arg_len_ok b
      | Syntax.If _ a b => is_arg_len_ok a && is_arg_len_ok b
      | Syntax.While _ body => is_arg_len_ok body
      | Syntax.Assign _ _ => true
      | Syntax.Label _ _ => true
    end.

  Require Import GetLocalVars.

  Require Import Depth.
  Require Import ListFacts3.
  Require Import ListFacts4.
  Require Import NoUninitDec.
  Require Import List.

  Definition is_good_func f := 
    let body := Body f in 
    let local_vars := get_local_vars body (ArgVars f) (RetVar f) in
    let all_vars := ArgVars f ++ local_vars in
    is_no_dup (ArgVars f) &&
    is_no_uninited f &&
    is_arg_len_ok body &&
    is_good_size (length local_vars + depth body).

  Definition is_good_funcs fs := forallb is_good_func fs.

  Require Import NameDecoration.

  Definition is_good_module (m : Module) :=
    is_good_module_name (MName m) &&
    is_good_funcs (map Core (Funcs m)) &&
    is_no_dup (map FName (Funcs m)).

  Require Import Bool.
  Require Import GeneralTactics.
  Require Import GeneralTactics2.

  Require Import Program.Basics.
  Require Import GoodFunc.

  Require Import WellFormed.

  Lemma is_good_size_sound : forall n, is_good_size n = true -> goodSize n.
    intros.
    unfold is_good_size in *.
    destruct (ZArith_dec.Dcompare_inf (N.of_nat n ?= Npow2 32)) as [ [Hc | Hc] | Hc ]; rewrite Hc in *.
    discriminate.
    eapply N.compare_lt_iff in Hc; eauto.
    discriminate.
  Qed.

  Hint Constructors args_not_too_long.

  Lemma is_arg_len_ok_sound : forall s, is_arg_len_ok s = true -> wellformed s.
    unfold wellformed.
    induction s; simpl; intuition eauto.
    eapply andb_true_iff in H; openhyp; eauto.
    eapply andb_true_iff in H; openhyp; eauto.
    econstructor.
    eapply is_good_size_sound; eauto.
  Qed.

  Lemma is_good_func_sound : forall f, is_good_func f = true -> GoodFunc f.
    unfold is_good_func.
    intros.
    repeat (eapply andb_true_iff in H; openhyp).
    econstructor.
    eapply is_no_dup_sound; eauto.
    split.
    eapply is_no_uninited_sound; eauto.
    split.
    eapply is_arg_len_ok_sound; eauto.
    eapply is_good_size_sound; eauto.
  Qed.

  Lemma is_good_funcs_sound : forall ls, is_good_funcs (map Core ls) = true -> Forall (compose GoodFunc Core) ls.
    intros.
    unfold is_good_funcs in *.
    eapply Forall_forall.
    intros.
    eapply forallb_forall in H.
    2 : eapply in_map; eauto.
    unfold compose.
    eapply is_good_func_sound; eauto.
  Qed.

  Lemma is_good_module_sound : forall m, is_good_module m = true -> IsGoodModule m.
    intros.
    unfold is_good_module in *.
    destruct m; simpl in *.
    eapply andb_true_iff in H.
    openhyp.
    eapply andb_true_iff in H.
    openhyp.
    econstructor; simpl.
    eapply is_good_module_name_sound; eauto.
    split.
    eapply is_good_funcs_sound; eauto.
    eapply is_no_dup_sound; eauto.
  Qed.

End TopSection.