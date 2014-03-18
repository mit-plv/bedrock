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

  Definition goodSize_bool n := proj1_sig (Sumbool.bool_of_sumbool (Malloc.goodSize_dec n)).

  Fixpoint wellformed_bool s :=
    match s with
      | Syntax.Call _ _ args => goodSize_bool (2 + length args)
      | Syntax.Skip => true
      | Syntax.Seq a b => wellformed_bool a && wellformed_bool b
      | Syntax.If _ a b => wellformed_bool a && wellformed_bool b
      | Syntax.While _ body => wellformed_bool body
      | Syntax.Assign _ _ => true
      | Syntax.Label _ _ => true
    end.

  Require Import GetLocalVars.

  Definition NoUninitialized_bool (f : FuncCore) := true.

  Require Import Depth.
  Require Import GoodModuleFacts.
  Require Import ListFacts3.

  Definition GoodFunc_bool f := 
    let body := Body f in 
    let local_vars := get_local_vars body (ArgVars f) (RetVar f) in
    let all_vars := ArgVars f ++ local_vars in
    NoDup_bool string_bool (ArgVars f) &&
    NoUninitialized_bool f &&
    wellformed_bool body &&
    goodSize_bool (length local_vars + depth body).

  Definition GoodFuncs_bool fs := forallb GoodFunc_bool fs.

  Definition GoodModule_bool (m : Module) :=
    GoodModuleName_bool (MName m) &&
    GoodFuncs_bool (map Core (Funcs m)) &&
    NoDup_bool string_bool (map FName (Funcs m)).

  Require Import Bool.
  Require Import GeneralTactics.
  Require Import GeneralTactics2.

  Require Import Program.Basics.
  Require Import GoodFunc.
(*
  Lemma NoUninitialized_bool_sound : forall f, NoUninitialized_bool f = true -> NoUninitialized (ArgVars f) (RetVar f) (Body f).
  Qed.

  Require Import WellFormed.

  Lemma goodSize_bool_sound : forall n, goodSize_bool n = true -> goodSize n.
    intros.
    unfold goodSize_bool in *.
    destruct (Malloc.goodSize_dec n); simpl in *; intuition.
  Qed.

  Hint Constructors args_not_too_long.

  Lemma wellformed_bool_sound : forall s, wellformed_bool s = true -> wellformed s.
    unfold wellformed.
    induction s; simpl; intuition eauto.
    eapply andb_true_iff in H; openhyp; eauto.
    eapply andb_true_iff in H; openhyp; eauto.
    econstructor.
    eapply goodSize_bool_sound; eauto.
  Qed.

  Lemma GoodFunc_bool_sound : forall f, GoodFunc_bool f = true -> GoodFunc f.
    unfold GoodFunc_bool.
    intros.
    repeat (eapply andb_true_iff in H; openhyp).
    econstructor.
    eapply NoDup_bool_string_eq_sound; eauto.
    split.
    eapply NoUninitialized_bool_sound; eauto.
    split.
    eapply wellformed_bool_sound; eauto.
    eapply goodSize_bool_sound; eauto.
  Qed.

  Lemma GoodFuncs_bool_sound : forall ls, GoodFuncs_bool (map Core ls) = true -> Forall (compose GoodFunc Core) ls.
    intros.
    unfold GoodFuncs_bool in *.
    eapply Forall_forall.
    intros.
    eapply forallb_forall in H.
    2 : eapply in_map; eauto.
    unfold compose.
    eapply GoodFunc_bool_sound; eauto.
  Qed.

  Lemma GoodModule_bool_sound : forall m, GoodModule_bool m = true -> IsGoodModule m.
    intros.
    unfold GoodModule_bool in *.
    destruct m; simpl in *.
    eapply andb_true_iff in H.
    openhyp.
    eapply andb_true_iff in H.
    openhyp.
    econstructor; simpl.
    eapply GoodModuleName_bool_sound; eauto.
    split.
    eapply GoodFuncs_bool_sound; eauto.
    eapply NoDup_bool_string_eq_sound; eauto.
  Qed.
*)
End TopSection.