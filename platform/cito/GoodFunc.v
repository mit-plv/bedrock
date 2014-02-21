Set Implicit Arguments.

Require Import Wf.
Export Wf.

Section TopSection.

  Require Import Notations.
  Local Open Scope stmt.
  Require Import SyntaxFunc.
  Require CompileStmtSpec.
  Require Import GetLocalVars.
  Require Import Depth.

  Definition GoodFunc f := 
    NoDup (ArgVars f) /\ 
    NoUninitialized (ArgVars f) (RetVar f) (Body f) /\
    let s := Body f in 
    CompileStmtSpec.syn_req (ArgVars f ++ get_local_vars s (ArgVars f) (RetVar f)) (depth s) s.

  Hint Constructors NoDup.

  Lemma NoDup_app : forall A (ls2 ls1 : list A),
    NoDup ls1
    -> NoDup ls2
    -> (forall x, In x ls1 -> ~In x ls2)
    -> NoDup (ls1 ++ ls2).
    induction 1; simpl; intuition.
    constructor; auto.
    intro.
    apply in_app_or in H4; intuition eauto.
    eauto.
  Qed.

  Lemma In_InA : forall A (x : A) ls,
    List.In x ls
    -> SetoidList.InA (@Logic.eq A) x ls.
    induction ls; simpl; intuition.
  Qed.

  Lemma NoDupA_NoDup : forall A ls,
    SetoidList.NoDupA (@Logic.eq A) ls
    -> List.NoDup ls.
    induction 1; intuition auto using In_InA.
  Qed.

  Lemma InA_In : forall A (x : A) ls,
    SetoidList.InA (@Logic.eq A) x ls
    -> List.In x ls.
    induction 1; simpl; intuition.
  Qed.

  Lemma got_em_all : forall x to_remove acc,
    In x to_remove \/ ~StringSet.StringSet.In x acc
    -> ~In x
    (StringSet.StringSet.elements
      (fold_left
        (fun (acc : StringSet.StringSet.t) (x0 : StringSet.StringSet.elt) =>
          StringSet.StringSet.remove x0 acc) to_remove
        acc)).
    induction to_remove; simpl; intuition (subst; eauto).
    apply In_InA in H0.
    apply StringSet.StringSet.elements_2 in H0.
    tauto.
    apply IHto_remove in H0.
    tauto.
    right; intuition.
    apply StringSet.StringFacts.remove_iff in H; tauto.
    apply IHto_remove in H0; intuition.
    right; intuition.
    apply StringSet.StringFacts.remove_iff in H; tauto.
  Qed.

  Require Import GetLocalVars.
  Lemma GoodFunc_NoDup_vars : forall f, GoodFunc f -> forall s r, NoDup (ArgVars f ++ get_local_vars s (ArgVars f) r).
    unfold GoodFunc; intuition.
    apply NoDup_app; auto.
    apply NoDupA_NoDup.
    apply StringSet.StringSet.elements_3w.
    intros.
    apply got_em_all; auto.
  Qed.

End TopSection.

Require Import ADT.

Module Make (Import E : ADT).

  Module Import WfMake := Wf.Make E.
  Require Import Semantics.
  Import SemanticsMake.

  Require Import GeneralTactics.

  Section TopSection.

    Lemma GoodFunc_Safe : forall f, GoodFunc f -> let s := Body f in forall fs vs h, Safe fs s (vs, h) -> forall vs', agree_in vs vs' (ArgVars f) -> Safe fs s (vs', h).
      intros.
      eapply NoUninitialized_Safe; eauto.
      destruct H; openhyp; eauto.
    Qed.

    Lemma GoodFunc_RunsTo : forall f, GoodFunc f -> let s := Body f in forall fs vs h v', RunsTo fs s (vs, h) v' -> forall vs', agree_in vs vs' (ArgVars f) -> exists vs'', RunsTo fs s (vs', h) (vs'', snd v') /\ sel vs'' (RetVar f) = sel (fst v') (RetVar f).
      intros.
      eapply NoUninitialized_RunsTo in H0; eauto.
      destruct H; intuition.
    Qed.
    
  End TopSection.

End Make.
