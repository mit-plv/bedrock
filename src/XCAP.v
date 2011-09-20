(* An adaptation of Ni & Shao's XCAP program logic *)

Require Import String.

Require Import Word IL LabelMap PropX.

Set Implicit Arguments.


(* The type of basic block preconditions (assertions) *)
Definition prop := PropX W state.
Definition assert := state -> prop.


(* A self-contained unit of code *)
Record module := {
  Imports : LabelMap.t assert;
  (* Which other blocks do we assume are available, and with what preconditions? *)
  Blocks : LabelMap.t (assert * block)
  (* The blocks that we provide, with precondition and code for each *)
}.

(* What must be verified for an individual block? *)
Definition blockOk (imps : LabelMap.t assert) (pre : assert) (bl : block) :=
  forall stn specs, (forall l pre, LabelMap.MapsTo l pre imps
    -> specs (Labels stn l) = Some pre)
    -> forall st, interp specs (pre st) -> exists st', evalBlock stn st bl = Some st'
      /\ exists l, Labels stn l = fst st'
        /\ exists pre', LabelMap.MapsTo l pre' imps
          /\ interp specs (pre' (snd st')).

Require FMapFacts.

Module LabelFacts := FMapFacts.WFacts_fun(LabelKey)(LabelMap).

Section moduleOk.
  Variable m : module.

  (* Calculate preconditions of all labels that are legal to mention. *)
  Definition allPreconditions := LabelMap.fold (fun l x m =>
    LabelMap.add l (fst x) m) (Blocks m) (Imports m).

  (* What must be verified for a full module? *)
  Definition moduleOk :=
    forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
      -> blockOk allPreconditions pre bl.

  (** Safety theorem *)

  Hypothesis closed : LabelMap.cardinal (Imports m) = 0.

  Hint Constructors SetoidList.InA.

  Lemma allPreconditions_just_blocks' : forall l pre mp,
    LabelMap.MapsTo l pre (LabelMap.fold (fun l x m => LabelMap.add l (fst x) m) (Blocks m) mp)
    -> LabelMap.MapsTo l pre mp
      \/ exists bl, LabelMap.MapsTo l (pre, bl) (Blocks m).
    clear closed; intros.
    rewrite LabelMap.fold_1 in H.
    apply LabelMap.elements_1 in H.
    assert (SetoidList.InA (@LabelMap.eq_key_elt _) (l, pre) (LabelMap.elements mp)
      \/ exists bl, SetoidList.InA (@LabelMap.eq_key_elt _) (l, (pre, bl)) (LabelMap.elements (Blocks m))).
    generalize dependent mp.
    induction (LabelMap.elements (Blocks m)); intuition; simpl in *; eauto.

    specialize (IHl0 _ H); clear H.
    destruct IHl0 as [ | [ ] ]; intuition.
    apply LabelMap.elements_2 in H.
    apply (proj1 (LabelFacts.add_mapsto_iff _ _ _ _ _)) in H; intuition; subst.
    right; eexists.
    apply SetoidList.InA_cons_hd; hnf; simpl; eauto.
    apply LabelMap.elements_1 in H1.
    eauto.
    eauto.

    intuition; eauto.
    apply LabelMap.elements_2 in H1; eauto.
    destruct H1.
    apply LabelMap.elements_2 in H0; eauto.
  Qed.

  Lemma allPreconditions_just_blocks : forall l pre, LabelMap.MapsTo l pre allPreconditions
    -> exists bl, LabelMap.MapsTo l (pre, bl) (Blocks m).
    intros.
    apply allPreconditions_just_blocks' in H; firstorder.

    rewrite LabelMap.cardinal_1 in closed.
    apply LabelMap.elements_1 in H.
    destruct (LabelMap.elements (Imports m)); simpl in *.
    inversion H.
    discriminate.
  Qed.

  Variable stn : settings.
  Variable prog : program.

  Hypothesis inj : forall l1 l2, Labels stn l1 = Labels stn l2
    -> l1 = l2.

  Hypothesis agree : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
    -> prog (Labels stn l) = Some bl.

  Hypothesis ok : moduleOk.

  Definition specs : codeSpec W state := fun w =>
    LabelMap.fold (fun l p pre =>
      match pre with
        | Some _ => pre
        | None => if weq w (Labels stn l)
          then Some (fst p)
          else pre
      end) (Blocks m) None.

  Theorem InA_weaken : forall A (P : A -> A -> Prop) (x : A) (ls : list A),
    SetoidList.InA P x ls
    -> forall (P' : A -> A -> Prop) x',
      (forall y, P x y -> P' x' y)
      -> SetoidList.InA P' x' ls.
    induction 1; simpl; intuition.
  Qed.

  Lemma specsOk : forall l pre, LabelMap.MapsTo l pre allPreconditions
    -> specs (Labels stn l) = Some pre.
    unfold specs; intros.

    destruct (allPreconditions_just_blocks H); clear H.

    apply LabelMap.elements_1 in H0.
    rewrite LabelMap.fold_1.
    generalize (LabelMap.elements_3w (Blocks m)).
    induction (LabelMap.elements (Blocks m)); simpl in *.
    inversion H0.

    destruct (weq (Labels stn l) (Labels stn (fst a))).
    inversion H0; clear H0; subst.
    hnf in H1; simpl in H1; intuition; subst.
    destruct a; simpl in *; subst; simpl in *.
    clear.
    induction l0; simpl; intuition.

    inversion 1; subst.
    apply inj in e; subst.
    elimtype False.
    apply H3; clear H3.
    eapply InA_weaken; eauto.
    intros.
    hnf in H0; simpl in H0; intuition.

    inversion H0; clear H0; subst.
    hnf in H1; simpl in H1; intuition.
    subst; tauto.
    inversion 1; auto.
  Qed.

  Lemma safety' : forall st' st'', reachable stn prog st' st''
    -> forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
      -> forall st, interp specs (pre st)
        -> st' = (Labels stn l, st)
        -> exists l', Labels stn l' = fst st''
          /\ exists pre', exists bl', LabelMap.MapsTo l' (pre', bl') (Blocks m)
            /\ interp specs (pre' (snd st'')).
    induction 1; simpl; intuition; subst; simpl in *.
    eauto 6.

    specialize (ok H1).
    red in ok.
    specialize (@ok stn _ specsOk _ H2).
    destruct ok; clear ok; intuition.
    destruct H5; intuition.
    destruct H6; intuition.
    apply allPreconditions_just_blocks in H6; destruct H6.
    eapply IHreachable; eauto.
    unfold step in H; simpl in H.
    rewrite (agree H1) in H.
    rewrite H in H4.
    injection H4; clear H4; intros; subst.
    destruct x; simpl in *; congruence.
  Qed.

  Theorem safety'' : forall st st', reachable stn prog st st'
    -> forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
      -> fst st = Labels stn l -> interp specs (pre (snd st))
      -> step stn prog st' <> None.
    induction 1; simpl; intuition.

    unfold step in H2.
    rewrite H0 in H2.
    rewrite (agree H) in H2.
    specialize (ok H stn specsOk _ H1).
    destruct ok; intuition.
    congruence.

    specialize (ok H1 stn specsOk _ H3).
    destruct ok; clear ok; intuition.
    destruct H7; intuition.
    destruct H8; intuition.
    apply allPreconditions_just_blocks in H8.
    destruct H8.

    unfold step in H.
    rewrite H2 in H.
    rewrite (agree H1) in H.
    rewrite H in H6; injection H6; clear H H6; intros; subst.

    eauto.
  Qed.

  Theorem safety : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
    -> forall st, interp specs (pre st) -> safe stn prog (Labels stn l, st).
    unfold safe; intros; eapply safety''; eauto.
  Qed.
End moduleOk.
