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
    -> exists w, Labels stn l = Some w
      /\ specs w = Some pre)
    -> forall st, interp specs (pre st) -> exists st', evalBlock stn st bl = Some st'
      /\ exists l, Labels stn l = Some (fst st')
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

  Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
    -> Labels stn l2 = Some w
    -> l1 = l2.

  Hypothesis agree : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
    -> exists w, Labels stn l = Some w
      /\ prog w = Some bl.

  Hypothesis ok : moduleOk.

  Definition specs : codeSpec W state := fun w =>
    LabelMap.fold (fun l p pre =>
      match pre with
        | Some _ => pre
        | None => match Labels stn l with
                    | None => None
                    | Some w' => if weq w w'
                      then Some (fst p)
                      else pre
                  end
      end) (Blocks m) None.

  Theorem InA_weaken : forall A (P : A -> A -> Prop) (x : A) (ls : list A),
    SetoidList.InA P x ls
    -> forall (P' : A -> A -> Prop) x',
      (forall y, P x y -> P' x' y)
      -> SetoidList.InA P' x' ls.
    induction 1; simpl; intuition.
  Qed.

  Lemma specsOk : forall l pre, LabelMap.MapsTo l pre allPreconditions
    -> exists w, Labels stn l = Some w
      /\ specs w = Some pre.
    unfold specs; intros.

    destruct (allPreconditions_just_blocks H); clear H.

    destruct (agree H0); intuition.
    do 2 esplit; eauto.

    apply LabelMap.elements_1 in H0.
    rewrite LabelMap.fold_1.
    generalize (LabelMap.elements_3w (Blocks m)).
    generalize (fun l pre bl H => @agree l pre bl (LabelMap.elements_2 H)); clear agree; intro agree.
    induction (LabelMap.elements (Blocks m)); simpl in *.
    inversion H0.

    case_eq (Labels stn (fst a)); intros.

    destruct (weq x0 w); subst.
    inversion H0; clear H0; subst.
    hnf in H5; simpl in H5; intuition; subst.
    destruct a; simpl in *; subst; simpl in *.
    clear.
    induction l0; simpl; intuition.

    inversion H3; subst.
    eapply inj in H; eauto; subst.
    elimtype False.
    apply H6; clear H6.
    eapply InA_weaken; eauto.
    intros.
    subst.
    hnf in H0; simpl in H0; intuition.

    inversion H0; clear H0; subst.
    hnf in H5; simpl in H5; intuition.
    unfold LabelMap.key in H.
    congruence.
    inversion H3; eauto.

    specialize (@agree (fst a) (fst (snd a)) (snd (snd a))).
    destruct agree.
    apply SetoidList.InA_cons; left.
    hnf; simpl.
    intuition.
    unfold LabelMap.key; simpl.
    destruct (snd (A := label) a); auto.
    intuition; congruence.
  Qed.

  Lemma safety' : forall st' st'', reachable stn prog st' st''
    -> forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
      -> forall st, interp specs (pre st)
        -> forall w, Labels stn l = Some w
          -> st' = (w, st)
        -> exists l', Labels stn l' = Some (fst st'')
          /\ exists pre', exists bl', LabelMap.MapsTo l' (pre', bl') (Blocks m)
            /\ interp specs (pre' (snd st'')).
    induction 1; simpl; intuition; subst; simpl in *.
    eauto 6.

    specialize (ok H1).
    red in ok.
    specialize (@ok stn _ specsOk _ H2).
    destruct ok; clear ok; intuition.
    destruct H6; intuition.
    destruct H7; intuition.
    apply allPreconditions_just_blocks in H7; destruct H7.
    eapply IHreachable; eauto.
    unfold step in H; simpl in H.
    destruct (agree H1); intuition.
    rewrite H9 in H3; injection H3; clear H3; intros; subst.
    rewrite H10 in H.
    rewrite H5 in H.
    injection H; clear H; intros; subst.
    destruct st'; simpl in *; congruence.
  Qed.

  Theorem safety'' : forall st st', reachable stn prog st st'
    -> forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
      -> Some (fst st) = Labels stn l -> interp specs (pre (snd st))
      -> step stn prog st' <> None.
    induction 1; simpl; intuition.

    unfold step in H2.
    destruct (agree H); intuition.
    rewrite <- H0 in H4; injection H4; clear H4; intros; subst.
    rewrite H5 in H2.
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
    destruct (agree H1); intuition.
    rewrite <- H2 in H10; injection H10; clear H10; intros; subst.
    rewrite H11 in H.
    rewrite H in H6; injection H6; clear H H6; intros; subst.

    eauto.
  Qed.

  Theorem safety : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
    -> forall w, Labels stn l = Some w
      -> forall st, interp specs (pre st)
        -> safe stn prog (w, st).
    unfold safe; intros; eapply safety''; eauto.
  Qed.
End moduleOk.
