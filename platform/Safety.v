Require Import Bedrock PreAutoSep Sys.
Import XCAP.


Section OpSem.
  Variable m : module.
  Variable stn : settings.
  Variable prog : program.

  Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
    -> Labels stn l2 = Some w
    -> l1 = l2.

  Definition labelSys (l : LabelMap.key) (pre : assert) :=
    l = ("sys", Global "abort")
    /\ pre = Precondition abortS None.

  Hypothesis impSys :
    LabelMap.fold (fun l pre P => labelSys l pre /\ P) (Imports m) True.

  Lemma preserve : forall (ls : list (LabelMap.key * assert)) Q,
    fold_left (fun P p => labelSys (fst p) (snd p) /\ P) ls Q
    -> Q.
    induction ls; simpl in *; intuition.
    apply IHls in H; tauto.
  Qed.

  Theorem impSys' : forall l pre, LabelMap.MapsTo l pre (Imports m)
    -> labelSys l pre.
    rewrite LabelMap.fold_1 in impSys; intros.
    apply LabelMap.elements_1 in H.
    generalize dependent True.
    clear impSys; induction H; simpl in *; intuition.

    hnf in H; simpl in H; intuition subst.
    apply preserve in impSys; tauto.

    eauto.
  Qed.    

  Hypothesis agree : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
    -> exists w, Labels stn l = Some w
      /\ prog w = Some bl.

  Hypothesis agreeImp : forall l pre, LabelMap.MapsTo l pre (Imports m)
    -> exists w, Labels stn l = Some w
      /\ prog w = None.

  Hypothesis omitImp : forall l w,
    Labels stn ("sys", l) = Some w
    -> prog w = None.

  Hypothesis ok : moduleOk m.

  Hint Constructors reachable sys_step.

  Lemma reachable_sys : forall st st',
    sys_reachable stn prog st st'
    -> reachable stn prog st st'
    \/ (reachable stn prog st st'
      /\ Labels stn ("sys", Global "abort") = Some (fst st')).
    induction 1; intuition.

    destruct H; eauto.

    destruct H; eauto.
  Qed.

  Lemma safe_sys : forall st,
    safe stn prog st
    -> sys_safe stn prog st.
    unfold sys_safe; post.
    apply reachable_sys in H0; post.

    specialize (H _ H1).
    case_eq (step stn prog st'); intuition eauto.

    specialize (H _ H0).
    unfold step in H.
    apply omitImp in H2.
    rewrite H2 in *.
    tauto.
  Qed.

  Theorem safety : forall st mn g pre, LabelMap.MapsTo (mn, Global g) pre (Exports m)
    -> Labels stn (mn, Global g) = Some (fst st)
    -> interp (specs0 m stn) (pre (stn, snd st))
    -> sys_safe stn prog st.
    intros; hnf; intros.

    apply (ExportsSound ok) in H; destruct H.

    apply reachable_sys in H2; post.
    eapply safety'' in H3; eauto.
    post.

    specialize (impSys' _ _ H4); intro.
    hnf in H2; intuition subst.
    apply agreeImp in H4; post; subst.
    eauto.
    case_eq (step stn prog st'); intros; eauto; congruence.
    
    eauto.
  Qed.
End OpSem.
