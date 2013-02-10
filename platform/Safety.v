Require Import Bedrock PreAutoSep Sys.
Import XCAP.


Section OpSem.
  Variable m : module.
  Variable stn : settings.
  Variable prog : program.

  Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
    -> Labels stn l2 = Some w
    -> l1 = l2.

  Hypothesis agree : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
    -> exists w, Labels stn l = Some w
      /\ prog w = Some bl.

  Hypothesis agreeImp : forall l pre, LabelMap.MapsTo l pre (Imports m)
    -> exists w, Labels stn l = Some w
      /\ prog w = None
      /\ l = ("sys", Global "abort")
      /\ pre = Precondition abortS None.

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

  Theorem safety : forall st l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
    -> Labels stn l = Some (fst st)
    -> interp (specs0 m stn) (pre (stn, snd st))
    -> sys_safe stn prog st.
    intros; hnf; intros.

    apply reachable_sys in H2; post.

    eapply safety'' in H3; eauto.
    post.
    apply agreeImp in H4; post; subst.
    eauto.
    case_eq (step stn prog st'); intros; eauto; congruence.
    
    intros.
    apply agreeImp in H2.
    post; eauto.

    eauto.
  Qed.
End OpSem.
