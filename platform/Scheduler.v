Require Import AutoSep Bags.

Set Implicit Arguments.


Section starL.
  Variable A : Type.
  Variable P : A -> HProp.

  Open Scope Sep_scope.

  Fixpoint starL (ls : list A) : HProp :=
    match ls with
      | nil => Emp
      | x :: ls => P x * starL ls
    end.
End starL.

Section starB.
  Definition bagify (ls : list (W * W)) : bag :=
    fold_left add ls empty.

  Definition predB := W * W -> HProp.
  Variable P : predB.

  Open Scope Sep_scope.

  Definition starB (b : bag) : HProp :=
    Ex ls, [| b %= bagify ls |] * starL P ls.

  Ltac to_himp := repeat intro.
  Ltac from_himp := match goal with
                      | [ |- interp ?specs (?p ?x ?y ---> ?q ?x ?y) ] =>
                        generalize dependent y; generalize dependent x; generalize dependent specs;
                          change (p ===> q)
                    end.

  Theorem starB_empty_bwd : Emp ===> starB empty.
    to_himp; apply existsR with nil; from_himp; sepLemma.
  Qed.

  Lemma exists_starL_fwd : forall A (P : A -> _) Q,
    (Ex x, P x) * Q ===> Ex x, P x * Q.
    sepLemma.
  Qed.

  Lemma equiv_symm : forall b1 b2,
    b1 %= b2
    -> b2 %= b1.
    unfold equiv; firstorder.
  Qed.

  Lemma equiv_trans : forall b1 b2 b3,
    b1 %= b2
    -> b2 %= b3
    -> b1 %= b3.
    unfold equiv; firstorder.
  Qed.

  Lemma bagify_cong : forall ls b1 b2,
    b1 %= b2
    -> fold_left add ls b1 %= fold_left add ls b2.
    induction ls; simpl; intuition.
  Qed.

  Lemma add_something : forall v ls b,
    fold_left add ls (b %+ v) %= fold_left add ls b %+ v.
    induction ls; simpl; intuition.
    eapply equiv_trans; [ | apply IHls ].
    apply bagify_cong; auto.
  Qed.

  Theorem starB_add_bwd : forall b v, starB b * P v ===> starB (b %+ v).
    intros; eapply Himp_trans; [ apply exists_starL_fwd | ]; cbv beta.
    to_himp; apply existsL; intro ls; apply existsR with (v :: ls); from_himp.
    simpl; generalize (starL P ls); generalize (P v); sepLemma.
    unfold bagify in *; simpl.
    apply equiv_symm; eapply equiv_trans; [ apply add_something | ]; auto.
  Qed.

  Lemma exists_starR_bwd : forall P A (Q : A -> _),
    Ex x, P * Q x ===> P * (Ex x, Q x).
    sepLemma.
  Qed.

  Definition W_pair_eq (x y : W * W): {x = y} + {x <> y}.
    refine (match weq (fst x) (fst y) with
              | left _ => match weq (snd x) (snd y) with
                            | left _ => left _
                            | right _ => right _
                          end
              | right _ => right _
            end); abstract (try congruence; destruct x; destruct y; simpl in *; congruence).
  Defined.

  Fixpoint nuke (p : W * W) (ls : list (W * W)) : list (W * W) :=
    match ls with
      | nil => nil
      | p' :: ls => if W_pair_eq p p' then ls else p' :: nuke p ls
    end.

  Lemma starL_del_fwd : forall v ls, In v ls
    -> starL P ls ===> P v * starL P (nuke v ls).
    induction ls; unfold bagify in *; simpl in *; intuition subst.
    destruct (W_pair_eq v v); apply Himp_refl || tauto.
    destruct (W_pair_eq v (a0, b)); subst; try apply Himp_refl.
    simpl.
    eapply Himp_trans.
    apply Himp_star_frame; [ apply Himp_refl | apply H ].
    generalize (starL P (nuke v ls)); generalize (P (a0, b)); generalize (P v); sepLemma.
  Qed.

  Lemma del_something : forall v ls b,
    v %in b
    -> fold_left add ls (b %- v) %= fold_left add ls b %- v.
    induction ls; simpl; intuition.
    eapply equiv_trans; [ | apply IHls ].
    apply bagify_cong; auto.
    auto.
  Qed.

  Lemma bagify_nuke' : forall v ls, In v ls
    -> forall b, fold_left add (nuke v ls) b %= fold_left add ls b %- v.
    induction ls; simpl; intuition subst.
    destruct (W_pair_eq v v); intuition.
    eapply equiv_trans; [ | apply del_something ].
    apply bagify_cong; auto.
    auto.
    destruct (W_pair_eq v (a0, b)); subst.
    eapply equiv_trans; [ | apply del_something ].
    apply bagify_cong; auto.
    auto.
    simpl; auto.
  Qed.

  Lemma bagify_nuke : forall v ls, In v ls
    -> bagify (nuke v ls) %= bagify ls %- v.
    intros; apply bagify_nuke'; auto.
  Qed.

  Lemma bagify_In' : forall v ls b b',
    v %in b
    -> b %= fold_left add ls b'
    -> In v ls \/ v %in b'.
    unfold bagify; induction ls; simpl; intuition.
    eapply IHls in H; [ | eauto ].
    intuition (eauto; bags).
  Qed.

  Lemma bagify_In : forall v ls b,
    v %in b
    -> b %= bagify ls
    -> In v ls.
    intros.
    eapply bagify_In' in H0; eauto.
    intuition bags.
  Qed.    

  Hint Resolve bagify_In bagify_nuke.

  Theorem starB_del_fwd : forall b v, v %in b
    -> starB b ===> P v * starB (b %- v).
    intros; eapply Himp_trans; [ | apply exists_starR_bwd ]; cbv beta.
    to_himp; apply existsL; intro ls; apply existsR with (nuke v ls).
    specialize (starL_del_fwd v ls);
      generalize (starL P ls); generalize (P v); generalize (starL P (nuke v ls)).
    intros; from_himp.
    sepLemma.
    eapply equiv_trans; [ | apply equiv_symm; apply bagify_nuke ].
    auto.
    eauto.
    transitivity (h0 * h); eauto.
    sepLemma.
  Qed.
End starB.
