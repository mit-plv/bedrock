Require Import AutoSep Malloc.

Set Implicit Arguments.


Definition bag := W * W -> nat.

Theorem W_W_dec : forall x y : W * W, {x = y} + {x <> y}.
  decide equality; apply weq.
Qed.

Definition mem (p : W * W) (b : bag) := (b p > 0)%nat.
Infix "%in" := mem (at level 70, no associativity).

Definition empty : bag := fun _ => O.

Definition equiv (b1 b2 : bag) := forall p, b1 p = b2 p.
Infix "%=" := equiv (at level 70, no associativity).

Definition add (b : bag) (p : W * W) : bag := fun p' => if W_W_dec p' p then S (b p') else b p'.
Infix "%+" := add (at level 50, left associativity).

Definition del (b : bag) (p : W * W) : bag := fun p' => if W_W_dec p' p then pred (b p') else b p'.
Infix "%-" := del (at level 50, left associativity).

Ltac bags := subst;
  repeat match goal with
           | [ H : _ %= _ |- _ ] => generalize dependent H
           | [ H : _ %in _ |- _ ] => generalize dependent H
           | [ H : ~ _ %in _ |- _ ] => generalize dependent H
           | [ H : _ \is _ |- _ ] => generalize dependent H
           | [ H : @eq W _ _ |- _ ] => generalize dependent H
           | [ H : ~(@eq W _ _) |- _ ] => generalize dependent H
         end; clear;
  unfold equiv, empty, mem, add, del, propToWord, IF_then_else; intuition idtac;
    repeat (match goal with
              | [ H : (_, _) = (_, _) |- _ ] => injection H; clear H; intros; subst
              | [ |- context[if ?E then _ else _] ] => destruct E; subst
              | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; subst
              | [ H : forall p : W * W, _ |- _ ] => rewrite H in *
            end; intuition idtac);
    try match goal with
          | [ |- _ \/ _ ] => right; intuition idtac
        end;
    repeat match goal with
             | [ H : forall p : W * W, _ |- _ ] => rewrite H in *
           end; auto; try (discriminate || omega).

Hint Extern 5 (_ %= _) => bags.
Hint Extern 5 (_ %in _) => bags.
Hint Extern 5 (~ _ %in _) => bags.
Hint Extern 5 (_ \is _) => bags.


Section adt.
  Variable P : bag -> W -> HProp.
  (* Abstract predicate for the data structure *)

  Variable res : nat.
  (* How many reserved stack slots? *)

  Definition initS : spec := SPEC reserving res
    PRE[_] mallocHeap 0
    POST[R] P empty R * mallocHeap 0.

  Definition isEmptyS : spec := SPEC("b") reserving res
    Al b,
    PRE[V] P b (V "b") * mallocHeap 0
    POST[R] [| (b %= empty) \is R |] * P b (V "b") * mallocHeap 0.

  Definition enqueueS : spec := SPEC("b", "v1", "v2") reserving res
    Al b,
    PRE[V] P b (V "b") * mallocHeap 0
    POST[_] P (b %+ (V "v1", V "v2")) (V "b") * mallocHeap 0.

  Definition dequeueS : spec := SPEC("b", "r") reserving res
    Al b,
    PRE[V] [| ~(b %= empty) |] * P b (V "b") * V "r" =?> 2 * mallocHeap 0
    POST[_] Ex v1, Ex v2, [| (v1, v2) %in b |] * P (b %- (v1, v2)) (V "b") * (V "r" ==*> v1, v2) * mallocHeap 0.
End adt.


(** * Iterated star *)

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

  Fixpoint nuke (p : W * W) (ls : list (W * W)) : list (W * W) :=
    match ls with
      | nil => nil
      | p' :: ls => if W_W_dec p p' then ls else p' :: nuke p ls
    end.

  Lemma starL_del_fwd : forall v ls, In v ls
    -> starL P ls ===> P v * starL P (nuke v ls).
    induction ls; unfold bagify in *; simpl in *; intuition subst.
    destruct (W_W_dec v v); apply Himp_refl || tauto.
    destruct (W_W_dec v (a0, b)); subst; try apply Himp_refl.
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
    destruct (W_W_dec v v); intuition.
    eapply equiv_trans; [ | apply del_something ].
    apply bagify_cong; auto.
    auto.
    destruct (W_W_dec v (a0, b)); subst.
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

Lemma propToWord_elim_not1 : forall P b,
  P \is b
  -> b <> 1
  -> ~P.
  bags.
Qed.

Hint Immediate propToWord_elim_not1.
