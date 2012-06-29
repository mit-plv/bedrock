Require Import Word SepIL IL Memory.


Fixpoint allocated (base : W) (offset len : nat) : HProp :=
  match len with
    | O => Emp
    | S len' => (Ex v, (match offset with
                          | O => base
                          | _ => base ^+ $(offset)
                        end) =*> v) * allocated base (4+offset) len'
  end%Sep.

Notation "p =?> len" := (allocated p O len) (at level 39) : Sep_scope.

Theorem allocated_extensional : forall base offset len, HProp_extensional (allocated base offset len).
  destruct len; reflexivity.
Qed.

Hint Immediate allocated_extensional.


Lemma Himp_refl : forall p, p ===> p.
  intros; hnf; intros; hnf; intros.
  apply PropX.Imply_I.
  apply PropX.Env.
  simpl; auto.
Qed.

Lemma allocated_shift_base' : forall base base' len offset offset',
  base ^+ $(offset) = base' ^+ $(offset')
  -> allocated base offset len ===> allocated base' offset' len.
  induction len; intros.

  apply Himp_refl.

  unfold allocated; fold allocated.
  match goal with
    | [ |- context[(?X =*> _)%Sep] ] =>
      assert (X = base ^+ natToW offset)
  end.
  destruct offset; auto.
  W_eq.
  rewrite H0; clear H0.

  match goal with
    | [ |- context[(?X =*> _)%Sep] ] =>
      match X with
        | context[offset'] => assert (X = base' ^+ natToW offset')
      end
  end.
  destruct offset'; auto.
  W_eq.
  rewrite H0; clear H0.

  match goal with
    | [ H : ?X = _ |- context[(?Y =*> _)%Sep] ] => change Y with X; rewrite H
  end.
  hnf; intros; hnf; intros.
  Require Import PropX.
  apply Imply_I.
  unfold starB, star.
  eapply Exists_E.
  apply Env; unfold List.In; eauto.
  cbv beta; intro.
  eapply Exists_E.
  apply Env; unfold List.In; eauto.
  cbv beta; intro.
  unfold exB, ex.
  eapply Exists_E.
  eapply And_E1.
  eapply And_E2.
  apply Env; unfold List.In; eauto.
  cbv beta; intro.
  apply Exists_I with B; apply Exists_I with B0.
  apply And_I.
  eapply And_E1; apply Env; unfold List.In; eauto.
  apply And_I.
  apply Exists_I with B1.
  apply Env; unfold List.In; auto.
  eapply Imply_E.
  apply PropXTac.interp_weaken.
  apply IHlen; eauto.
  instantiate (1 := 4 + offset).
  repeat rewrite natToW_plus.
  do 2 rewrite (wplus_comm (natToW 4)).
  repeat rewrite wplus_assoc.
  f_equal.
  assumption.

  do 2 eapply And_E2.
  apply Env; unfold List.In; eauto.
Qed.

Theorem allocated_shift_base : forall base base' len len' offset offset',
  base ^+ $(offset) = base' ^+ $(offset')
  -> len = len'
  -> allocated base offset len ===> allocated base' offset' len'.
  intros; subst; apply allocated_shift_base'; auto.
Qed.

Lemma split_empty : forall m, semp m
  -> split m m m.
  unfold semp; intros; subst.
  split.

  Lemma disjoint'_emp : forall addrs, disjoint' addrs (smem_emp' _) (smem_emp' _).
    induction addrs; simpl; intuition.
  Qed.
  apply disjoint'_emp.

  Lemma join'_emp : forall addrs, smem_emp' _ = join' addrs (smem_emp' _) (smem_emp' _).
    induction addrs; simpl; intuition.
    congruence.
  Qed.

  apply join'_emp.
Qed.

Theorem allocated_split : forall base len' len offset,
  (len' <= len)%nat
  -> allocated base offset len ===> allocated base offset len' * allocated base (offset + 4 * len') (len - len').
  induction len'; inversion 1.

  simpl.
  hnf; intros; hnf; intros.
  apply Imply_I.
  do 2 apply Exists_I with smem_emp.
  unfold empB, emp, inj.
  eapply Inj_E.
  eapply And_E2; apply Env; unfold List.In; eauto.
  intro.
  hnf in H1; subst.
  repeat apply And_I; apply Inj_I; auto.
  apply split_empty; reflexivity.
  reflexivity.
  reflexivity.

  replace (offset + 4 * 0) with offset by omega.
  simpl minus.
  unfold allocated at 2.
  hnf; intros; hnf; intros.
  apply Imply_I.
  apply Exists_I with smem_emp.
  apply Exists_I with m0.
  unfold empB, emp, inj.
  repeat apply And_I; try apply Inj_I; auto.
  apply split_a_semp_a.
  reflexivity.

  subst.
  replace (S len' - S len') with 0 by omega.
  unfold allocated at 3.
  hnf; intros; hnf; intros.
  apply Imply_I.
  apply Exists_I with m.
  apply Exists_I with smem_emp.
  unfold empB, emp, inj.
  repeat apply And_I; try apply Inj_I; auto.
  apply split_comm; apply split_a_semp_a.
  reflexivity.

  subst.
  replace (offset + 4 * S len') with ((4 + offset) + 4 * len') by omega.
  unfold allocated at 1 2; fold allocated.
  hnf; intros; hnf; intros.
  apply Imply_I.
  unfold starB, star, exB, ex, injB, inj.
  eapply Exists_E.
  apply Env; unfold List.In; eauto.
  cbv beta; intro.
  eapply Exists_E.
  apply Env; unfold List.In; eauto.
  cbv beta; intro.
  eapply Exists_E.
  eapply Imply_E.
  apply PropXTac.interp_weaken.
  eapply IHlen'.
  instantiate (1 := m); omega.
  do 2 eapply And_E2; apply Env; unfold List.In; eauto.
  cbv beta; intro.
  eapply Exists_E.
  apply Env; unfold List.In; eauto.
  cbv beta; intro.
  apply Exists_I with (HT.join B B1).
  apply Exists_I with B2.
  apply And_I.
  eapply Inj_E.
  eapply And_E1; apply Env; unfold List.In; eauto.
  intro.
  apply Inj_E with (split m0 B B0).
  eapply And_E1; apply Env; unfold List.In; eauto.
  intro.
  apply Inj_I.
  rewrite disjoint_join.
  eapply split_assoc; eauto.
  unfold split in *; intuition; subst.
  
  Require Import List DepList.

  Lemma hlist_eta : forall A B (ls : list A) (h : hlist B ls),
    h = match ls return hlist B ls -> hlist B ls with
          | nil => fun _ => HNil
          | _ :: _ => fun h => HCons (hlist_hd h) (hlist_tl h)
        end h.
    destruct h; reflexivity.
  Qed.

  Lemma disjoint_join' : forall dom (sm sm1 sm2 : smem' dom),
    disjoint' _ sm (join' _ sm1 sm2)
    -> disjoint' _ sm sm1.
    induction sm; intros; rewrite (hlist_eta _ _ _ sm1) in *;
      rewrite (hlist_eta _ _ _ sm2) in *; simpl in *; intuition eauto.
    destruct (hlist_hd sm1); auto; discriminate.
  Qed.

  eapply disjoint_join'; eauto.

  apply And_I.
  apply Exists_I with B; apply Exists_I with B1.
  apply And_I.
  eapply Inj_E.
  eapply And_E1; apply Env; unfold List.In; eauto.
  intro.
  apply Inj_E with (HT.split m0 B B0).
  eapply And_E1; apply Env; unfold List.In; eauto.
  intro.  
  apply Inj_I.
  apply disjoint_split_join.
  unfold HT.split in *; intuition; subst.
  eapply disjoint_join'; eauto.
  apply And_I.
  eapply And_E1; eapply And_E2; apply Env; unfold List.In; eauto.
  eapply And_E1; eapply And_E2; apply Env; unfold List.In; eauto.
  do 2 eapply And_E2; apply Env; unfold List.In; eauto.
Qed.
