Require Import Classes.RelationClasses.
Require Import Classes.Morphisms.
Require Import Setoid.

Module Type Heap.
  
  Parameter addr : Type.
  Parameter byte : Type.

  Parameter mem : Type.

  Parameter mem_get : mem -> addr -> option byte.

  Parameter addr_dec : forall a b : addr, {a = b} + {a <> b}.

End Heap.

Module HeapTheory (B : Heap).
  Import B.

  Definition smem := addr -> option byte.

  Definition smem_eq (a b : smem) : Prop := forall p, a p = b p.
  Infix "===" := smem_eq (at level 50).

  Definition disjoint (m1 m2 : smem) : Prop :=
    forall p, m1 p = None \/ m2 p = None.

  Definition join (m1 m2 : smem) : smem := 
    fun p => match m1 p with
               | None => m2 p
               | v => v
             end.

  Definition split (m ml mr : smem) : Prop :=
    disjoint ml mr /\ m === join ml mr.

  Definition semp (m : smem) : Prop :=
    forall p, m p = None.

  Definition satisfies (m : smem) (m' : B.mem) : Prop :=
    forall p, 
      match m p with
        | None => True
        | Some x => B.mem_get m' p = Some x
      end.

  Ltac morph := 
    unfold smem_eq, join, disjoint; intuition;
      repeat match goal with
               | [ H : forall p, _ , p : addr |- _ ] => specialize (H p)
               | [ H : _ = _ |- _ ] => rewrite H in *
             end; intuition.

  Global Instance Refl_smem : Reflexive smem_eq.
  Proof.
    red. firstorder.
  Qed.

  Global Instance Sym_smem : Symmetric smem_eq.
  Proof.
    red. firstorder.
  Qed.
  
  Global Instance Trans_smem : Transitive smem_eq.
  Proof.
    red. unfold smem_eq. firstorder. rewrite H. auto.
  Qed.

  Add Parametric Morphism : smem_eq with 
    signature smem_eq ==> smem_eq ==> iff as eq_mor.
  Proof.
    morph.
  Qed.
  Add Parametric Morphism : join with 
    signature smem_eq ==> smem_eq ==> smem_eq as join_mor.
  Proof.
    morph.
  Qed.
  Add Parametric Morphism : disjoint with 
    signature smem_eq ==> smem_eq ==> iff as disjoint_mor.
  Proof.
    morph.
  Qed.

  Add Parametric Morphism : semp with 
    signature smem_eq ==> iff as semp_mor.
  Proof.
    unfold semp; morph. 
  Qed.

  Lemma disjoint_join : forall a b, disjoint a b -> join a b === join b a.
  Proof.
    intros. red. intros. unfold join, disjoint in *. specialize (H p). destruct (a p); destruct (b p); try congruence.
    exfalso; firstorder; congruence.
  Qed.
    
  Lemma disjoint_comm : forall ml mr, disjoint ml mr -> disjoint mr ml.
  Proof.
    firstorder.
  Qed.

  Hint Resolve disjoint_join disjoint_comm : disjoint.

  Lemma split_assoc : forall a b c d e, split a b c -> split c d e ->
    split a (join d b) e.
  Proof.
    unfold split. intuition. unfold disjoint in *. intuition.
    unfold join in *.
    repeat match goal with
             | [ H : _ |- _ ] => specialize (H p); simpl in *
             | [ H : _ = _ |- _ ] => rewrite H in *
             | [ H : _ \/ _ |- _ ] => destruct H
           end; intuition.
    rewrite H2. intro. unfold join in *; simpl in *;
    repeat match goal with
             | [ H : _ |- _ ] => specialize (H p); simpl in *
             | [ H : _ = _ |- _ ] => rewrite H in *
             | [ H : _ \/ _ |- _ ] => destruct H
           end; intuition.
    destruct (d p); intuition.
    destruct (b p); intuition;
    destruct (d p); intuition. congruence.
  Qed.

  Lemma split_comm : forall m ml mr, split m ml mr -> split m mr ml.
  Proof.
    unfold split. intros. destruct H. apply disjoint_comm in H. split; auto. rewrite H0; eauto with disjoint.
  Qed.

  Lemma disjoint_split_join : forall a b, disjoint a b -> split (join a b) a b.
  Proof.
    unfold split, disjoint; intros; intuition.
  Qed.

  Lemma split_split_disjoint : forall a b c d e,
    split a b c -> split b d e -> disjoint c d.
  Proof.
    unfold split, disjoint, join, smem_eq; intros; intuition.
    specialize (H1 p). specialize (H p); specialize (H2 p); specialize (H3 p).    
    destruct H1; destruct H; intuition.  rewrite H0 in *. destruct (d p). congruence. auto.
  Qed.

  Lemma split_semp : forall a b c, 
    split a b c -> semp b -> a === c.
  Proof.
    unfold split, semp, join, disjoint, smem_eq. intuition.
    specialize (H2 p). rewrite H0 in H2. auto.
  Qed.

End HeapTheory.
