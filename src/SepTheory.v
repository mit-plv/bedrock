Require Import List.
Require Import PropX.

Module Type SepLog.
  
  Parameter addr : Type.
  Parameter byte : Type.

  Parameter addr_dec : forall a b : addr, {a = b} + {a <> b}.

End SepLog.

Module Make (M : SepLog).
  Import M.

  Definition mem := addr -> byte.

  Definition smem := addr -> option byte.

  Definition satisfies (s : smem) (m : mem) : Prop :=
    forall p, match s p with
                | None => True
                | Some x => m p = x
              end.

  (** TODO: Would it be better to denote this directly in terms of PropX? **)
  Definition hprop : Type := smem -> Prop.

  Definition disjoint (m1 m2 : smem) : Prop :=
    forall p, m1 p = None \/ m2 p = None.

  Definition join (m1 m2 : smem) : smem := 
    fun p => match m1 p with
               | None => m2 p
               | v => v
             end.

  Definition smem_eq (a b : smem) : Prop := forall p, a p = b p.
  Infix "===" := smem_eq (at level 50).

  Definition split (m ml mr : smem) : Prop :=
    disjoint ml mr /\ m === join ml mr.

  Definition semp : hprop := 
    fun h => forall p, h p = None.

  Definition ptsTo (a : addr) (b : byte) : hprop :=
    fun h => h a = Some b /\ forall p, p <> a -> h p = None.

  Definition star (P Q : hprop) : hprop :=
    fun h => exists hl, exists hr, split h hl hr /\ P hl /\ Q hr.

  Definition ex (T : Type) (p : T -> hprop) : hprop :=
    fun v => exists x, p x v.

  Definition himp (P Q : hprop) : Prop :=
    forall h, P h -> Q h.

  Infix "==>" := (himp) (at level 50).


  

  Require Import Classes.RelationClasses.
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


  
  Lemma disjoint_join : forall a b, disjoint a b -> join a b === join b a.
  Proof.
    intros. red. intros. unfold join, disjoint in *. specialize (H p). destruct (a p); destruct (b p); try congruence.
    exfalso; firstorder; congruence.
  Qed.
    
  Lemma disjoint_comm : forall ml mr, disjoint ml mr -> disjoint mr ml.
  Proof.
    firstorder.
  Qed.

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
    unfold split. intros. destruct H. apply disjoint_comm in H. split; auto. rewrite disjoint_join; auto.
  Qed.

  Theorem star_comm : forall P Q, star P Q ==> star Q P.
  Proof.
    intros. unfold himp, star. firstorder. apply disjoint_comm in H. 
    do 3 eexists. unfold split. 2: split; eassumption. rewrite disjoint_join; auto.
  Qed.

  Theorem star_assoc : forall P Q R, star P (star Q R) ==> star (star P Q) R.
  Proof.  
    unfold himp, star. intros.
    do 2 destruct H. intuition. destruct H2. destruct H1. intuition.
    do 2 eexists. split. eapply split_assoc; eassumption.
    intuition. eexists. eexists. intuition; eauto.
  Admitted.
   

  (** separation logic theory **)
  (** I need to denote this in terms of PropX **)
End Make.

  