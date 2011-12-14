Require Import Heaps.
Require Import PropX PropXTac.
Require Import Env.
Require Import IL.

Require Import RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.

Module SepTheoryX (H : Heap).
  Module HT := HeapTheory H.

  Section env.
    Variable pcType : Type.    
    Variable stateType : Type.

    Definition hprop (sos : list Type) := settings -> HT.smem -> propX pcType stateType sos.

    Variable cs : codeSpec pcType stateType.

    Definition himp (gl gr : hprop nil) : Prop :=
      forall s m, interp cs (gl s m) -> interp cs (gr s m).
    Definition heq (gl gr : hprop nil) : Prop :=
      himp gl gr /\ himp gr gl.


    Global Instance Refl_himp : Reflexive himp.
    Proof.
      red; unfold himp; firstorder.
    Qed.
    Global Instance Trans_himp : Transitive himp.
    Proof.
      red; unfold himp; firstorder.
    Qed.

    Global Instance Refl_heq : Reflexive heq.
    Proof.
      red; unfold heq; auto; split; reflexivity.
    Qed.
    Global Instance Sym_heq : Symmetric heq.
    Proof.
      red; unfold heq; firstorder.
    Qed.
    Global Instance Trans_heq : Transitive heq.
    Proof.
      red; unfold heq. intuition; etransitivity; eassumption.
    Qed.

    Theorem heq_himp : forall a b, heq a b -> himp a b.
    Proof.
      unfold heq; firstorder.
    Qed.

    Theorem himp_heq : forall a b, himp a b -> himp b a -> heq a b.
    Proof.
      unfold heq; firstorder.
    Qed.

    (* Definitions *)
    Definition inj sos (p : propX pcType stateType sos) : hprop sos :=
      fun _ m => PropX.And p (PropX.Inj (HT.semp m)).

    Definition emp {sos} : hprop sos := inj (PropX.Inj True).

    Definition star sos (l r : hprop sos) : hprop sos :=
      fun s m => PropX.Exists (fun ml : HT.smem => PropX.Exists (fun mr : HT.smem =>
        PropX.And (PropX.Inj (HT.split m ml mr)) (And (l s ml) (r s mr)))).

    Definition ex sos (T : Type) (p : T -> hprop sos) : hprop sos :=
      fun s h => PropX.Exists (fun t => p t s h).

    Definition hptsto sos (p : H.addr) (v : H.byte) : hprop sos :=
      fun s h => 
        PropX.Inj (HT.smem_get p h = Some v /\ forall p', p' <> p -> HT.smem_get p' h = None).



    (** Lemmas **)
    Ltac doIt :=
      unfold himp, heq; simpl; intros;
        repeat match goal with
(*                 | [ h : HT.smem , H : forall x : HT.smem , _ |- _ ] => specialize (H h) *)
                 | [ H : _ -> _ |- _ ] => apply H; clear H
                 | [ H : forall x, _ -> _ , H' : _ |- _ ] => apply H in H'
                 | [ H : ?X -> _ , H' : ?X |- _ ] => apply H in H'; clear H
               end; propxFo;
        repeat match goal with
                 | [ |- exists x, _ ] => eexists
                 | [ |- _ /\ _ ] => split
                 | [ |- simplify _ _ _ ] => eassumption || apply simplify_fwd
                 | [ H : interp ?X (?Y _) |- interp ?X (?Y _) ] => eapply H
               end.

    Hint Immediate HT.split_comm : heaps.
    Hint Resolve HT.split_assoc HT.disjoint_split_join HT.split_split_disjoint : heaps.

    Lemma himp_star_comm : forall P Q, himp (star P Q) (star Q P).
    Proof.
      unfold star; doIt; eauto with heaps.
    Qed.

    Theorem himp_star_comm_p : forall P Q R, himp (star P Q) R -> himp (star Q P) R.
    Proof.
      unfold star; doIt. eauto with heaps. 
    Qed.
    Theorem himp_star_comm_c : forall P Q R, himp R (star P Q) -> himp R (star Q P).
    Proof.
      unfold star; doIt. eauto with heaps.
    Qed.

    Theorem heq_star_comm : forall P Q R, heq (star P Q) R -> heq (star Q P) R.
    Proof.
      intros.
      generalize (@himp_star_comm_p P Q R).
      generalize (@himp_star_comm_c P Q R).
      unfold himp, heq in *. intuition.
    Qed.
  
    Theorem himp_star_assoc_p : forall P Q R S,
      himp (star P (star Q R)) S -> himp (star (star P Q) R) S.
    Proof.
      doIt.
      eapply HT.split_comm. eapply HT.split_assoc. eapply HT.split_comm. eassumption. eapply HT.split_comm. eassumption.
      eapply HT.disjoint_split_join. eapply HT.disjoint_comm. eauto with heaps. 
    Qed.

    Theorem himp_star_assoc_c : forall P Q R S, 
      himp S (star P (star Q R)) -> himp S (star (star P Q) R).
    Proof.
      doIt. eapply HT.split_assoc. eassumption. eassumption.
      eapply HT.split_comm. eapply HT.disjoint_split_join. eapply HT.disjoint_comm. eauto with heaps.
    Qed.

    Theorem heq_star_assoc : forall P Q R S, 
      heq (star P (star Q R)) S -> heq (star (star P Q) R) S.
    Proof.
      intros. generalize (@himp_star_assoc_p P Q R S). generalize (@himp_star_assoc_c P Q R S).
      firstorder.
    Qed.

    Theorem himp_star_frame : forall P Q R S, 
      himp P Q -> himp R S -> himp (star P R) (star Q S).
    Proof.
      doIt. 2: eapply H; eassumption. 2: eapply H0; eassumption. auto.
    Qed.

    Theorem heq_star_frame : forall P Q R S, heq P Q -> heq R S -> heq (star P R) (star Q S).
    Proof.
      doIt. eapply himp_star_frame; eauto. eapply himp_star_frame; eauto.
    Qed.

    Theorem himp_subst_p : forall P Q R S,
      himp P S -> himp (star S Q) R ->
      himp (star P Q) R.
    Proof. 
      doIt; eauto.
    Qed.

    Theorem himp_subst_c : forall P Q R S,
      himp S Q -> himp P (star S R) ->
      himp P (star Q R).
    
      doIt; eauto.
    Qed.       

    Theorem heq_subst : forall P Q R S,
      heq P S -> heq (star S Q) R ->
      heq (star P Q) R.
    
      unfold heq; destruct 1; destruct 1; split.
      eapply himp_subst_p; eauto. eapply himp_subst_c; eauto.
    Qed. 

    Theorem himp_star_emp_p : forall P Q, himp P Q -> himp (star emp P) Q.
    
      doIt. eapply HT.split_semp in H0; subst; auto.
    Qed. 

    Theorem himp_star_emp_p' : forall P Q, himp (star emp P) Q -> himp P Q.
    
      doIt. eapply HT.split_a_semp_a. auto. eapply HT.semp_smem_emp.
    Qed. 

    Theorem himp_star_emp_c : forall P Q, himp P Q -> himp P (star emp Q).
    
      doIt; auto. eapply HT.split_a_semp_a. eapply HT.semp_smem_emp.
    Qed. 

    Theorem himp_star_emp_c' : forall P Q, himp P (star emp Q) -> himp P Q.
    
      doIt; auto. eapply HT.split_semp in H1; subst; auto.
    Qed. 

    Theorem heq_star_emp : forall P Q, heq P Q -> heq (star emp P) Q.
    
      intros. unfold heq in *; intuition.
      eapply himp_star_emp_p. auto.
      eapply himp_star_emp_c. auto.
    Qed. 

    Theorem heq_star_emp' : forall P Q, heq (star emp P) Q -> heq P Q.
    
      intros. unfold heq in *; intuition.
      eapply himp_star_emp_p' in H0. auto.
      eapply himp_star_emp_c' in H1. auto.
    Qed. 

    Theorem himp_star_cancel : forall P Q R, himp Q R -> himp (star P Q) (star P R).
    
      intros. eapply himp_star_frame. reflexivity. auto.
    Qed. 

    Theorem heq_star_cancel : forall P Q R, heq Q R -> heq (star P Q) (star P R).
    
      intros. eapply heq_star_frame. reflexivity. auto.
    Qed. 

    Theorem himp_ex_p : forall T (P : T -> _) Q, 
      (forall v, himp (P v) Q) -> himp (ex P) Q.
    
      intros. unfold himp, ex in *; simpl in *; intros. propxFo. eauto.
    Qed.

    Theorem himp_ex_c : forall T (P : T -> _) Q, 
      (exists v, himp Q (P v)) -> himp Q (ex P).
    Proof.
      intros. unfold himp, ex in *; simpl in *; intros. propxFo. exists x. propxFo.
    Qed.

    Hint Resolve simplify_fwd : heaps.

    Theorem heq_ex : forall T (P Q : T -> _), 
      (forall v, heq (P v) (Q v)) ->
      heq (ex P) (ex Q).
    Proof.
      unfold heq, himp; propxFo;
       match goal with
         | [ H : forall v : ?T, _, x : ?T |- _ ] => specialize (H x)
       end; propxFo; eauto with heaps.
    Qed.

    Theorem heq_ex_star : forall T (P : T -> _) Q,
      heq (star (ex P) Q) (ex (fun x => star (P x) Q)).
    Proof.
      unfold heq, star, ex. doIt; intuition eauto. 
    Qed.

    Theorem himp_ex_star : forall T (P : T -> _) Q,
      himp (star (ex P) Q) (ex (fun x => star (P x) Q)).
    Proof.
      unfold himp, star, ex. doIt; intuition eauto. 
    Qed.
      
  End env.
End SepTheoryX.