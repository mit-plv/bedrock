Require Import Heaps.
Require Import PropX.

Require Import RelationClasses.

Module SepTheoryX (H : Heap).
  Module HT := HeapTheory H.

  Section env.
    Variable pcType : Type.    
    Variable stateType : Type.

    Definition hprop := HT.smem -> PropX pcType stateType.

    Record Hprop : Type := 
    { prop : hprop
    ; respects : forall cs G m m', HT.smem_eq m m' -> valid cs G (prop m) -> valid cs G (prop m')
    }.

    Coercion prop : Hprop >-> hprop.

    Variable cs : codeSpec pcType stateType.
    
    Definition himp (gl gr : Hprop) : Prop :=
      forall m, valid cs nil ((prop gl) m) -> valid cs nil ((prop gr) m).
    Definition heq (gl gr : Hprop) : Prop :=
      himp gl gr /\ himp gr gl.

    Global Instance Relf_himp : Reflexive himp.
    Proof.
      red. unfold himp. firstorder.
    Qed.
    Global Instance Trans_himp : Transitive himp.
    Proof.
      red. unfold himp. firstorder.
    Qed.

    Global Instance Relf_heq : Reflexive heq.
    Proof.
      red. unfold heq. firstorder.
    Qed.
    Global Instance Sym_heq : Symmetric heq.
    Proof.
      red. unfold heq. firstorder.
    Qed.
    Global Instance Trans_heq : Transitive heq.
    Proof.
      red. unfold heq. firstorder.
    Qed.

    Theorem heq_himp : forall a b, heq a b -> himp a b.
    Proof.
      unfold heq; firstorder.
    Qed.

    Theorem himp_heq : forall a b, himp a b -> himp b a -> heq a b.
    Proof.
      unfold heq; firstorder.
    Qed.

    Require Import PropXTac.
    Ltac goPropX := 
      repeat match goal with
               | [ H : valid _ _ _ |- _ ] => apply simplify_fwd in H; simpl in H
               | [ |- valid _ _ _ ] => apply simplify_bwd; simpl
               | [ H : exists x , _ |- _ ] => destruct H
               | [ H : _ /\ _ |- _ ] => destruct H
             end.
    Ltac doIt :=
      unfold himp, heq; simpl; intros;
        repeat match goal with
                 | [ h : HT.smem , H : forall x : HT.smem , _ |- _ ] => specialize (H h)
                 | [ H : _ -> _ |- _ ] => apply H; clear H
                 | [ H : ?X -> _ , H' : ?X |- _ ] => apply H in H'; clear H
               end; goPropX;
        repeat match goal with
                 | [ |- exists x, _ ] => eexists
                 | [ |- _ /\ _ ] => split
                 | [ |- simplify _ _ _ ] => eassumption
               end.

    (* Definitions *)
    Definition hemp : hprop :=
      fun m => PropX.Inj (HT.semp m).
    
    Theorem hemp_respects : forall cs G m m', HT.smem_eq m m' -> valid cs G (hemp m) -> valid cs G (hemp m').
      intros; goPropX; eapply Inj_E in H0; try eassumption; intros; eapply Inj_I;
        eapply HT.semp_mor; eauto; symmetry; auto.
    Qed.

    Definition emp : Hprop := Build_Hprop _ hemp_respects.

    Definition hstar (l r : Hprop) : hprop :=
      fun m => PropX.Exists (fun ml : HT.smem => PropX.Exists (fun mr : HT.smem =>
        PropX.And (PropX.Inj (HT.split m ml mr)) (And ((prop l) ml) ((prop r) mr)))).

    Theorem hstar_respects (l r : Hprop) : forall cs G m m', HT.smem_eq m m' -> 
      valid cs G ((hstar l r) m) -> valid cs G ((hstar l r) m').
    Proof.
      intros; unfold hstar in *; goPropX. 
    Admitted.

    Definition star (l r : Hprop) : Hprop := Build_Hprop _ (hstar_respects l r).
      
    Definition hinj (p : PropX pcType stateType) : hprop :=
      fun m => PropX.And p (prop emp m).
    
    Theorem hinj_respects (p : PropX pcType stateType) : forall cs G m m', 
      HT.smem_eq m m' -> valid cs G ((hinj p) m) -> valid cs G ((hinj p) m').
    Proof.
      unfold hinj; intros. eapply And_I. eapply And_E1 in H0. auto. eapply And_E2 in H0.
      unfold emp, hemp in *. simpl in *. eapply Inj_E in H0. eassumption. intros.
      eapply Inj_I. eapply HT.semp_mor; eauto. symmetry; auto.
    Qed.

    Definition inj (p : PropX pcType stateType) : Hprop := Build_Hprop _ (hinj_respects p).


    Definition hcptr (stateMem : stateType -> H.mem) (p : pcType) (t : stateType -> Hprop) : hprop :=
      fun h => 
        PropX.And 
          (PropX.Inj (HT.semp h))
          (PropX.Cptr p
            (fun x : stateType => PropX.Exists (fun m => 
              PropX.And (PropX.Inj (HT.satisfies m (stateMem x))) (prop (t x) m)))).

    Theorem hcptr_respects (stateMem : stateType -> H.mem) (p : pcType) (t : stateType -> Hprop) : 
      forall cs G m m', 
        HT.smem_eq m m' -> valid cs G ((hcptr stateMem p t) m) -> valid cs G ((hcptr stateMem p t) m').
    Proof.
      unfold hcptr; intros; goPropX. eapply And_I. eapply And_E1 in H0. eapply Inj_E in H0. eassumption. intros.
        eapply Inj_I. eapply HT.semp_mor; eauto. symmetry; auto.
        eapply And_E2 in H0. eassumption.
    Qed.

    Definition cptr (stateMem : stateType -> H.mem) (p : pcType) (t : stateType -> Hprop) : Hprop :=
      Build_Hprop _ (hcptr_respects stateMem p t).

    Definition hex (T : Type) (p : T -> Hprop) : hprop :=
      fun h => PropX.Exists (fun t => prop (p t) h).
    
    Definition hex_respects T (p : T -> Hprop) : forall cs G m m', 
      HT.smem_eq m m' -> valid cs G ((hex _ p) m) -> valid cs G ((hex _ p) m').
    Proof.
      unfold hex; intros; goPropX. eapply Exists_E in H0. eassumption. intros.
        eapply Exists_I. instantiate (1 := B). destruct (p B). simpl in *.
    Admitted.

    Definition ex (T : Type) (p : T -> Hprop) : Hprop := Build_Hprop _ (hex_respects T p).

    (** Lemmas **)

    Theorem himp_star_comm_p : forall P Q R, himp (star P Q) R -> himp (star Q P) R.
    Proof.
      doIt. eapply HT.split_comm. auto.
    Qed.
    Theorem himp_star_comm_c : forall P Q R, himp R (star P Q) -> himp R (star Q P).
    Proof.
      doIt. eapply HT.split_comm. auto.
    Qed.

    Theorem heq_star_comm : forall P Q R, heq (star P Q) R -> heq (star Q P) R.
    Proof.
      intros.
      generalize (himp_star_comm_p P Q R).
      generalize (himp_star_comm_c P Q R).
      unfold himp, heq in *. intuition.
    Qed.
  
    Theorem himp_star_assoc_p : forall P Q R S,
      himp (star P (star Q R)) S -> himp (star (star P Q) R) S.
    Proof.
      doIt. apply HT.split_comm. apply HT.split_comm in H. eapply HT.split_assoc; try eassumption. 
      apply HT.split_comm. eassumption. eapply HT.disjoint_split_join.
      apply HT.disjoint_comm. eapply HT.split_split_disjoint; eauto.
      apply HT.split_comm in H0; eassumption.
    Qed.
    Theorem himp_star_assoc_c : forall P Q R S, 
      himp S (star P (star Q R)) -> himp S (star (star P Q) R).
    Proof.
      doIt. eapply HT.split_assoc; eassumption. apply HT.split_comm.
      apply HT.disjoint_split_join. apply HT.disjoint_comm.
      eapply HT.split_split_disjoint. apply HT.split_comm. eassumption. eassumption.
    Qed.

    Theorem heq_star_assoc : forall P Q R S, 
      heq S (star P (star Q R)) -> heq S (star (star P Q) R).
    Proof.
      intros. generalize (himp_star_assoc_p P Q R S). generalize (himp_star_assoc_c P Q R S).
      firstorder.
    Qed.

    Theorem himp_star_frame : forall P Q R S, himp P Q -> himp R S -> himp (star P R) (star Q S).
    Proof.
      unfold himp; simpl; intros;
        repeat match goal with
                 | [ H : _ -> _ |- _ ] => apply H; clear H
                 | [ H : ?X -> _ , H' : ?X |- _ ] => apply H in H'; clear H
               end; goPropX.
      apply simplify_bwd in H2. apply simplify_bwd in H3. apply H in H2. apply H0 in H3. doIt.
      assumption.
    Qed.

    Theorem heq_star_frame : forall P Q R S, heq P Q -> heq R S -> heq (star P R) (star Q S).
    Proof.
      intros; generalize (himp_star_frame P Q R S). generalize (himp_star_frame Q P S R).
      unfold heq in *. intuition.
    Qed.

    Theorem himp_star_emp_p : forall P Q, himp P Q -> himp (star emp P) Q.
    Proof.
      unfold himp. intros. eapply H. unfold star in *. simpl in *.
      goPropX. apply simplify_bwd in H2. destruct P. simpl in *.
      eapply HT.split_semp in H1; eauto.
      eapply respects0 in H2. goPropX. eassumption. symmetry; eauto.
    Qed.

    Theorem himp_star_emp_p' : forall P Q, himp (star emp P) Q -> himp P Q.
    Proof.
      unfold himp. intros. eapply H. unfold star in *. simpl in *.
      goPropX. do 2 eexists. split. eapply HT.split_a_semp_a. split; eauto.
      eapply HT.semp_smem_emp.
    Qed.

    Theorem himp_star_emp_c : forall P Q, himp P Q -> himp P (star emp Q).
    Proof.
      unfold himp. intros. eapply H in H0. unfold star in *. simpl in *.
      goPropX. do 2 eexists. split. eapply HT.split_a_semp_a. split; eauto.
      eapply HT.semp_smem_emp.
    Qed.

    Theorem himp_star_emp_c' : forall P Q, himp P (star emp Q) -> himp P Q.
    Proof.
      unfold himp. intros. eapply H in H0. unfold star in *. simpl in *.
      goPropX. apply simplify_bwd in H2. destruct Q. simpl in *.
      eapply HT.split_semp in H1; eauto. unfold interp in H2.
      eapply respects0 in H2. goPropX. eassumption. symmetry; eauto.
    Qed.

    Theorem heq_star_emp : forall P Q, heq P Q -> heq (star emp P) Q.
    Proof.
      intros. unfold heq in *; intuition.
      eapply himp_star_emp_p. auto.
      eapply himp_star_emp_c. auto.
    Qed.

    Theorem heq_star_emp' : forall P Q, heq (star emp P) Q -> heq P Q.
    Proof.
      intros. unfold heq in *; intuition.
      eapply himp_star_emp_p' in H0. auto.
      eapply himp_star_emp_c' in H1. auto.
    Qed.

    Theorem himp_star_cancel : forall P Q R, himp Q R -> himp (star P Q) (star P R).
    Proof.
      intros. eapply himp_star_frame. reflexivity. auto.
    Qed.

    Theorem heq_star_cancel : forall P Q R, heq Q R -> heq (star P Q) (star P R).
    Proof.
      intros. eapply heq_star_frame. reflexivity. auto.
    Qed.

  End env.
End SepTheoryX.