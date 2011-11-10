Require Import Heaps.
Require Import PropX.
Require Import Env.
Require Import PropXTac.

Require Import RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.

Module SepTheoryX (H : Heap).
  Module HT := HeapTheory H.

  Section env.
    Variable pcType : Type.    
    Variable stateType : Type.

    Definition hprop (sos : list Type) := HT.smem -> propX pcType stateType sos.

    Variable cs : codeSpec pcType stateType.
    Require Import List.
    
    Fixpoint forallXify (ls : list Type) : propX pcType stateType ls -> PropX pcType stateType :=
      match ls with
        | nil => fun x => x 
        | a :: b => fun x => forallXify (PropX.ForallX x)
      end.

    Fixpoint SubstAll dom (m : hlist (fun T => T -> PropX pcType stateType) dom) (p : propX pcType stateType dom) : PropX pcType stateType :=
      match p in propX _ _ dom 
        return hlist (fun T => T -> PropX pcType stateType) dom -> PropX pcType stateType
        with 
        | Inj _ p => fun _ => Inj p
        | Cptr _ pc s => fun m => Cptr pc (fun x => SubstAll m (s x))
        | And _ l r => fun m => And (SubstAll m l) (SubstAll m r)
        | Or _ l r => fun m => Or (SubstAll m l) (SubstAll m r)
        | Imply _ l r => fun m => Imply (SubstAll m l) (SubstAll m r)

        | _ => fun _ => Inj True
      end m.

    Lemma forallXify_subst : forall sos (l : propX pcType stateType sos),
      (forall m : hlist (fun T => T -> PropX pcType stateType) sos, 
        interp cs (SubstAll m l))
      -> interp cs (forallXify l).
    Admitted.

    Definition himp (gl gr : hprop nil) : Prop :=
      forall m, interp cs (gl m --> gr m).
    Definition heq (gl gr : hprop nil) : Prop :=
      himp gl gr /\ himp gr gl.

    Global Instance Relf_himp : Reflexive himp.
    Proof.
      red. unfold himp. intros. apply Imply_I. econstructor; simpl; auto.
    Qed.
    Global Instance Trans_himp : Transitive himp.
    Proof.
      red. unfold himp. firstorder. apply Imply_I.
    Admitted.

    Global Instance Relf_heq : Reflexive heq.
    Proof.
      red. unfold heq. 
    Admitted.
    Global Instance Sym_heq : Symmetric heq.
    Proof.
      red. unfold heq. 
    Admitted.
    Global Instance Trans_heq : Transitive heq.
    Proof.
      red. unfold heq.
    Admitted.

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
    Definition inj sos (p : propX pcType stateType sos) : hprop sos :=
      fun m => PropX.And p (PropX.Inj (HT.semp m)).
(*    
    Theorem hinj_respects (p : PropX pcType stateType) : forall cs G m m', 
      HT.smem_eq m m' -> valid cs G ((hinj p) m --> (hinj p) m').
    Proof.
      unfold hinj; intros. eapply Imply_I. eapply And_I.
      eapply And_E1. econstructor; left; reflexivity.
      unfold emp, hemp in *. simpl in *. eapply Inj_E. eapply And_E2.
      econstructor; left; reflexivity. intros; eapply Inj_I. 
      eapply HT.semp_mor; eauto. symmetry; eassumption. 
    Qed.

    Definition inj (p : PropX pcType stateType) : Hprop := Build_Hprop _ (hinj_respects p).
*)

    Definition emp {sos} : hprop sos := inj (PropX.Inj True).
(*
    Theorem hemp_respects : forall cs G m m', HT.smem_eq m m' -> 
      valid cs G (hemp m --> hemp m').
      intros; goPropX. unfold hemp. eapply Imply_I.
      generalize (Env cs0 ([|HT.semp m|]%PropX :: G) [|HT.semp m|]%PropX ).
      intros. eapply Inj_E. eapply H0. left. reflexivity.
      intros. rewrite H in H1. eapply Inj_I. auto.
    Qed.

    Definition emp : Hprop := Build_Hprop _ hemp_respects.
*)

    Definition star sos (l r : hprop sos) : hprop sos :=
      fun m => PropX.Exists (fun ml : HT.smem => PropX.Exists (fun mr : HT.smem =>
        PropX.And (PropX.Inj (HT.split m ml mr)) (And (l ml) (r mr)))).

(*
    Theorem hstar_respects (l r : Hprop) : forall cs G m m', HT.smem_eq m m' -> 
      valid cs G ((hstar l r) m --> (hstar l r) m').
    Proof.
      intros; unfold hstar in *. eapply Imply_I. eapply Exists_E.
      econstructor. left. reflexivity.
      intros; eapply Exists_E. econstructor; left; reflexivity.
      intros. eapply Exists_I. instantiate (1 := B). eapply Exists_I. instantiate (1 := B0).
      repeat eapply And_I.
      2: eapply And_E1; eapply And_E2; econstructor; left; reflexivity.
      2: eapply And_E2; eapply And_E2; econstructor; left; reflexivity.
      eapply Inj_E. eapply And_E1. econstructor. left. reflexivity.
      intros. rewrite H in H0. eapply Inj_I; auto.
    Qed.

    Definition star (l r : Hprop) : Hprop := Build_Hprop _ (hstar_respects l r).
*)
      
(*
    Definition cptr sos (stateMem : stateType -> H.mem) (p : pcType) 
      (t : stateType -> hprop sos) : hprop sos :=
      fun h => 
        PropX.And 
          (emp h)
          (PropX.Cptr p
            (fun x : stateType => PropX.Exists (fun m => 
              PropX.And (PropX.Inj (HT.satisfies m (stateMem x))) (t x m)))).
    Theorem hcptr_respects (stateMem : stateType -> H.mem) (p : pcType) (t : stateType -> Hprop) : 
      forall cs G m m', 
        HT.smem_eq m m' -> valid cs G ((hcptr stateMem p t) m --> (hcptr stateMem p t) m').
    Proof.
      unfold hcptr; intros. eapply Imply_I. eapply And_I.
      2: eapply And_E2; econstructor; left; reflexivity.
      eapply Imply_E. 2: eapply And_E1; econstructor; left; reflexivity. eapply Imply_I.
      generalize hemp_respects. intros. eapply H0 in H. eapply Imply_E. 2: eassumption.
      unfold hemp in *. clear. eapply Imply_I. 
      eapply Imply_E. econstructor; left; reflexivity. econstructor; right; left; reflexivity.
    Qed.

    Definition cptr (stateMem : stateType -> H.mem) (p : pcType) (t : stateType -> Hprop) : Hprop :=
      Build_Hprop _ (hcptr_respects stateMem p t).
*)
    Definition ex sos (T : Type) (p : T -> hprop sos) : hprop sos :=
      fun h => PropX.Exists (fun t => p t h).
(*    
    Definition hex_respects T (p : T -> Hprop) : forall cs G m m', 
      HT.smem_eq m m' -> valid cs G ((hex _ p) m --> (hex _ p) m').
    Proof.
      unfold hex; intros. eapply Imply_I. eapply Exists_E. econstructor; left; reflexivity.
      intros. eapply Exists_I. instantiate (1 := B). destruct (p B). simpl in *.
        specialize (respects0 cs0 G _ _ H). generalize respects0. clear. intros.
        eapply Imply_E. 2: econstructor; left; reflexivity.
        eapply valid_weaken. eassumption. clear.
        red. intros. simpl. tauto.
    Qed.

    Definition ex (T : Type) (p : T -> Hprop) : Hprop := Build_Hprop _ (hex_respects T p).
*)

    Definition hptsto sos (p : H.addr) (v : H.byte) : hprop sos :=
      fun h => PropX.And (PropX.Inj (HT.smem_get p h = Some v))
        (PropX.Forall (fun p' =>
          (PropX.Imply (PropX.Inj (p <> p')) (PropX.Inj (HT.smem_get p' h = None))))).

    (** Lemmas **)

    Lemma himp_star_comm : forall P Q, himp (star P Q) (star Q P).
    Proof.
      unfold star; doIt. apply Imply_I. eapply Exists_E. econstructor. left; auto.
      intros. eapply Exists_E. econstructor; left; auto. intros.
      do 2 eapply Exists_I. repeat eapply And_I.
      2: eapply And_E2; eapply And_E2; econstructor; left; auto.
      2: eapply And_E1; eapply And_E2; econstructor; left; auto.
      eapply Imply_E. 2: eapply And_E1; econstructor; left; eauto.
      eapply Imply_I. eapply Inj_E. econstructor; left; auto. intros.
      apply HT.split_comm in H. apply Inj_I. auto.
    Qed.      

    Theorem himp_star_comm_p : forall P Q R, himp (star P Q) R -> himp (star Q P) R.
    Proof.
      doIt. generalize (himp_star_comm Q P). intros. eapply Imply_I. eapply Imply_E.
      eapply interp_weaken in H. eassumption. specialize (H0 m).
      eapply Imply_E. eapply interp_weaken in H0. eapply H0. econstructor; left; auto.
    Qed.
    Theorem himp_star_comm_c : forall P Q R, himp R (star P Q) -> himp R (star Q P).
    Proof.
    Admitted.

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
(*
      doIt. apply HT.split_comm. apply HT.split_comm in H. eapply HT.split_assoc; try eassumption. 
      apply HT.split_comm. eassumption. eapply HT.disjoint_split_join.
      apply HT.disjoint_comm. eapply HT.split_split_disjoint; eauto.
      apply HT.split_comm in H0; eassumption.
*)
    Admitted.
    Theorem himp_star_assoc_c : forall P Q R S, 
      himp S (star P (star Q R)) -> himp S (star (star P Q) R).
    Proof.
(*
      doIt. eapply HT.split_assoc; eassumption. apply HT.split_comm.
      apply HT.disjoint_split_join. apply HT.disjoint_comm.
      eapply HT.split_split_disjoint. apply HT.split_comm. eassumption. eassumption.
*)
    Admitted.

    Theorem heq_star_assoc : forall P Q R S, 
      heq S (star P (star Q R)) -> heq S (star (star P Q) R).
    Proof.
(*
      intros. generalize (himp_star_assoc_p P Q R S). generalize (himp_star_assoc_c P Q R S).
      firstorder.
*)
    Admitted.

    Theorem himp_star_frame : forall P Q R S, himp P Q -> himp R S -> himp (star P R) (star Q S).
    Proof.
(*
      unfold himp; simpl; intros;
        repeat match goal with
                 | [ H : _ -> _ |- _ ] => apply H; clear H
                 | [ H : ?X -> _ , H' : ?X |- _ ] => apply H in H'; clear H
               end; goPropX.
      apply simplify_bwd in H2. apply simplify_bwd in H3. apply H in H2. apply H0 in H3. doIt.
      assumption.
*)
    Admitted.

    Theorem heq_star_frame : forall P Q R S, heq P Q -> heq R S -> heq (star P R) (star Q S).
    Proof.
(*
      intros; generalize (himp_star_frame P Q R S). generalize (himp_star_frame Q P S R).
      unfold heq in *. intuition.
*)
    Admitted.

    Theorem himp_star_emp_p : forall P Q, himp P Q -> himp (star emp P) Q.
    Proof.
(*
      unfold himp. intros. eapply H. unfold star in *. simpl in *.
      goPropX. apply simplify_bwd in H2. destruct P. simpl in *.
      eapply HT.split_semp in H1; eauto.
      apply simplify_fwd.  eapply Imply_E.  2: eassumption. eapply respects0. symmetry; auto.
*)
    Admitted.

    Theorem himp_star_emp_p' : forall P Q, himp (star emp P) Q -> himp P Q.
    Proof.
(*
      unfold himp. intros. eapply H. unfold star in *. simpl in *.
      goPropX. do 2 eexists. split. eapply HT.split_a_semp_a. split; eauto.
      eapply HT.semp_smem_emp.
*)
    Admitted.

    Theorem himp_star_emp_c : forall P Q, himp P Q -> himp P (star emp Q).
    Proof.
(*
      unfold himp. intros. eapply H in H0. unfold star in *. simpl in *.
      goPropX. do 2 eexists. split. eapply HT.split_a_semp_a. split; eauto.
      eapply HT.semp_smem_emp.
*)
    Admitted.

    Theorem himp_star_emp_c' : forall P Q, himp P (star emp Q) -> himp P Q.
    Proof.
(*
      unfold himp. intros. eapply H in H0. unfold star in *. simpl in *.
      goPropX. apply simplify_bwd in H2. destruct Q. simpl in *.
      eapply HT.split_semp in H1; eauto.
      apply simplify_fwd. unfold interp in *.
      eapply Imply_E. eapply respects0. symmetry; eassumption. auto.
*)
    Admitted.

    Theorem heq_star_emp : forall P Q, heq P Q -> heq (star emp P) Q.
    Proof.
(*
      intros. unfold heq in *; intuition.
      eapply himp_star_emp_p. auto.
      eapply himp_star_emp_c. auto.
*)
    Admitted.

    Theorem heq_star_emp' : forall P Q, heq (star emp P) Q -> heq P Q.
    Proof.
(*
      intros. unfold heq in *; intuition.
      eapply himp_star_emp_p' in H0. auto.
      eapply himp_star_emp_c' in H1. auto.
*)
    Admitted.

    Theorem himp_star_cancel : forall P Q R, himp Q R -> himp (star P Q) (star P R).
    Proof.
(*
      intros. eapply himp_star_frame. reflexivity. auto.
*)
    Admitted.

    Theorem heq_star_cancel : forall P Q R, heq Q R -> heq (star P Q) (star P R).
    Proof.
(*
      intros. eapply heq_star_frame. reflexivity. auto.
*)
    Admitted.

  End env.
End SepTheoryX.