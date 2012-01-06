Require Import Heaps.
Require Import PropX PropXTac.
Require Import Env.
Require Import IL.

Require Import RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.

Module Type SepTheoryXType (H : Heap).
  
  Parameter hprop : forall (pcType stateType : Type), list Type -> Type.

Section Env.  
  Variable pcType : Type.
  Variable stateType : Type.

  Parameter satisfies : forall (cs : codeSpec pcType stateType) (p : hprop pcType stateType nil) (s : settings) (m : H.mem), Prop.
  
  Parameter himp : forall (cs : codeSpec pcType stateType), 
    hprop pcType stateType nil -> hprop pcType stateType nil -> Prop.

  Parameter heq : forall (cs : codeSpec pcType stateType), 
    hprop pcType stateType nil -> hprop pcType stateType nil -> Prop.

  Variable cs : codeSpec pcType stateType.

  Parameter Refl_himp : Reflexive (@himp cs).
  Parameter Trans_himp : Transitive (@himp cs).

  Parameter Refl_heq : Reflexive (@heq cs).
  Parameter Sym_heq : Symmetric (@heq cs).
  Parameter Trans_heq : Transitive (@heq cs).

  Notation "a ===> b" := (himp cs a b) (at level 60).
  Notation "a <===> b" := (heq cs a b) (at level 60).

  Parameter heq_defn : forall a b, (a ===> b /\ b ===> a) <-> a <===> b.

  Parameter heq_himp : forall a b, a <===> b -> a ===> b.
     
  (* Definitions *)
  Parameter inj : forall {sos} (p : propX pcType stateType sos), 
    hprop pcType stateType sos.

  Parameter emp : forall {sos}, hprop pcType stateType sos.

  Parameter star : forall {sos} (l r : hprop pcType stateType sos),
    hprop pcType stateType sos.

  Parameter ex : forall {sos} (T : Type) (p : T -> hprop pcType stateType sos),
    hprop pcType stateType sos.

  Parameter hptsto : forall {sos} (p : H.addr) (v : H.byte),
    hprop pcType stateType sos.

  (* satisfies lemmas *)
  Parameter satisfies_himp : forall cs P Q stn m,
    himp cs P Q ->
    satisfies cs P stn m ->
    satisfies cs Q stn m.

  Parameter satisfies_star : forall cs P Q stn m,
    satisfies cs (star P Q) stn m ->
    satisfies cs P stn m /\
    satisfies cs Q stn m.    

  (* himp/heq lemmas *)
  Parameter himp_star_comm : forall P Q, (star P Q) ===> (star Q P).

  Parameter himp_star_comm_p : forall P Q R, 
    (star P Q) ===> R -> (star Q P) ===> R.

  Parameter himp_star_comm_c : forall P Q R, 
    R ===> (star P Q) -> R ===> (star Q P).

  Parameter heq_star_comm : forall P Q R, 
    (star P Q) <===> R -> (star Q P) <===> R.
  
  Parameter himp_star_assoc_p : forall P Q R S,
    (star P (star Q R)) ===> S -> (star (star P Q) R) ===> S.

  Parameter himp_star_assoc_c : forall P Q R S, 
    S ===> (star P (star Q R)) -> S ===> (star (star P Q) R).

  Parameter heq_star_assoc : forall P Q R S, 
    (star P (star Q R)) <===> S -> (star (star P Q) R) <===> S.

  Parameter himp_star_frame : forall P Q R S, 
    P ===> Q -> R ===> S -> (star P R) ===> (star Q S).

  Parameter heq_star_frame : forall P Q R S, 
    P <===> Q -> R <===> S -> (star P R) <===> (star Q S).

  Parameter himp_subst_p : forall P Q R S,
    P ===> S -> (star S Q) ===> R ->
    (star P Q) ===> R.

  Parameter himp_subst_c : forall P Q R S,
    S ===> Q -> P ===> (star S R) ->
    P ===> (star Q R).

  Parameter heq_subst : forall P Q R S,
    P <===> S -> (star S Q) <===> R ->
    (star P Q) <===> R.

  Parameter himp_star_emp_p : forall P Q, P ===> Q -> (star emp P) ===> Q.

  Parameter himp_star_emp_p' : forall P Q, (star emp P) ===> Q -> P ===> Q.
    
  Parameter himp_star_emp_c : forall P Q, P ===> Q -> P ===> (star emp Q).

  Parameter himp_star_emp_c' : forall P Q, P ===> (star emp Q) -> P ===> Q.

  Parameter heq_star_emp : forall P Q, P <===> Q -> (star emp P) <===> Q.

  Parameter heq_star_emp' : forall P Q,
    (star emp P) <===> Q -> P <===> Q.

  Parameter himp_star_cancel : forall P Q R,
    Q ===> R -> (star P Q) ===> (star P R).

  Parameter heq_star_cancel : forall P Q R, 
    Q <===> R -> (star P Q) <===> (star P R).

  Parameter himp_ex_p : forall T (P : T -> _) Q, 
    (forall v, (P v) ===> Q) -> (ex P) ===> Q.

  Parameter himp_ex_c : forall T (P : T -> _) Q, 
    (exists v, Q ===> (P v)) -> Q ===> (ex P).

  Parameter heq_ex : forall T (P Q : T -> _), 
    (forall v, P v <===> Q v) ->
    ex P <===> ex Q.

  Parameter heq_ex_star : forall T (P : T -> _) Q,
    (star (ex P) Q) <===> (ex (fun x => star (P x) Q)).

  Parameter himp_ex_star : forall T (P : T -> _) Q,
    (star (ex P) Q) ===> (ex (fun x => star (P x) Q)).

  Parameter himp'_ex : forall T (P : T -> _) Q,
    (forall x, (P x) ===> Q) ->
    ex P ===> Q.

End Env.

Existing Instance Refl_himp. 
Existing Instance Trans_himp. 
Existing Instance Refl_heq.
Existing Instance Sym_heq. 
Existing Instance Trans_heq. 

End SepTheoryXType.


Module SepTheoryX (H : Heap) <: SepTheoryXType H.
  Module HT := HeapTheory H.

  Section env.
    Variable pcType : Type.    
    Variable stateType : Type.

    Definition hprop (sos : list Type) := settings -> HT.smem -> propX pcType stateType sos.

    Variable cs : codeSpec pcType stateType.

    Definition satisfies (p : hprop nil) (s : settings) (m : H.mem) : Prop :=
      exists sm, HT.satisfies sm m /\ interp cs (p s sm).

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

(*
    Theorem himp_heq : forall a b, himp a b -> himp b a -> heq a b.
    Proof.
      unfold heq; firstorder.
    Qed.
*)

    Theorem heq_defn : forall a b, (himp a b /\ himp b a) <-> heq a b.
    Proof.
      unfold heq; intuition.
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

  (* satisfies lemmas *)
  Theorem satisfies_himp : forall P Q stn m,
    himp P Q ->
    satisfies P stn m ->
    satisfies Q stn m.
  Proof.
    unfold himp, satisfies. intros.
    destruct H0. exists x. intuition.
  Qed.

  Lemma satisfies_star : forall P Q stn m,
    satisfies (star P Q) stn m ->
    satisfies P stn m /\
    satisfies Q stn m.
  Proof.
    unfold satisfies. intros.
    destruct H as [ ? [ ? ? ] ]. unfold star in *.
    eapply simplify_fwd in H0. simpl in H0.
    destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ].
    apply simplify_bwd in H1. apply simplify_bwd in H2.
    eapply HT.satisfies_split in H0; eauto.
    split; [ exists x0 | exists x1 ]; intuition.
  Qed.

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

    Lemma himp'_ex : forall T (P : T -> _) Q,
      (forall x, himp (P x) Q) ->
      himp (ex P) Q.
    Proof.
      clear. intros. unfold himp in *. propxFo. eauto.
    Qed.

      
  End env.
End SepTheoryX.