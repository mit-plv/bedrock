Require Import Heaps Memory.
Require Import PropX PropXTac.
Require Import RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.

Module Type SepTheoryXType.
  Declare Module H : Heap.
  
  Parameter hprop : forall (pcType stateType : Type), list Type -> Type.

  Module HT := HeapTheory H.

Section Env.  
  Variable pcType : Type.
  Variable stateType : Type.
  Parameter settings : Type.

  Parameter satisfies : forall (cs : codeSpec pcType stateType) (p : hprop pcType stateType nil) (s : settings) (m : HT.smem), Prop.
  
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

  Parameter hptsto : forall {sos} (p : H.addr) (v : B),
    hprop pcType stateType sos.

  (* satisfies lemmas *)
  Parameter satisfies_himp : forall cs P Q stn,
    himp cs P Q ->
    (forall m, 
     satisfies cs P stn m ->
     satisfies cs Q stn m).

  Parameter satisfies_star : forall cs P Q stn m,
    satisfies cs (star P Q) stn m <->
    exists ml, exists mr, 
      HT.split m ml mr /\
      satisfies cs P stn ml  /\ satisfies cs Q stn mr.

  Parameter satisfies_pure : forall cs p stn m,
    satisfies cs (inj p) stn m ->
    interp cs p /\ HT.semp m.

  (* himp/heq lemmas *)
  Parameter himp_star_comm : forall P Q, (star P Q) ===> (star Q P).

  Parameter himp_star_assoc : forall P Q R,
    (star (star P Q) R) ===> (star P (star Q R)).

  Parameter heq_star_comm : forall P Q, 
    (star P Q) <===> (star Q P).

  Parameter heq_star_assoc : forall P Q R, 
    (star (star P Q) R) <===> (star P (star Q R)).

  Parameter heq_star_emp_l : forall P, (star emp P) <===> P.
  Parameter heq_star_emp_r : forall P, (star P emp) <===> P.

  Parameter himp_star_frame : forall P Q R S, 
    P ===> Q -> R ===> S -> (star P R) ===> (star Q S).

  Parameter himp_star_pure_p : forall P Q F,
    (star (inj F) P) ===> Q -> (interp cs F -> P ===> Q).
  
  Parameter himp_star_pure_c : forall P Q (F : Prop),
    (F -> P ===> Q) -> (star (inj (PropX.Inj F)) P) ===> Q.

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

  Parameter himp_ex : forall T (P Q : T -> _), 
    (forall v, P v ===> Q v) ->
    ex P ===> ex Q.

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

Module SepTheoryX_Rewrites (Import ST : SepTheoryXType).
  
  Require Import Setoid Classes.Morphisms.
  
  Section env. 
    Variable p s : Type.
    Variable cs : codeSpec p s.

    Add Parametric Relation : (@hprop p s nil) (@himp p s cs)
      reflexivity proved by (Refl_himp cs)
      transitivity proved by (@Trans_himp p s cs)
    as himp_rel.

    Add Parametric Relation : (@hprop p s nil) (@heq p s cs)
      reflexivity proved by (Refl_heq cs)
      symmetry proved by (@Sym_heq p s cs)
      transitivity proved by (@Trans_heq p s cs)
    as heq_rel.

    Global Add Parametric Morphism : (@star p s nil) with
      signature (himp cs ==> himp cs ==> himp cs)
    as star_himp_mor.
      intros. eapply himp_star_frame; eauto.
    Qed.

    Global Add Parametric Morphism : (@star p s nil) with
      signature (heq cs ==> heq cs ==> heq cs)
    as star_heq_mor.
      intros. eapply heq_star_frame; eauto.
    Qed.

    Global Add Parametric Morphism T : (@ex p s nil T) with 
      signature (pointwise_relation T (heq cs) ==> heq cs)
    as ex_heq_mor.
      intros. eapply heq_ex. eauto.
    Qed.

    Global Add Parametric Morphism T : (@ex p s nil T) with 
      signature (pointwise_relation T (himp cs) ==> himp cs)
    as ex_himp_mor.
      intros. eapply himp_ex. auto.
    Qed.

    Global Add Parametric Morphism : (himp cs) with 
      signature (heq cs ==> heq cs ==> Basics.impl)
    as himp_heq_mor.
      intros. intro. etransitivity.
      symmetry in H. eapply heq_defn in H. eapply (proj1 H).
      etransitivity. eassumption. eapply heq_defn in H0. intuition.
    Qed.

(*
    Global Add Parametric Morphism : (himp cs) with 
      signature (heq cs ==> heq cs ==> Basics.flip Basics.impl)
    as himp_heq_mor'.
      intros. intro. etransitivity.
      symmetry in H. eapply heq_defn in H. eapply (proj2 H).
      etransitivity. eassumption. eapply heq_defn in H0. intuition.
    Qed.
*)

    Global Add Parametric Morphism : (himp cs) with 
      signature (himp cs --> himp cs ++> Basics.impl)
    as himp_himp_mor.
      intros. intro. repeat (etransitivity; eauto).
    Qed.

    Global Add Parametric Morphism : (satisfies cs) with
      signature (heq cs ==> @eq _ ==> @eq _ ==> Basics.impl)
    as heq_satsifies_mor.
      intros. intro. eapply satisfies_himp; eauto. eapply heq_defn in H.
      tauto.
    Qed.

  End env.

  Hint Rewrite heq_star_emp_l heq_star_emp_r : hprop.
  Existing Instance himp_rel_relation.
  Existing Instance heq_rel_relation.

End SepTheoryX_Rewrites.
