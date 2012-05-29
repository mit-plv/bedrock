Require Setoid. 

(** This file defines some inductives, type-classes and tactics to
perform reflection on a small scale *) 

(** Two inductives to perform case-based reasonning *)
Inductive reflect (P : Prop) : bool -> Type := 
| reflect_true : P -> reflect P true 
| reflect_false : ~ P -> reflect P false.

Inductive semi_reflect (P : Prop) : bool -> Type :=
  | semi_reflect_true : P -> semi_reflect P true
  | semi_reflect_false : semi_reflect P false. 

Lemma equiv_to_reflect {A B} (P : A -> B -> Prop) (T : A -> B -> bool)  : 
  (forall x y, T x y = true <-> P x y) ->
  (forall x y, reflect (P x y) (T x y)). 
Proof. 
  intros. case_eq (T x y); intros Hxy; constructor.
  rewrite <- H; auto.  
  intros Hf;   rewrite <- H, Hxy in Hf; discriminate. 
Qed. 

Lemma reflect_true_inv P : reflect P true -> P.
Proof. 
  exact (fun x => match x in reflect _ b 
                    return if b then P else ID
                 with | reflect_true H => H | reflect_false H => (fun _ x => x) end). 
Qed.

Lemma reflect_false_inv P : reflect P false -> ~ P.
Proof. 
  exact (fun x => match x in reflect _ b 
                    return if b then ID else ~P
                 with | reflect_true H => fun _ x => x | reflect_false H => H end). 
Qed.

Lemma semi_reflect_true_inv P : semi_reflect P true -> P.
Proof. 
  exact (fun x => match x in semi_reflect _ b 
                    return if b then P else ID
                 with | semi_reflect_true H => H | semi_reflect_false => (fun _ x => x) end). 
Qed.


Class Reflect (T : bool) (P : Prop) := _Reflect : reflect P T. 
Class SemiReflect (T : bool) (P : Prop) := _SemiReflect : semi_reflect P T. 

Section boolean_logic. 
  Ltac t :=
    repeat match goal with 
           | H: Reflect true ?P |- _ => apply (reflect_true_inv P) in H
           | H: Reflect false ?P  |- _ => apply (reflect_false_inv P) in H
           end. 

  Context {T1 T2 P1 P2} {R1 : Reflect T1 P1} {R2: Reflect T2 P2}.   

  Global Instance Reflect_andb : Reflect (T1 && T2)%bool (P1 /\ P2). 
  Proof. 
    destruct T1; destruct T2; t; constructor; tauto. 
  Qed.     
  
  Global Instance Reflect_orb : Reflect (T1 || T2)%bool (P1 \/ P2). 
  Proof. 
    destruct T1; destruct T2; t; constructor; tauto. 
  Qed.     

  Global Instance Reflect_negb : Reflect (negb T1)%bool (~P1). 
  Proof. 
    destruct T1; t; constructor; tauto. 
  Qed.     

End boolean_logic. 

Require Arith.  
Section reflect_peano.
  
  Global Instance Reflect_eqb_nat x y : Reflect (EqNat.beq_nat x y) (x = y). 
  Proof. 
    apply equiv_to_reflect. 
    apply EqNat.beq_nat_true_iff. 
  Qed. 

  Global Instance Reflect_leb_nat x y : Reflect (NPeano.leb x y) (x <= y). 
  Proof. 
    apply equiv_to_reflect. 
    apply NPeano.leb_le. 
  Qed. 

  Global Instance Reflect_ltb_nat x y : Reflect (NPeano.ltb x y) (x < y). 
  Proof. 
    apply equiv_to_reflect. 
    apply NPeano.ltb_lt. 
  Qed. 
End reflect_peano.

(** The main tactic. [consider f] will perform case-analysis (using
[case]) on the function symbol [f] using a reflection-lemma that is
inferred by type-class resolution. *)

Ltac consider f :=
  let rec clean := 
      match goal with 
       | |- true = true -> _ => intros _ ; clean
       | |- false = true -> _ => discriminate
       | |- ?P1 -> ?P2 => 
         let H := fresh in intros H ; clean; revert H 
       | |- _ => idtac
      end in 
    ((let c := constr:(_ : Reflect f _) in 
      case c; 
      let H := fresh in 
      intros H; try rewrite H; revert H
    ) ); clean. 

(**  Some tests *)
Section test. 
  Require Import NPeano Bool.
  Instance Reflect_ltb x y : Reflect (ltb x y) (x < y). 
  Proof. 
  Admitted. 

  Goal forall x y z,  (ltb x y && ltb y z) = true ->
                 ltb x z = true. 
  intros x y z.
  consider (ltb x y && ltb y z).
  Abort. 

End test.  

(** A more powerful tactic that takes as argument a tuple of functions
  symbols, and use the fact that some reflection lemmas have been declared for them *)

(* NOT YET PORTED
Ltac t L :=
  let rec foo l := 
      match l with 
        | (?t,?q) => case (_test (t _)); foo q 
        | (?t,?q) => case (_test (t _ _)); foo q 
        | (?t,?q) => case (_test (t _ _ _)); foo q 
        | (?t,?q) => case (_test (t _ _ _ _)); foo q 
    
        | tt => idtac 
      end  in 
    foo L;
  intros;
  repeat match goal with 
           | H : true = true |- _ => clear H
           | H : false = false |- _ => clear H
           | H : true = false |- _ => clear - H; discriminate
           | H : false = true |- _ => clear - H; discriminate
         end.
*)























