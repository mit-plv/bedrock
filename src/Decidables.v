Require Import List EqdepClass.
Require Export EquivDec.

Set Implicit Arguments.
Set Strict Implicit.

Theorem EquivDec_refl_left (T : Type) {c : EqDec T (@eq T)} :
  forall (n : T), equiv_dec n n = left (refl_equal _).
Proof.
  intros. destruct (equiv_dec n n); try congruence.
  Require Eqdep_dec.
  rewrite (Eqdep_dec.UIP_dec (A := T) (@equiv_dec _ _ _ c) e (refl_equal _)).
  reflexivity.
Qed.

Class SemiDec (t : Type) : Type :=
{ seq_dec : forall a b : t, option (a = b) }.
Global Instance EquivDec_SemiDec t (EQ : EqDec t (@eq t)) : SemiDec t :=
{ seq_dec := fun a b =>
  match equiv_dec a b with
    | left pf => Some pf
    | right _ => None
  end 
}.

Global Instance EquivDec_nat : EqDec nat (@eq nat) :=
  Peano_dec.eq_nat_dec.  

Global Instance SemiDec_option T (S : SemiDec T) : SemiDec (option T) :=
{ seq_dec := fun a b =>
  match a as a, b as b return option (a = b) with
    | None , None => Some (refl_equal _)
    | Some x , Some y => 
      match seq_dec x y with
        | None => None
        | Some pf => 
          match pf in _ = t return option (Some x = Some t) with
            | refl_equal => Some (refl_equal _)
          end
      end
    | _ , _ => None
  end
}.

Global Instance SemiDec_list T (S : SemiDec T) : SemiDec (list T) :=
{ seq_dec := fix seq_dec' a b : option (a = b) :=
  match a as a, b as b return option (a = b) with
    | nil , nil => Some (refl_equal _)
    | x :: xs , y :: ys => 
      match seq_dec x y with
        | None => None
        | Some pf => 
          match seq_dec' xs ys with
            | None => None
            | Some pf' => 
              match pf in _ = t , pf' in _ = t' return option (x :: xs = t :: t') with
                | refl_equal , refl_equal => Some (refl_equal _)
              end
          end
      end
    | _ , _ => None
  end
}.

Inductive dcomp T (a b : T) : Type :=
| Lt | Gt | Eq : a = b -> dcomp a b.

Class Comparable (t : Type) : Type :=
{ cmp_dec : forall a b : t, dcomp a b }.
Class SemiComparable (t : Type) : Type :=
{ scmp_dec : forall a b : t, option (dcomp a b) }.
Global Instance Comparable_SemiComparable t (SC : Comparable t) 
  : SemiComparable t :=
{ scmp_dec := fun a b => Some (cmp_dec a b) }.

Global Instance Comparable_nat : Comparable nat :=
{| cmp_dec :=
   fun a b => match Compare_dec.lt_eq_lt_dec a b with
                | inleft (left _) => Lt _ _
                | inleft (right pf) => Eq pf
                | inright _ => Gt _ _
              end
|}.