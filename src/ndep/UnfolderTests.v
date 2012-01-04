Require Import Heaps Reflect.
Require Bedrock.ndep.SepExpr Bedrock.ndep.Expr Bedrock.ndep.Unfolder.
Import Bedrock.ndep.Expr.
Require Import EquivDec.
Require Import List.

Set Implicit Arguments.

Module Make (B : Heap).
  Module ST := SepTheoryX.SepTheoryX (B).
  Module U := Unfolder.Make B ST.

  (** Just a test separation logic predicate **)
  Section Tests.
    Variables pc state : Type.

    Variable f : nat -> ST.hprop pc state nil.
    Variable h : bool -> unit -> ST.hprop pc state nil.
    Variable g : bool -> nat -> nat -> nat.

    Ltac isConst e :=
      match e with
        | true => true
        | false => true
        | O => true
        | S ?e => isConst e
        | _ => false
      end.

    Definition nat_type := {|
      Impl := nat;
      Eq := fun x y => match equiv_dec x y with
                         | left pf => Some pf
                         | _ => None 
                       end
      |}.

    Hypothesis Hemp : forall cs, ST.himp cs (ST.emp pc state) (ST.emp pc state).
    Hypothesis Hf : forall cs, ST.himp cs (f 0) (ST.emp _ _).
    Hypothesis Hg : forall cs, ST.himp cs (h true tt) (ST.star (h true tt) (f 13)).

    Hypothesis Hf0 : forall n cs, ST.himp cs (f n) (ST.emp _ _).
    Hypothesis Hg0 : forall b u cs, ST.himp cs (h b u) (ST.star (h (negb b) tt) (f 13)).

    Hypothesis Hf1 : forall n, n <> 0 -> forall cs, ST.himp cs (f n) (ST.emp _ _).
    Hypothesis Hg1 : forall b u, b = false -> u <> tt -> forall cs, ST.himp cs (h b u) (ST.star (h b tt) (f 13)).

    Ltac prepare := U.prepareHints pc state isConst (nat_type :: nil).

    Definition hints_tt : U.hints.
      prepare tt tt.
    Defined.
    Print hints_tt.

    Definition hints_emp : U.hints.
      prepare Hemp Hemp.
    Defined.
    Print hints_emp.

    Definition hints_Hf : U.hints.
      prepare Hf Hemp.
    Defined.
    Print hints_Hf.

    Definition hints_Hg : U.hints.
      prepare (Hemp, Hf) (Hemp, Hf, Hg).
    Defined.
    Print hints_Hg.

    Definition hints_Hf0 : U.hints.
      prepare Hf0 tt.
    Defined.
    Print hints_Hf0.

    Definition hints_glom : U.hints.
      prepare (Hemp, Hf, Hg, Hf0) (Hemp, Hf0, tt).
    Defined.
    Print hints_glom.

    Definition hints_Hg0 : U.hints.
      prepare Hg0 tt.
    Defined.
    Print hints_Hg0.

    Definition hints_Hf1 : U.hints.
      prepare Hf1 tt.
    Defined.
    Print hints_Hf1.

    Definition hints_Hg1 : U.hints.
      prepare Hg1 tt.
    Defined.
    Print hints_Hg1.

  End Tests.

End Make.
