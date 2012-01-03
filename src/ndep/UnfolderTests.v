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

    Definition nat_type : Expr.type :=
      {| Expr.Impl := nat 
       ; Expr.Eq := fun x y => match equiv_dec x y with
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

    Ltac prepare x := U.prepareHints pc state isConst x (@nil type).

    Definition hints0 : list type.
      prepare tt.
      prepare Hemp.
      prepare Hf.
      prepare (Hemp, Hf).
      prepare (Hemp, Hf, Hg).

      prepare Hf0.
      prepare (Hemp, Hf, Hg, Hf0).

      prepare Hg0.

      prepare Hf1.
      prepare Hg1.
    Abort.

  End Tests.

End Make.
