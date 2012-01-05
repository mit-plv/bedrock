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

    Definition bool_type := {|
      Impl := bool;
      Eq := fun x y => match equiv_dec x y with
                         | left pf => Some pf
                         | _ => None 
                       end
      |}.

    Definition unit_type := {|
      Impl := unit;
      Eq := fun x y => match equiv_dec x y with
                         | left pf => Some pf
                         | _ => None 
                       end
      |}.

    Definition types0 := nat_type :: bool_type :: unit_type :: nil.

    Definition nullProver (types : list type) (_ : list (expr types)) (_ : expr types) := false.

    Hypothesis Hemp : forall cs, ST.himp cs (ST.emp pc state) (ST.emp pc state).
    Hypothesis Hf : forall cs, ST.himp cs (f 0) (ST.emp _ _).
    Hypothesis Hh : forall cs, ST.himp cs (h true tt) (ST.star (h true tt) (f 13)).

    Hypothesis Hf0 : forall n cs, ST.himp cs (f n) (ST.emp _ _).
    Hypothesis Hh0 : forall b u cs, ST.himp cs (h b u) (ST.star (h (negb b) tt) (f 13)).

    Hypothesis Hf1 : forall n, n <> 0 -> forall cs, ST.himp cs (f n) (ST.emp _ _).
    Hypothesis Hh1 : forall b u, b = false -> u <> tt -> forall cs, ST.himp cs (h b u) (ST.star (h b tt) (f 13)).


    (** * Creating hint databases *)

    Ltac prepare := U.prepareHints pc state isConst types0 nullProver.

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

    Definition hints_Hh : U.hints.
      prepare (Hemp, Hf) (Hemp, Hf, Hh).
    Defined.
    Print hints_Hh.

    Definition hints_Hf0 : U.hints.
      prepare Hf0 tt.
    Defined.
    Print hints_Hf0.

    Definition hints_glom : U.hints.
      prepare (Hemp, Hf, Hh, Hf0) (Hemp, Hf0, tt).
    Defined.
    Print hints_glom.

    Definition hints_Hh0 : U.hints.
      prepare Hh0 tt.
    Defined.
    Print hints_Hh0.

    Definition hints_Hf1 : U.hints.
      prepare Hf1 tt.
    Defined.
    Print hints_Hf1.

    Definition hints_Hh1 : U.hints.
      prepare Hh1 tt.
    Defined.
    Print hints_Hh1.


    (** * Simplifying some goals *)

    Import U.
    Import SE.

    Ltac exec hs := cbv beta iota zeta delta [hash forallEach Vars UVars Heap
      forward backward unfoldForward unfoldBackward fmFind Unfolder.FM.fold
        impures pures other
        Unfolder.FM.add star_SHeap multimap_join liftSHeap
        SepExpr.FM.empty SepExpr.FM.map SepExpr.FM.find ExprUnify.empty_Subst
        app rev_append map length Compare_dec.lt_eq_lt_dec
        findWithRest findWithRest' find Forward Backward
        Types Functions PcType StateType SFunctions Hints Lhs Rhs
        equiv_dec ExprUnify.exprUnifyArgs ExprUnify.fold_left_2_opt
        ExprUnify.exprUnify exprSubstU sheapSubstU EqDec_tvar tvar_rec tvar_rect sumbool_rec sumbool_rect
        eq_rec_r eq_rec eq_rect eq_sym f_equal ExprUnify.get_Eq defaultType
        nth_error value error Eq liftExpr Env.seq_dec ExprUnify.Subst_lookup SHeap_empty
        exists_subst ExprUnify.env_of_Subst fst snd tvarD sexprD
        Impl sheapD starred fold_right applyD
        SDomain SDenotation exprD Domain Range Denotation
        ExprUnify.Subst Compare_dec.lt_dec Compare_dec.le_dec Foralls plus minus
        Compare_dec.le_gt_dec Compare_dec.le_lt_dec
        ExprUnify.Subst_replace SemiDec_expr expr_seq_dec
        lookupAs projT1 projT2 Unfolder.allb Prover Hyps
        substExpr substSexpr

        hs
        Peano_dec.eq_nat_dec nat_eq_eqdec nat_rec nat_rect
        bool_eqdec Bool.bool_dec bool_rec bool_rect
        unit_eqdec unit_rec unit_rect
        nullProver].

    Ltac unfolder hs := U.unfolder isConst hs 10; exec hs.

    Theorem f_easy : forall cs, ST.himp cs (f 0) (ST.emp _ _).
      Time unfolder hints_Hf.
      reflexivity.
    Qed.

    Theorem f_easy2 : forall cs, ST.himp cs (ST.star (f 0) (f 0)) (ST.emp _ _).
      Time unfolder hints_Hf.
      reflexivity.
    Qed.

    Theorem f_easy3 : forall cs, ST.himp cs (ST.star (f 0) (ST.star (f 0) (f 0))) (ST.emp _ _).
      Time unfolder hints_Hf.
      reflexivity.
    Qed.

    Hypothesis Hh' : forall cs, ST.himp cs (h true tt) (ST.emp _ _).

    Definition hints_Hf_Hh' : U.hints.
      prepare (Hf, Hh') tt.
    Defined.

    Theorem f_and_h : forall cs, ST.himp cs (ST.star (h true tt) (f 0)) (ST.emp _ _).
      Time unfolder hints_Hf_Hh'.
      reflexivity.
    Qed.

    Theorem f0 : forall cs, ST.himp cs (f 42) (ST.emp _ _).
      Time unfolder hints_Hf0.
      reflexivity.
    Qed.

    Theorem f04 : forall cs, ST.himp cs (ST.star (ST.star (f 42) (f 42)) (ST.star (f 42) (f 42))) (ST.emp _ _).
      Time unfolder hints_Hf0.
      reflexivity.
    Qed.

    Hypothesis fex : forall cs, ST.himp cs (f 0) (ST.ex (fun b => h b tt)).
    Hypothesis hgo : forall b u cs, ST.himp cs (h b u) (ST.emp _ _).

    Definition hints_fex : U.hints.
      prepare (fex, hgo) tt.
    Defined.

    Theorem test_fex : forall cs, ST.himp cs (f 0) (ST.emp _ _).
      Time unfolder hints_fex.
      reflexivity.
    Qed.


    (** Backward time! *)

    Hypothesis Hb_f : forall cs, ST.himp cs (ST.emp _ _) (f 0).
  
    Definition hints_Hb_f : U.hints.
      prepare tt Hb_f.
    Defined.

    Theorem test_Hb_f : forall cs, ST.himp cs (ST.emp _ _) (f 0).
      Time unfolder hints_Hb_f.
      reflexivity.
    Qed.

    Theorem test_Hb_f3 : forall cs, ST.himp cs (ST.emp _ _) (ST.star (f 0) (ST.star (f 0) (f 0))).
      Time unfolder hints_Hb_f.
      reflexivity.
    Qed.

    Hypothesis f02 : forall cs, ST.himp cs (f 0) (f 2).
    Hypothesis f21 : forall cs, ST.himp cs (f 2) (f 1).

    Definition hints_f2 : U.hints.
      prepare f02 f21.
    Defined.

    Theorem test_f2 : forall cs, ST.himp cs (f 0) (f 1).
      Time unfolder hints_f2.
      reflexivity.
    Qed.

    Theorem test_f2' : forall cs, ST.himp cs (ST.star (f 0) (ST.star (f 0) (f 0))) (ST.star (ST.star (f 1) (f 1)) (f 1)).
      Time unfolder hints_f2.
      reflexivity.
    Qed.

    Hypothesis Hb_f0 : forall n cs, ST.himp cs (ST.emp _ _) (f n).

    Definition hints_Hb_f0 : U.hints.
      prepare tt Hb_f0.
    Defined.

    Theorem test_Hb_f0 : forall cs, ST.himp cs (ST.emp _ _) (f 42).
      Time unfolder hints_Hb_f0.
      reflexivity.
    Qed.

    Theorem test_Hb_f0' : forall cs, ST.himp cs (ST.emp _ _) (ST.star (f 42) (f 19)).
      Time unfolder hints_Hb_f0.
      reflexivity.
    Qed.

    Hypothesis fexb : forall cs, ST.himp cs (ST.ex (fun b => ST.star (h b tt) (h b tt))) (f 0).
    Hypothesis hgob : forall u b cs, ST.himp cs (ST.emp _ _) (h b u).

    Definition hints_fexb : U.hints.
      prepare tt (fexb, hgob).
    Defined.

    Theorem test_fexb : forall cs, ST.himp cs (ST.emp _ _) (f 0).
      Time unfolder hints_fexb.
      exists true; reflexivity.
    Qed.

    Theorem test_fexb' : forall cs, ST.himp cs (ST.emp _ _) (ST.star (f 0) (f 0)).
      Time unfolder hints_fexb.
      repeat exists true; reflexivity.
    Qed.

    Hypothesis fexb' : forall cs, ST.himp cs (ST.ex (fun u => h true u)) (f 1).

    Definition hints_fexb' : U.hints.
      prepare tt (fexb, fexb', hgob).
    Defined.

    Theorem test_fexb'' : forall cs, ST.himp cs (ST.emp _ _) (ST.star (f 0) (f 1)).
      Time unfolder hints_fexb'.
      exists true; exists tt; reflexivity.
    Qed.

  End Tests.

End Make.
