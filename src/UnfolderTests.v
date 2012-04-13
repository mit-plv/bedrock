Require Import Heaps Reflect.
Require SepExpr Expr Unfolder.
Require Decidables.
Import Expr.
Require Import EquivDec.
Require Import List.

Set Implicit Arguments.

Module Make (ST : SepTheoryX.SepTheoryXType).
  Module SEP := SepExpr.Make ST.
  Module U := Unfolder.Make SEP.
  Module PACK := U.PACK.

  (** Just some test separation logic predicates **)
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

    Definition env0 : PACK.TypeEnv (Env.listToRepr ({| Impl := pc ; Eq := fun _ _ => None |} :: {| Impl := state ; Eq := fun _ _ => None |} :: nil) EmptySet_type) (tvType 0) (tvType 1) :=
      {| PACK.Types := Env.nil_Repr EmptySet_type
       ; PACK.Funcs := fun ts => Env.nil_Repr (Default_signature _)
       ; PACK.Preds := fun ts => Env.nil_Repr (SEP.Default_predicate _ _ _)
      |}.

    Fixpoint assumptionProver (types : list type) (Hs : list (expr types)) (P : expr types) :=
      match Hs with
        | nil => false
        | H :: Hs' => match expr_seq_dec H P with
                        | Some _ => true
                        | None => assumptionProver Hs' P
                      end
      end.

    Hypothesis Hemp : forall cs, ST.himp cs (ST.emp pc state) (ST.emp pc state).
    Hypothesis Hf : forall cs, ST.himp cs (f 0) (ST.emp _ _).
    Hypothesis Hh : forall cs, ST.himp cs (h true tt) (ST.star (h true tt) (f 13)).

    Hypothesis Hf0 : forall n cs, ST.himp cs (f n) (ST.emp _ _).
    Hypothesis Hh0 : forall b u cs, ST.himp cs (h b u) (ST.star (h (negb b) tt) (f 13)).

    Hypothesis Hf1 : forall n, n <> 0 -> forall cs, ST.himp cs (f n) (ST.emp _ _).
    Hypothesis Hh1 : forall b u, b = false -> u <> tt -> forall cs, ST.himp cs (h b u) (ST.star (h b tt) (f 13)).


    (** * Creating hint databases *)

    Ltac prepare := U.prepareHints ltac:(fun x => x) pc state isConst env0.

    Definition hints_tt : U.hints.
      prepare tt tt ltac:(fun x => refine x).
    Defined.
    (*Print hints_tt.*)

    Definition hints_emp : U.hints.
      prepare Hemp Hemp ltac:(fun x => refine x).
    Defined.
    (*Print hints_emp.*)

    Definition hints_Hf : U.hints.
      prepare Hf Hemp ltac:(fun x => refine x).
    Defined.
    (* Print hints_Hf. *)

    Definition hints_Hh : U.hints.
      prepare (Hemp, Hf) (Hemp, Hf, Hh) ltac:(fun x => refine x).
    Defined.
    (* Print hints_Hh. *)

    Definition hints_Hf0 : U.hints.
      prepare Hf0 tt ltac:(fun x => refine x).
    Defined.
    (* Print hints_Hf0. *)

    Definition hints_glom : U.hints.
      prepare (Hemp, Hf, Hh, Hf0) (Hemp, Hf0, tt) ltac:(fun x => refine x).
    Defined.
    (* Print hints_glom. *)

    Definition hints_Hh0 : U.hints.
      prepare Hh0 tt ltac:(fun x => refine x).
    Defined.
    (* Print hints_Hh0. *)

    Definition hints_Hf1 : U.hints.
      prepare Hf1 tt ltac:(fun x => refine x).
    Defined.
    (* Print hints_Hf1. *)

    Definition hints_Hh1 : U.hints.
      prepare Hh1 tt ltac:(fun x => refine x).
    Defined.
    (* Print hints_Hh1. *)


    (** * Simplifying some goals *)

    Import U.
    Import SEP.

    Ltac exec hs := cbv beta iota zeta delta [SEP.hash forallEach Vars UVars Heap
      forward backward unfoldForward unfoldBackward fmFind Unfolder.FM.fold
        SEP.impures SEP.pures SEP.other
        Unfolder.FM.add star_SHeap multimap_join liftSHeap
        SepExpr.FM.empty SepExpr.FM.map SepExpr.FM.find ExprUnify.empty_Subst
        app rev_append map length Compare_dec.lt_eq_lt_dec
        findWithRest findWithRest' find Forward Backward
        Types PcType StateType Hints Lhs Rhs
        equiv_dec ExprUnify.exprUnifyArgs ExprUnify.fold_left_2_opt
        ExprUnify.exprUnify exprSubstU sheapSubstU EqDec_tvar tvar_rec tvar_rect sumbool_rec sumbool_rect
        eq_rec_r eq_rec eq_rect eq_sym f_equal ExprUnify.get_Eq 
        nth_error value error Eq liftExpr Decidables.seq_dec ExprUnify.Subst_lookup SHeap_empty
        exists_subst ExprUnify.env_of_Subst fst snd tvarD sexprD
        Impl sheapD starred fold_right applyD
        SEP.SDomain SEP.SDenotation exprD Domain Range Denotation
        ExprUnify.Subst Compare_dec.lt_dec Compare_dec.le_dec Foralls plus minus
        Compare_dec.le_gt_dec Compare_dec.le_lt_dec
        ExprUnify.Subst_replace SemiDec_expr expr_seq_dec
        lookupAs projT1 projT2 Unfolder.allb andb Hyps
        substExpr substSexpr tvar_val_sdec

        hs
        Peano_dec.eq_nat_dec nat_eq_eqdec nat_rec nat_rect
        bool_eqdec Bool.bool_dec bool_rec bool_rect
        unit_eqdec unit_rec unit_rect
        assumptionProver EquivDec_nat EquivDec_bool substV Impl_
        SEP.hash'
        Prover.Prove Provers.reflexivityProver
        Prover.Summarize 
        Provers.reflexivityProve expr_seq_dec
    ].

    Ltac unfolder' hs n := U.unfolder isConst hs n.
    Ltac unfolder hs := unfolder' hs 10; exec hs.
    Ltac unfolder_noexec hs := unfolder' hs 10.

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
      prepare (Hf, Hh') tt ltac:(fun x => refine x).
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
      prepare (fex, hgo) tt ltac:(fun x => refine x).
    Defined.

    Theorem test_fex : forall cs, ST.himp cs (f 0) (ST.emp _ _).
      Time unfolder hints_fex.
      reflexivity.
    Qed.


    (** Backward time! *)

    Hypothesis Hb_f : forall cs, ST.himp cs (ST.emp _ _) (f 0).
  
    Definition hints_Hb_f : U.hints.
      prepare tt Hb_f ltac:(fun x => refine x).
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
      prepare f02 f21 ltac:(fun x => refine x).
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
      prepare tt Hb_f0 ltac:(fun x => refine x).
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
      prepare tt (fexb, hgob) ltac:(fun x => refine x).
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
      prepare tt (fexb, fexb', hgob) ltac:(fun x => refine x).
    Defined.

    Theorem test_fexb'' : forall cs, ST.himp cs (ST.emp _ _) (ST.star (f 0) (f 1)).
      Time unfolder hints_fexb'.
      exists true; exists tt; reflexivity.
    Qed.


    (** * Pure conjuncts *)

    Ltac easy := intros; hnf; PropXTac.propxFo.

    Theorem simple : forall cs, ST.himp cs (ST.inj (PropX.Inj True)) (ST.inj (PropX.Inj (pc := pc) (state := state) (1 = 1))).
      Time unfolder hints_tt.
    Abort.

    Hypothesis Hf1' : False -> forall cs, ST.himp cs (f 0) (ST.emp _ _).

    Definition hints_Hf1' : U.hints.
      prepare Hf1' tt ltac:(fun x => refine x).
    Defined.

    Theorem test_Hf1' : forall cs, ST.himp cs (ST.star (ST.inj (PropX.Inj False)) (f 0)) (ST.emp _ _).
      Time unfolder hints_Hf1'.
    Abort.
    

    Theorem test_Hf1'_bad : forall cs, ST.himp cs (ST.star (ST.inj (PropX.Inj True)) (f 0)) (ST.emp _ _).
      Time unfolder hints_Hf1'.
    Abort.

    Hypothesis Hf_eq0 : 0 = 0 -> forall cs, ST.himp cs (f 0) (ST.emp _ _).

    Definition hints_Hf_eq0 : U.hints.
      prepare Hf_eq0 tt ltac:(fun x => refine x).
    Defined.

    Theorem test_Hf_eq0 : forall cs, ST.himp cs (ST.star (ST.inj (PropX.Inj (0 = 0))) (f 0)) (ST.emp _ _).
      Time unfolder hints_Hf_eq0.
    Abort.

    Theorem test_Hf_eq0_wrong : forall cs, ST.himp cs (ST.star (ST.inj (PropX.Inj (0 <> 0))) (f 0)) (ST.emp _ _).
      Time unfolder hints_Hf_eq0.
    Abort.

    Hypothesis Hf_eqn : forall n, n = n -> forall cs, ST.himp cs (f n) (ST.emp _ _).

    Definition hints_Hf_eqn : U.hints.
      prepare Hf_eqn tt ltac:(fun x => refine x).
    Defined.

    Theorem test_Hf_eqn : forall n cs, ST.himp cs (ST.star (ST.inj (PropX.Inj (n = n))) (f n)) (ST.emp _ _).
      Time unfolder hints_Hf_eqn.
    Abort.

    Theorem test_Hf_eqn_wrong : forall n cs, ST.himp cs (ST.star (ST.inj (PropX.Inj (n <> n))) (f n)) (ST.emp _ _).
      Time unfolder hints_Hf_eqn.
      (* Also broken by change to [himp] *)
    Abort.

    (** Reflection performance testing *)

    Fixpoint many_f n :=
      match n with
        | O => f 0
        | S n' => ST.star (f 0) (many_f n')
      end.

    Theorem test_many : forall cs, ST.himp cs (many_f 19) (ST.emp _ _).
      simpl.
      Time unfolder' hints_Hf 20; exec hints_Hf.
      easy.
    Qed.

  End Tests.

End Make.
