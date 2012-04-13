Require Import AutoSep.

(** A very basic abstract predicate: pairs of words *)

Module Type PAIR.
  Parameter pair : W -> W -> W -> HProp.

  Axiom pair_extensional : forall a b p, HProp_extensional (pair a b p).

  Axiom pair_fwd : forall a b p,
    pair a b p ===> p =*> a * p =*> b.

  Axiom pair_bwd : forall a b p,
    p =*> a * p =*> b ===> pair a b p.
End PAIR.

Module Pair : PAIR.
  Open Scope Sep_scope.

  Definition pair (a b p : W) : HProp :=
    p =*> a * p =*> b.

  Theorem pair_extensional : forall a b p, HProp_extensional (pair a b p).
    reflexivity.
  Qed.

  Theorem pair_fwd : forall a b p,
    pair a b p ===> p =*> a * p =*> b.
    sepLemma.
  Qed.

  Theorem pair_bwd : forall a b p,
    p =*> a * p =*> b ===> pair a b p.
    sepLemma.
  Qed.
End Pair.

Import Pair.
Hint Immediate pair_extensional.

Definition firstS : assert := st ~> ExX, Ex a, Ex b, ![ ^[pair a b st#Rv] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = a |] /\ ![ ^[pair a b st#Rv] * #1 ] st').

Definition pair := bmodule "pair" {{
  bfunction "first" [firstS] {
    Return $[Rv]
  }
}}.

Definition hints_pair' : TacPackage.
  let env := eval simpl SymIL.EnvOf in (SymIL.EnvOf auto_ext) in
  prepare env pair_fwd pair_bwd ltac:(fun x =>
    SymIL.Package.build_hints_pack x ltac:(fun x => 
      SymIL.Package.glue_pack x auto_ext ltac:(fun x => refine x))).
Defined.

Definition hints_pair : TacPackage.
  let v := eval unfold hints_pair' in hints_pair' in
  let v := eval simpl in v in
  refine v.
Defined.

Theorem pairOk : moduleOk pair.
  vcgen.
  sep hints_pair.
  evaluate hints_pair.
  repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
         end.
  Print Ltac sep.
  descend. step hints_pair. step hints_pair. descend.
    Theorem substH_lift1_eatLast : forall T U (P : HProp) p,
      HProp_extensional P ->
      substH (sos := eatLast (T :: U :: nil)) (^[P])%Sep p = P.
    Proof.
      intros. simpl. rewrite substH_lift1; auto.
    Qed.
    Hint Rewrite substH_lift1_eatLast using (solve [ auto ]) : sepFormula.
Programming.ho unf. reduce.



Programming.reduce unf.
  Print Ltac step.
 step hints_pair. descend.
  


  cancel hints_pair.

  cbv beta iota zeta delta [
    eq_sym SEP.SDenotation ].
Print hints_pair.

Require Import Setoid Classes.Morphisms.
specialize (H3 (stn, st)).

autorewrite with sepFormula in H3.
Print substH.

    Require Import PropXRel.

Global Add Parametric Morphism pc st cs : (@And pc st nil) with
    signature (PropX_eq pc st cs ==> PropX_eq pc st cs ==> PropX_eq pc st cs)
  as And_mor.
Admitted.
    
    Global Add Parametric Morphism pcT stT (cs : codeSpec pcT stT) : (himp cs) with 
      signature (heq cs ==> @eq _ ==> Basics.impl)
    as himp_heq_mor.
    Admitted.

    rewrite substH_lift_a in H3.
Lemma pointwise.

Global Add Parametric Morphism pcT stT (cs : codeSpec pcT stT) : (himp cs) with 
      signature (heq cs ==> @eq _ ==> Basics.impl)
    as himp_heq_mor.
Admitted.
    Locate "^[ _ ]".
    Check subst.
    Print lift.

    rewrite substH_lift_a.


autorewrite with sepFormula in H3.
             
  SymIL.sym_eval ltac:SymIL.isConst hints_pair ltac:(fun H => idtac).
  
  cbv beta zeta iota delta [ 
    hints_pair
    SymIL.Algos SymIL.Types SymIL.Preds SymIL.MemEval
    SymIL.Prover SymIL.Hints ] in H1.
  Set Printing Depth 80.
  sym_eval_simplifier H1.
  cbv beta iota zeta delta [ rev_append ] in H1.
  About substSexpr.
  cbv beta iota zeta delta [ SEP.hash substSexpr ] in H1.
  SEP.star_SHeap SEP.liftSHeap SEP.multimap_join map substExpr SEP.hash'
  


  (* Stuck here: need to create a hint database in the fancy new form expected by [sep]. *)
  admit.
  admit.
Qed.
