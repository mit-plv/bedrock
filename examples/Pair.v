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

Definition hints_pair : hints.
  prepare pair_fwd pair_bwd.
Defined.

Theorem pairOk : moduleOk pair.
  vcgen.
  let v := eval simpl HintsOk in (fun ts (_ _ : Expr.tvar) fs ps => @HintsOk hints_pair ts fs ps) in
(*    match type of v with
      | forall ts (pc : Expr.tvar) (st : Expr.tvar) fs ps, SymIL.UnfolderLearnHook.UNF.hintsSoundness _ _ _ => idtac "SUCCESS" 
      | ?T => idtac T
    end.
*)  
  sep v.
  

  (* Stuck here: need to create a hint database in the fancy new form expected by [sep]. *)
  admit.
  admit.
Qed.
