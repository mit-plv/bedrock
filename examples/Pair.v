Require Import AutoSep.

(** A very basic abstract predicate: pairs of words *)

Module Type PAIR.
  Parameter pair : W -> W -> W -> HProp.

  Axiom pair_extensional : forall a b p, HProp_extensional (pair a b p).

  Axiom pair_fwd : forall a b p,
    pair a b p ===> p =*> a * (p ^+ $4) =*> b.

  Axiom pair_bwd : forall a b p,
    p =*> a * (p ^+ $4) =*> b ===> pair a b p.
End PAIR.

Module Pair : PAIR.
  Open Scope Sep_scope.

  Definition pair (a b p : W) : HProp :=
    p =*> a * (p ^+ $4) =*> b.

  Theorem pair_extensional : forall a b p, HProp_extensional (pair a b p).
    reflexivity.
  Qed.

  Theorem pair_fwd : forall a b p,
    pair a b p ===> p =*> a * (p ^+ $4) =*> b.
    sepLemma. 
  Qed.

  Theorem pair_bwd : forall a b p,
    p =*> a * (p ^+ $4) =*> b ===> pair a b p.
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
      SymIL.Package.refine_glue_pack x auto_ext)).
Defined.

Definition hints_pair : TacPackage.
  let v := eval cbv beta iota zeta delta [ 
    auto_ext hints_pair'
    SymIL.AllAlgos_composite SymIL.oplus
    SymIL.Types SymIL.Funcs SymIL.Preds SymIL.Hints SymIL.Prover SymIL.MemEval
    SymIL.Algos 
    
    Env.repr_combine 
    Env.listToRepr
    app map 
  ] in hints_pair' in
  exact v.
Defined.

Theorem pairOk : moduleOk pair.
  vcgen; abstract (sep hints_pair).
Qed.
