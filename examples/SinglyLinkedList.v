Require Import AutoSep.

Set Implicit Arguments.


(** The king of the abstract predicates *)

Module Type SINGLY_LINKED_LIST.
  Parameter sll : list W -> W -> HProp.

  Axiom sll_extensional : forall ls p, HProp_extensional (sll ls p).

  Axiom nil_fwd : forall ls (p : W), p = 0
    -> sll ls p ===> [| ls = nil |].

  Axiom nil_bwd : forall ls (p : W), p = 0
    -> [| ls = nil |] ===> sll ls p.
End SINGLY_LINKED_LIST.

Module SinglyLinkedList : SINGLY_LINKED_LIST.
  Open Scope Sep_scope.

  Fixpoint sll (ls : list W) (p : W) : HProp :=
    match ls with
      | nil => [| p = 0 |]
      | x :: ls' => [| p <> 0 |] * Ex p', (p ==*> x, p') * sll ls' p'
    end.

  Theorem sll_extensional : forall ls (p : W), HProp_extensional (sll ls p).
    destruct ls; reflexivity.
  Qed.

  Theorem nil_fwd : forall ls (p : W), p = 0
    -> sll ls p ===> [| ls = nil |].
    destruct ls; sepLemma.
  Qed.

  Theorem nil_bwd : forall ls (p : W), p = 0
    -> [| ls = nil |] ===> sll ls p.
(*
    destruct ls; sepLemma.
*)
  Admitted.

End SinglyLinkedList.

Import SinglyLinkedList.
Hint Immediate sll_extensional.

Definition null A (ls : list A) : bool :=
  match ls with
    | nil => true
    | _ => false
  end.

Definition B2N (b : bool) : nat :=
  if b then 1 else 0.

Coercion B2N : bool >-> nat.

Definition nullS : assert := st ~> ExX, Ex ls, ![ ^[sll ls st#Rv] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = null ls |] /\ ![ ^[sll ls st#Rv] * #1 ] st').

Definition sllM := bmodule "sll" {{
  bfunction "null" [nullS] {
    If ($[Rv] = 0) {
      Return 0
    } else {
      Return 1
    }
  }
}}.

Definition hints_sll' : TacPackage.
  let env := eval simpl SymIL.EnvOf in (SymIL.EnvOf auto_ext) in
  prepare env nil_fwd nil_bwd ltac:(fun x =>
    SymIL.Package.build_hints_pack x ltac:(fun x => 
      SymIL.Package.glue_pack x auto_ext ltac:(fun x => exact x))).
Defined.

Definition hints_sll : TacPackage.
  let v := eval cbv beta iota zeta delta [
    hints_sll' auto_ext
    SymIL.Types SymIL.Funcs SymIL.Preds
    SymIL.Algos SymIL.Hints SymIL.MemEval SymIL.Prover
    SymIL.AllAlgos_composite 
    Env.repr_combine 
    in_dec equiv_dec EquivDec_nat Env.repr_optimize Env.footprint Env.default
    Peano_dec.eq_nat_dec nat_rec nat_rect
    list_rec list_rect app  
    SymIL.oplus Forward Backward
    sumbool_rec sumbool_rect
  ] in hints_sll'
  in
  exact v.
Defined.



Theorem sllMOk : moduleOk sllM.
  vcgen.

  (* This fails with: couldn't apply sym_eval_any! (SF case)
  sep hints_sll. *)

  admit.
  admit.
  admit.
  admit.
  admit.
Qed.
