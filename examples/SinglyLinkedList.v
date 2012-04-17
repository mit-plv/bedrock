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
    destruct ls; sepLemma.
  Qed.

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
    If (Rv = 0) {
      Return 1
    } else {
      Return 0
    }
  }
}}.

Definition hints_sll' : TacPackage.
  let env := eval simpl SymIL.EnvOf in (SymIL.EnvOf auto_ext) in
  prepare env nil_fwd nil_bwd ltac:(fun x => 
    SymIL.Package.build_hints_pack x ltac:(fun x =>
      SymIL.Package.refine_glue_pack x auto_ext)).
Defined.

Definition hints_sll : TacPackage.
  let v := eval cbv beta iota zeta delta [ 
    auto_ext hints_sll'
    SymIL.AllAlgos_composite SymIL.oplus
    SymIL.Types SymIL.Funcs SymIL.Preds SymIL.Hints SymIL.Prover SymIL.MemEval
    SymIL.Algos 
    
    Env.repr_combine 
    Env.listToRepr
    app map 
  ] in hints_sll' in
  exact v.
Defined.

Lemma null_nil : forall T (x1 : list T) (v : W),
  x1 = nil ->
  v = 1 ->
  v = null x1.
Proof.
  intros; subst; simpl; reflexivity.
Qed.
Lemma null_not_nil : forall T (x1 : list T) (v : W),
  x1 <> nil ->
  v = 0 ->
  v = null x1.
Proof.
  destruct x1; simpl; try congruence.
Qed.
Local Hint Resolve null_nil null_not_nil : sll.


Theorem sllMOk : moduleOk sllM.
  vcgen; (sep hints_sll; eauto with sll).
  admit. (** We can't solve this until we get the prover reasoning about inequality facts **)
Qed.
