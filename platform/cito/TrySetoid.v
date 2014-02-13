Require Export Setoid.

Require Export Relation_Definitions.

Set Implicit Arguments.

Parameter set: Type -> Type.

Parameter empty: forall A, set A.

Parameter eq_set: forall A, set A -> set A -> Prop.

Parameter union: forall A, set A -> set A -> set A.

Axiom eq_set_refl: forall A, reflexive _ (eq_set (A:=A)).

Axiom eq_set_sym: forall A, symmetric _ (eq_set (A:=A)).

Axiom eq_set_trans: forall A, transitive _ (eq_set (A:=A)).

Axiom empty_neutral: forall A (S: set A), eq_set (union S (empty A)) S.

Axiom union_compat:
 forall (A : Type),
  forall x x' : set A, eq_set x x' ->
  forall y y' : set A, eq_set y y' ->
   eq_set (union x y) (union x' y').

Add Parametric Relation A : (set A) (@eq_set A)
 reflexivity proved by (eq_set_refl (A:=A))
 symmetry proved by (eq_set_sym (A:=A))
 transitivity proved by (eq_set_trans (A:=A))
 as eq_set_rel.

Add Parametric Morphism A : (@union A) with 
signature (@eq_set A) ==> (@eq_set A) ==> (@eq_set A) as union_mor.

Proof. exact (@union_compat A). Qed.

Goal forall (S: set nat),
 eq_set (union (union S (empty _)) S) (union S S).

Proof. intros. rewrite empty_neutral. reflexivity. Qed.