Require Import AutoSep.
Require Import List.

Set Implicit Arguments.

Variable splittable : forall A, list A -> nat -> Prop.

Definition array_to_split ls p (_ : nat) := array ls p.

Lemma replace_array_to_split : forall ls p pos, array ls p = array_to_split ls p pos.
  eauto.
Qed.

Lemma array_split : forall ls p pos, splittable ls pos -> array_to_split ls p pos ===> array (firstn pos ls) p * array (skipn pos ls) (p ^+ $4 ^* $(pos)).
  admit.
Qed.

Definition hints_array_split : TacPackage.
  prepare array_split tt.
Defined.
