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

Definition to_elim (_ : list W) := True.

Lemma array_elim : forall ls p, to_elim ls -> array ls p ===> p =?> length ls.
  admit.
Qed.

Definition hints_array_split : TacPackage.
  prepare array_split tt.
Defined.

Definition hints_array_elim : TacPackage.
  prepare array_elim tt.
Defined.

