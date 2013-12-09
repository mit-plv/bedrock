Require Import AutoSep.
Require Import List.

Set Implicit Arguments.

Definition array_to_locals ls p (_ : list string) := array ls p.

Definition array_to_locals_ok (ls : list W) (vars : list string) := length vars = length ls /\ NoDup vars.

Lemma array_to_locals_fwd : forall ls p vars, array_to_locals_ok ls vars -> array_to_locals ls p vars ===> Ex vs, locals vars vs 0 p * [| toArray vars vs = ls |].
  admit.
Qed.

Definition hints_array_to_locals : TacPackage.
  prepare array_to_locals_fwd tt.
Defined.

Lemma replace_array_to_locals : forall ls p vars, array ls p = array_to_locals ls p vars.
  eauto.
Qed.

