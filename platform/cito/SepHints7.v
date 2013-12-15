Require Import AutoSep.

Set Implicit Arguments.

Definition locals_to_split vars1 vars2 vs p := locals (vars1 ++ vars2) vs 0 p.

Lemma fold_locals_to_split : forall vars1 vars2 vs p, locals (vars1 ++ vars2) vs 0 p = locals_to_split vars1 vars2 vs p.
  eauto.
Qed.

Lemma split_locals : forall vars1 vars2 vs p, locals_to_split vars1 vars2 vs p ===> locals vars1 vs 0 p * locals vars2 vs 0 p.
  admit.
Qed.

Definition hints_split_locals : TacPackage.
  prepare split_locals tt.
Defined.

