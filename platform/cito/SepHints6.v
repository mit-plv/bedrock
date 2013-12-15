Require Import AutoSep.

Set Implicit Arguments.

Definition to_intro_array (_ : W) := True.

Lemma intro_array : forall len p, to_intro_array p -> p =?> len ===> Ex ls, [| length ls = len |] * array ls p.
  admit.
Qed.

Definition combined_locals vars1 vars2 vs1 vs2 p  := locals (vars1 ++ vars2) (merge vs1 vs2 vars1) 0 p.

Lemma fold_combined_locals : forall vars1 vars2 vs1 vs2 p, locals (vars1 ++ vars2) (merge vs1 vs2 vars1) 0 p = combined_locals vars1 vars2 vs1 vs2 p.
  eauto.
Qed.

Definition locals_combinable A (vars vars2 : list A) := NoDup (vars ++ vars2).

Lemma combine_locals : forall vars1 vars2 vs1 vs2 p, locals vars1 vs1 0 p * locals vars2 vs2 0 (p ^+ $(4 * length vars1)) ===> combined_locals vars1 vars2 vs1 vs2 p.
  admit.
Qed.

Definition hints_intro_array : TacPackage.
  prepare intro_array tt.
Defined.

Definition hints_combine_locals : TacPackage.
  prepare tt combine_locals.
Defined.

