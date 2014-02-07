Require Import AutoSep.
Require Import List.

Set Implicit Arguments.

Section TopSection.

  Definition locals_to_elim (_ : list string) := True.

  Lemma elim_locals : forall vars vs p, locals_to_elim vars -> locals vars vs 0 p ===> p =?> length vars.
    admit.
  Qed.

  Definition hints_elim_locals : TacPackage.
    prepare elim_locals tt.
  Defined.

End TopSection.