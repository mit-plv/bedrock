Set Implicit Arguments.

Require Import String.
Local Open Scope string_scope.

Definition tmp_prefix := "!".
Local Notation PRE := tmp_prefix.

Definition is_good_varname s := negb (prefix PRE s).
