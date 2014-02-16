Require Import StringSet.
Import StringSet.

Set Implicit Arguments.

Definition union_list ls := List.fold_left union ls empty.