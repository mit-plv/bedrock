Require Import ReservedNames.

Set Implicit Arguments.

Definition make_temp_vars_range_list start len := List.map temp_var (List.seq start len).

Definition make_temp_vars_list := make_temp_vars_range_list 0.