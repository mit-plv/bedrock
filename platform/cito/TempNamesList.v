Require Import ReservedNames.

Set Implicit Arguments.

Definition make_temp_names_range_list start len := List.map temp_name (List.seq start len).

Definition make_temp_names_list := make_temp_names_range_list 0.