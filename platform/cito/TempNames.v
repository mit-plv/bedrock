Require Import TempNamesList.
Require Import StringSet.
Require Import SetUtil.

Set Implicit Arguments.

Definition make_temp_names_range start len := to_set (make_temp_names_range_list start len).

Definition make_temp_names := make_temp_names_range 0.