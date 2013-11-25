Require Import TempVarsList.
Require Import StringSet.
Require Import SetUtil.

Set Implicit Arguments.

Definition make_temp_vars_range start len := to_set (make_temp_vars_range_list start len).

Definition make_temp_vars := make_temp_vars_range 0.