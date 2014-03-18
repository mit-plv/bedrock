Set Implicit Arguments.

Require Import StringSet.
Module String_as_OT := StringKey.

Require Import FMapAVL.
Module Import StringMap := Make String_as_OT.

Require Import OrdersAlt.
Module String_as_OT_new := Update_OT String_as_OT.
Require Import Equalities.
Module String_as_UDT := Make_UDT String_as_OT.
