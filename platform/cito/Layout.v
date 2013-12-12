Require Import AutoSep.
Require Import Semantics.

Set Implicit Arguments.

Definition Layout := W -> ADTValue -> HProp.

Variable layout : Layout.
