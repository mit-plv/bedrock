Set Implicit Arguments.

Require Import FModule.

Section ADTValue.

  Variable ADTValue : Type.

  Notation FModule := (@FModule ADTValue).

  Definition compile (m : FModule)