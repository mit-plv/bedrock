Set Implicit Arguments.

Require Import Notations.
Export Notations.

Infix "<-" := Syntax.Assign : stmt_scope.

Notation "x <- 'Label' lbl" := (Syntax.Label x lbl)
  (no associativity, at level 95, f at level 0) : stmt_scope.
