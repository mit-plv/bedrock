Require Import Syntax.

Local Notation skip := Syntax.Skip.

Infix ";:" := Syntax.Seq (left associativity, at level 110).

Infix "<-" := Syntax.Assign (at level 90, no associativity).

