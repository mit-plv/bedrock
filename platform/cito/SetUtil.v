Require Import StringSet.

Set Implicit Arguments.

Definition to_set ls := List.fold_left (fun s e => add e s) ls empty.

Definition disjoint a b := forall x, In x a -> In x b -> False.
