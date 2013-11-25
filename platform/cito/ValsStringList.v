Require Import Locals.

Definition agree_in a b := List.Forall (fun x => sel a x = sel b x).

