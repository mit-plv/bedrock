Set Implicit Arguments.

Definition default A def (x : option A) :=
  match x with
    | Some v => v
    | None => def
  end.