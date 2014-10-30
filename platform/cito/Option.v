Set Implicit Arguments.

Definition default A def (x : option A) :=
  match x with
    | Some v => v
    | None => def
  end.

Definition option_dec A (x : option A) : {a | x = Some a} + {x = None}.
  destruct x.
  left.
  exists a.
  eauto.
  right.
  eauto.
Qed.

