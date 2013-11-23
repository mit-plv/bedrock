Require Import List.

Set Implicit Arguments.

Fixpoint range start length:=
  match length with
    | O => nil
    | S n' => range start n' ++ (start + n' :: nil)
  end.

Definition range0 := range 0.