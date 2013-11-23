Require Import String.

Set Implicit Arguments.

Fixpoint show_nat_unary s n := 
  match n with
    | O => s
    | S n' => (s ++ show_nat_unary s n')%string
  end.

