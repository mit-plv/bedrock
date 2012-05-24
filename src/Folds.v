Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

Section fold_left2_opt.
  Variable T U V : Type.
  Variable F : T -> V -> U -> option U.

  Fixpoint fold_left_2_opt (ls : list T) (ls' : list V) (acc : U) : option U :=
    match ls, ls' with 
      | nil , nil => Some acc
      | x :: xs , y :: ys => 
        match F x y acc with
          | None => None
          | Some acc => fold_left_2_opt xs ys acc
        end
      | _ , _ => None
    end.
End fold_left2_opt.

Section fold_left3_opt.
  Variable T U V A : Type.
  Variable F : T -> U -> V -> A -> option A.

  Fixpoint fold_left_3_opt (ls : list T) (ls' : list U) (ls'' : list V) 
    (acc : A) : option A :=
    match ls, ls', ls'' with 
      | nil , nil , nil => Some acc
      | x :: xs , y :: ys , z :: zs => 
        match F x y z acc with
          | None => None
          | Some acc => fold_left_3_opt xs ys zs acc
        end
      | _ , _ , _ => None
    end.
End fold_left3_opt.