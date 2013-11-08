Set Implicit Arguments.

Fixpoint elim_dead s :=
  match s with
    | Skip => Skip
    | a ;; b => 
      let result := elim_dead b in
      