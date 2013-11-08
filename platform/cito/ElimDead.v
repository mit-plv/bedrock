Require Import Syntax.

Set Implicit Arguments.

Variable set : Type.

Fixpoint elim_dead s used : Statement * set :=
  match s with
    | skip => skip
    | a ;; b => 
      let result := elim_dead b in
      let b' := fst result in
      let used := snd result in
      elim_dead a used
    | x <- e =>
      if mem_dec x used then
        let used' := used %- x in
        let used'' := used' + free_vars e in
        (x <- e, used'')
      else
        (skip, used)