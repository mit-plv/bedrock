Require Import Syntax.
Require Import WritingPrograms.

Set Implicit Arguments.

Variable set : Type.

Fixpoint elim_dead s used : Statement * set :=
  match s with
    | skip => (s, used)
    | a ;; b => 
      let result := elim_dead b in
      let b' := fst result in
      let used := snd result in
      elim_dead a used
    | Conditional e t f => 
      let result := elim_dead t in
      let t' := fst result in
      let used_t := snd result in
      let result := elim_dead f in
      let f' := fst result in
      let used_f := snd result in
      (Conditional e t' f', free_vars e + used_t + used_f)
    | Loop e body => 
      let result := elim_dead body (used + free_vars c + free_vars_stmt body) in
      let body' := fst result in
      let used' := snd result in
      (Loop e body', used' + free_vars c)
    | x <- e =>
      if mem_dec x used then
        (s, used %- x + free_vars e)
      else
        (skip, used)
    | x <== arr[idx] =>
      if mem_dec x used then
        (s, used %- x + free_vars arr + free_var idx)
      else
        (skip, used)
    | arr[idx] <== e =>
      (s, used + free_vars arr + free_vars idx + free_vars e)
    | x <- new e =>
      (s, used %- x + free_vars e)
    | Free e =>
      (s, used + free_vars e)
    | Len x e =>
      if mem_dec x used then
        (s, used %- x + free_vars e)
      else
        (skip, used)
    | Call f x =>
      (s, used + free_vars f + free_vars x)
      