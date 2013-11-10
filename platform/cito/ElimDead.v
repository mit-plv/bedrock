Require Import Syntax.
Import String Memory IL SyntaxExpr.
Require Import Notations.

Set Implicit Arguments.

Variable set : Type.
Variable mem_dec : string -> set -> bool.
Variable remove : set -> string -> set.
Infix "%-" := remove (at level 20).
Variable free_vars : Expr -> set.
Variable free_vars_stmt : Statement -> set.
Notation skip := Syntax.Skip.
Variable union : set -> set -> set.
Infix "+" := union.

Open Scope stmnt.

Fixpoint elim_dead s used : Statement * set :=
  match s with
    | skip => (s, used)
    | a ;: b => 
      let result := elim_dead b used in
      let b := fst result in
      let used := snd result in
      let result := elim_dead a used in
      let a := fst result in
      let used := snd result in
      (a ;: b, used)
    | Conditional e t f => 
      let result := elim_dead t used in
      let t := fst result in
      let used_t := snd result in
      let result := elim_dead f used in
      let f := fst result in
      let used_f := snd result in
      (Conditional e t f, free_vars e + used_t + used_f)
    | Loop e body => 
      let result := elim_dead body (used + free_vars e + free_vars_stmt body) in
      let body := fst result in
      let used' := snd result in
      (Loop e body, used + used' + free_vars e)
    | x <- e =>
      if mem_dec x used then
        (s, used %- x + free_vars e)
      else
        (skip, used)
    | x <== arr[idx] =>
      if mem_dec x used then
        (s, used %- x + free_vars arr + free_vars idx)
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
    | Call f[x] =>
      (s, used + free_vars f + free_vars x)
  end.

Require Import Semantics.

Variable agree_in : vals -> vals -> set -> Prop.

Lemma elim_dead_is_bp : 
  forall fs s used vs vt heap vt' heap', 
    let result := elim_dead s used in
    let t := fst result in
    let used' := snd result in
    RunsTo fs t (vt, heap) (vt', heap') ->
    agree_in vs vt used' ->
    exists vs',
      RunsTo fs s (vs, heap) (vs', heap') /\
      agree_in vs' vt' used.
    