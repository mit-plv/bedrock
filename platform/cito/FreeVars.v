Require Import FreeVarsExpr.
Require Import Syntax.
Require Import Option.
Import MSet.

Set Implicit Arguments.

Fixpoint free_vars (s : Syntax.Stmt) :=
  match s with
    | Syntax.Skip => empty
    | Syntax.Seq a b => union (free_vars a) (free_vars b)
    | Syntax.If cond t f => union (union (FreeVarsExpr.free_vars cond) (free_vars t)) (free_vars f)
    | Syntax.While cond body => union (FreeVarsExpr.free_vars cond) (free_vars body)
    | Syntax.Call var f args => 
      union 
        (union 
           (default empty (option_map singleton var)) 
           (FreeVarsExpr.free_vars f)) 
        (List.fold_left (fun acc arg => union acc (FreeVarsExpr.free_vars arg)) args empty)
  end.

