Require Import IL Memory String.
Require Import SyntaxExpr.

Inductive Statement : Set := 
  | Assignment : string -> Expr -> Statement
  | ReadAt : string -> Expr -> Expr -> Statement
  | WriteAt : Expr -> Expr -> Expr -> Statement
  | Seq : Statement -> Statement -> Statement
  | Skip : Statement
  | Conditional : Expr -> Statement -> Statement -> Statement
  | Loop : Expr -> Statement -> Statement
  | Malloc : string -> Expr -> Statement
  | Free : Expr -> Statement
  | Len : string -> Expr -> Statement
  | Call : Expr -> Expr -> Statement.

