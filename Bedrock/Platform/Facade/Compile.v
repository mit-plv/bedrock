Set Implicit Arguments.

Require Import Facade.
Require Semantics.

Require Import String.
Require Import SyntaxExpr.

Fixpoint compile (s : Stmt) : Syntax.Stmt :=
  match s with
    | Skip => Syntax.Skip
    | Seq a b => Syntax.Seq (compile a) (compile b)
    | If e t f => Syntax.If e (compile t) (compile f)
    | While e c => Syntax.While e (compile c)
    | Facade.Assign x e => Syntax.Assign x e
    | Label x lbl => Syntax.Label x lbl
    | Call x f args => Syntax.Call (Some x) f (List.map Var args)
  end.

Require Import ListFacts3.

Definition compile_op (spec : OperationalSpec) :=
  {|
    Semantics.Fun :=
      {|
        FuncCore.ArgVars := ArgVars spec;
        FuncCore.RetVar := RetVar spec;
        FuncCore.Body := compile (Body spec)
      |};
    Semantics.NoDupArgVars := is_no_dup_sound _ (args_no_dup spec)
  |}.