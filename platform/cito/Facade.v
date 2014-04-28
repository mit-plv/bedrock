Set Implicit Arguments.

Require Import String.

Require Import StringMap.
Import StringMap.

Section ADTSection.

  (* Syntax *)

  Inductive Ty :=
  | TSCA
  | TADT.

  Record Var := 
    {
      VarType : Ty;
      VarName : string
    }.

  Require Import Memory IL.

  Definition BinOp := (binop + test)%type.

  Inductive Expr : Ty -> Type :=
  | ExprVar : forall var, Expr (VarType var)
  | ExprConst : W -> Expr TSCA
  | ExprBinOp : Expr TSCA -> BinOp -> Expr TSCA -> Expr TSCA.

  Record Arg :=
    {
      ArgType : Ty;
      ArgValue : Expr ArgType
    }.

  Inductive Stmt :=
  | Skip
  | Seq : Stmt -> Stmt -> Stmt
  | If : Expr TSCA -> Stmt -> Stmt -> Stmt
  | While : Expr TSCA -> Stmt -> Stmt
  | Call : option Var -> string -> list Arg -> Stmt
  | Assign : string -> Expr TSCA -> Stmt.

  (* Semantics *)

  Variable ADTValue : Type.

  Record State := 
    {
      SCAValues : string -> W;
      ADTValues : t ADTValue
    }.

  Fixpoint eval_binop op a b :=
    match op with
      | inl op' => evalBinop op' a b
      | inr op' => if evalTest op' a b then $1 else $0
    end.

  Fixpoint eval_sca (vs : string -> W) (e : Expr TSCA) : W :=
    match e with
      | ExprVar x => vs (VarName x)
      | ExprConst w => w
      | ExprBinOp a op b => eval_binop op (eval_sca vs a) (eval_sca vs b)
    end.

  Definition eval v := eval_sca (SCAValues v).

  Definition Equal_f A B (f g : A -> B) := forall x, f x = g x.

  Definition Equal_state a b :=
    Equal_f (SCAValues a) (SCAValues b) /\
    Equal (ADTValues a) (ADTValues b).

  Require Locals.

  Definition upd_sca v x w := {| SCAValues := Locals.upd (SCAValues v) x w; ADTValues := ADTValues v |}.

  Section EnvSection.

    Inductive RunsTo : Stmt -> State -> State -> Prop :=
    | RunsToSkip : forall v, RunsTo Skip v v
    | RunsToSeq : 
        forall a b v v' v'',
          RunsTo a v v' -> 
          RunsTo b v' v'' -> 
          RunsTo (Seq a b) v v''
    | RunsToIfTrue : 
        forall cond t f v v', 
          wneb (eval v cond) $0 = true ->
          RunsTo t v v' ->
          RunsTo (If cond t f) v v'
    | RunsToIfFalse : 
        forall cond t f v v', 
          wneb (eval v cond) $0 = false ->
          RunsTo f v v' ->
          RunsTo (If cond t f) v v'
    | RunsToWhileTrue : 
        forall cond body v v' v'', 
          let loop := While cond body in
          wneb (eval v cond) $0 = true ->
          RunsTo body v v' ->
          RunsTo loop v' v'' ->
          RunsTo loop v v''
    | RunsToWhileFalse : 
        forall cond body v, 
          let loop := While cond body in
          wneb (eval v cond) $0 = false ->
          RunsTo loop v v
    | RunsToAssign :
        forall x e v v',
          Equal_state (upd_sca v x (eval v e)) v' ->
          RunsTo (Assign x e) v v'
    | RunsToCallAx :
        forall x f args spec,
          env f = Some (Axiomatic spec) ->
          spec