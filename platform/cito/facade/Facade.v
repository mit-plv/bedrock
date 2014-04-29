Set Implicit Arguments.

Require Import String.

Require Import StringMap.
Import StringMap.

Section ADTSection.

  (* Syntax *)

  Require Import Memory IL.
  Require Import SyntaxExpr.

  Inductive Stmt :=
  | Skip
  | Seq : Stmt -> Stmt -> Stmt
  | If : Expr -> Stmt -> Stmt -> Stmt
  | While : Expr -> Stmt -> Stmt
  | Call : option string -> string -> list string -> Stmt
  | Assign : string -> Expr -> Stmt.

  (* Semantics *)

  Variable ADTValue : Type.

  Inductive Value :=
  | SCA : W -> Value
  | ADT : ADTValue -> Value.

  Definition State := t Value.

  Fixpoint eval_binop (op : binop + test) a b :=
    match op with
      | inl op' => evalBinop op' a b
      | inr op' => if evalTest op' a b then $1 else $0
    end.

  Fixpoint eval_binop_m (op : binop + test) oa ob :=
    match oa, ob with
      | Some (SCA a), Some (SCA b) => Some (SCA (eval_binop op a b))
      | _, _ => None
    end.

  Fixpoint eval (st : State) (e : Expr) : option Value :=
    match e with
      | Var x => find x st
      | Const w => Some (SCA w)
      | Binop op a b => eval_binop_m (inl op) (eval st a) (eval st b)
      | TestE op a b => eval_binop_m (inr op) (eval st a) (eval st b)
    end.

  Fixpoint eval_bool st e : option bool := 
    match eval st e with
      | Some (SCA w) => Some (wneb w $0)
      | _ => None
    end.

  Definition is_true st e := eval_bool st e = Some true.
  Definition is_false st e := eval_bool st e = Some false.

  Require Import StringMapFacts.
  Import FMapNotations.
  Open Scope fmap.
  
  Fixpoint add_remove elt k (v : option elt) st :=
    match v with
      | Some v' => add k v' st
      | None => remove k st
    end.

  Require Import List.

  Fixpoint add_remove_many elt keys (values : list (option elt)) st :=
    match keys, values with 
      | k :: keys', v :: values' => add_remove_many keys' values' (add_remove k v st)
      | _, _ => st
    end.

  Fixpoint addM elt k (v : elt) st :=
    match k with
      | Some k' => add k' v st
      | None => st
    end.

  Fixpoint mapM A B (f : A -> option B) ls :=
    match ls with
      | x :: xs => 
        match f x, mapM f xs with
          | Some y, Some ys => Some (y :: ys)
          | _, _ => None
        end
      | nil => Some nil
    end.
        
  Record AxiomaticSpec :=
    {
      PreCond : list Value -> Prop;
      PostCond : list (Value * option Value) -> Value -> Prop
    }.

  Record OperationalSpec := 
    {
      ArgVars : list string;
      RetVar : string;
      Body : Stmt;
      NoDupArgVars : NoDup ArgVars
    }.

  Inductive FuncSpec :=
    | Axiomatic : AxiomaticSpec -> FuncSpec
    | Operational : OperationalSpec -> FuncSpec.

  Definition sel st x := @StringMap.find Value x st.

  Fixpoint make_state keys values :=
    match keys, values with
      | k :: keys', v :: values' => add k v (make_state keys' values')
      | _, _ => @empty Value
    end.

  Section EnvSection.

    Variable env : string -> option FuncSpec.

    Inductive RunsTo : Stmt -> State -> State -> Prop :=
    | RunsToSkip : forall st, RunsTo Skip st st
    | RunsToSeq : 
        forall a b st st' st'',
          RunsTo a st st' -> 
          RunsTo b st' st'' -> 
          RunsTo (Seq a b) st st''
    | RunsToIfTrue : 
        forall cond t f st st', 
          is_true st cond ->
          RunsTo t st st' ->
          RunsTo (If cond t f) st st'
    | RunsToIfFalse : 
        forall cond t f st st', 
          is_false st cond ->
           RunsTo f st st' ->
          RunsTo (If cond t f) st st'
    | RunsToWhileTrue : 
        forall cond body st st' st'', 
          let loop := While cond body in
          is_true st cond ->
          RunsTo body st st' ->
          RunsTo loop st' st'' ->
          RunsTo loop st st''
    | RunsToWhileFalse : 
        forall cond body st, 
          let loop := While cond body in
          is_false st cond ->
          RunsTo loop st st
    | RunsToAssign :
        forall x e st st' w,
          eval st e = Some (SCA w) ->
          st' == add x (SCA w) st ->
          RunsTo (Assign x e) st st'
    | RunsToCallAx :
        forall x f args st st' spec input_output ret,
          env f = Some (Axiomatic spec) ->
          let input := map (@fst _ _) input_output in
          let output := map (@snd _ _) input_output in
          mapM (sel st) args = Some input ->
          PreCond spec input ->
          PostCond spec input_output ret ->
          let st := add_remove_many args output st in
          let st := addM x ret st in
          st' == st ->
          RunsTo (Call x f args) st st'
    | RunsToCallOp :
        forall x f args st st' spec input callee_st' ret,
          env f = Some (Operational spec) ->
          length args = length (ArgVars spec) ->
          mapM (sel st) args = Some input ->
          let callee_st := make_state (ArgVars spec) input in
          RunsTo (Body spec) callee_st callee_st' ->
          let output := map (sel callee_st') (ArgVars spec) in
          sel callee_st' (RetVar spec) = Some ret ->
          let st := add_remove_many args output st in
          let st := addM x ret st in
          st' == st ->
          RunsTo (Call x f args) st st'.

  End EnvSection.
          
End ADTSection.