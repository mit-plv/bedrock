Set Implicit Arguments.

Require Import String.

Require Import StringMap.
Import StringMap.

Section ADTSection.

  (* Syntax *)

  Require Import Memory IL.
  Require Import SyntaxExpr.
  Require Import GLabel.

  Inductive Stmt :=
  | Skip
  | Seq : Stmt -> Stmt -> Stmt
  | If : Expr -> Stmt -> Stmt -> Stmt
  | While : Expr -> Stmt -> Stmt
  | Call : string -> Expr -> list string -> Stmt
  | Label : string -> glabel -> Stmt
  | Assign : string -> Expr -> Stmt.

  (* Semantics *)

  Variable ADTValue : Type.

  Inductive Value :=
  | SCA : W -> Value
  | ADT : ADTValue -> Value.

  Definition State := StringMap.t Value.

  Definition eval_binop (op : binop + test) a b :=
    match op with
      | inl op' => evalBinop op' a b
      | inr op' => if evalTest op' a b then $1 else $0
    end.

  Definition eval_binop_m (op : binop + test) oa ob :=
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

  Definition eval_bool st e : option bool := 
    match eval st e with
      | Some (SCA w) => Some (wneb w $0)
      | _ => None
    end.

  Definition is_true st e := eval_bool st e = Some true.
  Definition is_false st e := eval_bool st e = Some false.

  Require Import StringMapFacts.
  Import FMapNotations.
  Open Scope fmap.
  
  Definition add_remove elt k (v : option elt) st :=
    match v with
      | Some v' => add k v' st
      | None => remove k st
    end.

  Require Import List.

  Fixpoint add_remove_many keys (input : list Value) (output : list (option Value)) st :=
    match keys, input, output with 
      | k :: keys', i :: input', o :: output' => 
        let st' :=
            match i with
              | ADT _ => add_remove k o st
              | _ => st
            end in
        add_remove_many keys' input' output' st'
      | _, _, _ => st
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
      NoDupArgVars : NoDup (RetVar :: ArgVars)
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

  Record Env := 
    {
      Label2Word : glabel -> option W ;
      Word2Spec : W ->option FuncSpec
    }.

  Definition no_adt_leak input argvars retvar st :=
    forall var a, 
      sel st var = Some (ADT a) -> 
      var = retvar \/ 
      exists i ai, nth_error argvars i = Some var /\ 
                   nth_error input i = Some (ADT ai).

  Section EnvSection.

    Variable env : Env.

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
    | RunsToLabel :
        forall x lbl st st' w,
          Label2Word env lbl = Some w ->
          st' == add x (SCA w) st ->
          RunsTo (Label x lbl) st st'
    | RunsToCallAx :
        forall x f args st spec input output ret f_w,
          NoDup args ->
          eval st f = Some (SCA f_w) ->
          Word2Spec env f_w = Some (Axiomatic spec) ->
          mapM (sel st) args = Some input ->
          PreCond spec input ->
          length input = length output ->
          PostCond spec (combine input output) ret ->
          let st' := add_remove_many args input output st in
          let st' := add x ret st' in
          forall st'',
            st'' == st' ->
            RunsTo (Call x f args) st st''
    | RunsToCallOp :
        forall x f args st spec input callee_st' ret f_w,
          NoDup args ->
          eval st f = Some (SCA f_w) ->
          Word2Spec env f_w = Some (Operational spec) ->
          length args = length (ArgVars spec) ->
          mapM (sel st) args = Some input ->
          let callee_st := make_state (ArgVars spec) input in
          RunsTo (Body spec) callee_st callee_st' ->
          sel callee_st' (RetVar spec) = Some ret ->
          no_adt_leak input (ArgVars spec) (RetVar spec) callee_st' ->
          let output := map (sel callee_st') (ArgVars spec) in
          let st' := add_remove_many args input output st in
          let st' := add x ret st' in
          forall st'',
            st'' == st' ->
            RunsTo (Call x f args) st st''.

    CoInductive Safe : Stmt -> State -> Prop :=
    | SafeSkip : forall st, Safe Skip st
    | SafeSeq : 
        forall a b st,
          Safe a st /\
          (forall st',
             RunsTo a st st' -> Safe b st') ->
          Safe (Seq a b) st
    | SafeIfTrue : 
        forall cond t f st, 
          is_true st cond ->
          Safe t st ->
          Safe (If cond t f) st
    | SafeIfFalse : 
        forall cond t f st, 
          is_false st cond ->
          Safe f st ->
          Safe (If cond t f) st
    | SafeWhileTrue : 
        forall cond body st, 
          let loop := While cond body in
          is_true st cond ->
          Safe body st ->
          (forall st',
             RunsTo body st st' -> Safe loop st') ->
          Safe loop st
    | SafeWhileFalse : 
        forall cond body st, 
          let loop := While cond body in
          is_false st cond ->
          Safe loop st
    | SafeAssign :
        forall x e st w,
          eval st e = Some (SCA w) ->
          Safe (Assign x e) st
    | SafeLabel :
        forall x lbl st w,
          Label2Word env lbl = Some w ->
          Safe (Label x lbl) st
    | SafeCallAx :
        forall x f args st spec input f_w,
          NoDup args ->
          eval st f = Some (SCA f_w) ->
          Word2Spec env f_w = Some (Axiomatic spec) ->
          mapM (sel st) args = Some input ->
          PreCond spec input ->
          Safe (Call x f args) st
    | SafeCallOp :
        forall x f args st spec input f_w,
          NoDup args ->
          eval st f = Some (SCA f_w) ->
          Word2Spec env f_w = Some (Operational spec) ->
          length args = length (ArgVars spec) ->
          mapM (sel st) args = Some input ->
          let callee_st := make_state (ArgVars spec) input in
          Safe (Body spec) callee_st ->
          (forall callee_st', 
             RunsTo (Body spec) callee_st callee_st' -> 
             sel callee_st' (RetVar spec) <> None /\ 
             no_adt_leak input (ArgVars spec) (RetVar spec) callee_st') ->
          Safe (Call x f args) st.

  End EnvSection.
          
End ADTSection.

