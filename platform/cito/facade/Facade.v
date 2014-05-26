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
  | Call : option string -> Expr -> list string -> Stmt
  | Label : string -> glabel -> Stmt
  | Assign : string -> Expr -> Stmt.

  (* Semantics *)

  Variable ADTValue : Type.

  Inductive Value :=
  | SCA : W -> Value
  | ADT : ADTValue -> Value.

  Definition State := StringMap.t Value.

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

  Fixpoint add_remove_many keys (input : list Value) (ouput : list (option Value)) st :=
    match keys, inputs, outputs with 
      | k :: keys', i :: inputs', o :: outputs' => 
        let st' :=
            match i with
              | ADT _ => add_remove k v st
              | _ => st
            end in
        add_remove_many keys' inputs' outputs' st'
      | _, _, _ => st
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
        forall x f args st st' spec input output ret f_w,
          NoDup args ->
          eval st f = Some (SCA f_w) ->
          Word2Spec env f_w = Some (Axiomatic spec) ->
          mapM (sel st) args = Some input ->
          PreCond spec input ->
          length input = length output ->
          PostCond spec (combine input output) ret ->
          let st := add_remove_many args input output st in
          let st := addM x ret st in
          st' == st ->
          RunsTo (Call x f args) st st'
    | RunsToCallOp :
        forall x f args st st' spec input callee_st' ret f_w,
          NoDup args ->
          eval st f = Some (SCA f_w) ->
          Word2Spec env f_w = Some (Operational spec) ->
          length args = length (ArgVars spec) ->
          mapM (sel st) args = Some input ->
          let callee_st := make_state (ArgVars spec) input in
          RunsTo (Body spec) callee_st callee_st' ->
          let output := map (sel callee_st') (ArgVars spec) in
          sel callee_st' (RetVar spec) = Some ret ->
          let st := add_remove_many args input output st in
          let st := addM x ret st in
          st' == st ->
          RunsTo (Call x f args) st st'.

  End EnvSection.
          
End ADTSection.

Require Syntax.

Require Import String.
Open Scope string.

Coercion Var : string >-> Expr.

Fixpoint compile (s : Stmt) : Syntax.Stmt :=
  match s with
    | Skip => Syntax.Skip
    | Seq a b => Syntax.Seq (compile a) (compile b)
    | If e t f => Syntax.If e (compile t) (compile f)
    | While e c => Syntax.While e (compile c)
    | Assign x e => Syntax.Assign x e
    | Label x lbl => Syntax.Label x lbl
    | Call x f args => Syntax.Call x f (List.map Var args)
  end.

Require Import ADT.

Module Make (Import A : ADT).

  Require Semantics.
  Module Cito := Semantics.Make A.

  Definition RunsTo := @RunsTo ADTValue.
  Definition State := @State ADTValue.
  Definition Env := @Env ADTValue.
  Definition AxiomaticSpec := @AxiomaticSpec ADTValue.
  Definition Value := @Value ADTValue.

  Import StringMap.

  Definition related_state (s_st : State) (t_st : Cito.State) := 
    (forall x v, 
       find x s_st = Some v ->
       match v with
         | SCA w => Locals.sel (fst t_st) x = w
         | ADT a => exists p, Locals.sel (fst t_st) x = p /\ Cito.heap_sel (snd t_st) p = Some a
       end) /\
    (forall p a,
       Cito.heap_sel (snd t_st) p = Some a ->
       exists x,
         Locals.sel (fst t_st)  x = p /\
         find x s_st = Some (ADT a)).
                
  Definition CitoEnv := ((glabel -> option W) * (W -> option Cito.Callee))%type.

  Coercion Semantics.Fun : Semantics.InternalFuncSpec >-> FuncCore.FuncCore.

  Definition CitoIn_FacadeIn (argin : Cito.ArgIn) : Value :=
    match argin with
      | inl w => SCA _ w
      | inr a => ADT a
    end.

  Definition compile_ax (spec : AxiomaticFuncSpec) : Cito.Callee :=
    Semantics.Foreign 
      {|
        Semantics.PreCond := fun args => PreCond (List.map CitoIn_FacadeIn args) ;
        Semantics.PostCond := fun pairs ret => PostCond (

  Definition compile_spec (spec : FuncSpec) : Cito.Callee :
    match spec with
      | Axiomatic s => compile_ax s
      | Operational s => compile_op s
    end.

  Definition compile_env (env : Env) : CitoEnv :=
    (Label2Word env, 
     fun w => option_map compile_spec (Word2Spec env w)).

    
  Definition related_op_spec s_env (s_spec : OperationalSpec) : Cito.ForeignFuncSpec :=
    {|
      PreCond := 
        fun args =>
          length args = length (ArgVars s_spec) /\
          let st := zip (ArgVars s_spec) args in
          Safe s_env (Body s_spec) st ;
      PostCond :=
        fun pairs ret =>
          length pairs = length (AgrVars specs) /\
          let st := zip (ArgVars s_spec) (List.map fst args) in
          let st' := zip (ArgVars s_spec) (List.map snd args) in
          RunsTo s_env (Body s_spec) st st' /\
          find (RetVar s_spec) st'


    ArgVars s_spec = FuncCore.ArgVars t_spec /\
    RetVar s_spec = FuncCore.RetVar t_spec /\
    compile (Body s_spec) = FuncCore.Body t_spec.

  Definition related_op_spec (s_spec : OperationalSpec) (t_spec : Semantics.InternalFuncSpec) := 
    ArgVars s_spec = FuncCore.ArgVars t_spec /\
    RetVar s_spec = FuncCore.RetVar t_spec /\
    compile (Body s_spec) = FuncCore.Body t_spec.

  Definition FacadeIn_CitoIn (v : Value) : Cito.ArgIn :=
    match v with
      | SCA w => inl w
      | ADT a => inr a
    end.
  
  Definition CitoInOut_FacadeInOut (in_out : Cito.ArgIn * Cito.ArgOut) : Value * option Value :=
    match fst in_out, snd in_out with
      | inl w, _ => (SCA _ w, Some (SCA _ w))
      | inr a, Some a' => (ADT a, Some (ADT a'))
      | inr a, None => (ADT a, None)
    end.

  Definition related_ax_spec (s_spec : AxiomaticSpec) (t_spec : Cito.ForeignFuncSpec) := 
    (forall t_ins,
       Semantics.PreCond t_spec t_ins -> PreCond s_spec (List.map CitoIn_FacadeIn t_ins)) /\
    (forall t_inouts t_ret,
       Semantics.PostCond t_spec t_inouts t_ret -> PostCond s_spec (List.map CitoInOut_FacadeInOut t_inouts) (CitoIn_FacadeIn t_ret)) /\
    (forall s_ins,
       PreCond s_spec s_ins -> Semantics.PreCond t_spec (List.map FacadeIn_CitoIn s_ins)) /\
    (forall s_inouts s_ret,
       PostCond s_spec s_inouts s_ret -> exists t_inouts, List.map CitoInOut_FacadeInOut t_inouts = s_inouts /\ Semantics.PostCond t_spec t_inouts (FacadeIn_CitoIn s_ret)).

  Definition related_spec s_spec t_spec :=
    match s_spec, t_spec with 
      | Operational s, Semantics.Internal t => related_op_spec s t
      | Axiomatic s, Semantics.Foreign t => related_ax_spec s t
      | _, _ => False
    end.

  Definition related_env (s_env : Env) (t_env : CitoEnv) :=
    forall lbl,
      match s_env lbl with
        | Some s_spec => 
          exists w t_spec,
            fst t_env lbl = Some w /\
            snd t_env w = Some t_spec /\
            related_spec s_spec t_spec
        | _ => True
      end.

  Theorem compile_runsto : forall t t_env t_st t_st', Cito.RunsTo t_env t t_st t_st' -> forall s, t = compile s -> forall s_env s_st, related_env s_env t_env -> related_state s_st t_st -> exists s_st', RunsTo s_env s s_st s_st' /\ related_state s_st' t_st'.
  Proof.
    induction 1; simpl; intros; destruct s; simpl in *; intros; try discriminate.
    admit.
    admit.


  Qed.

End Make.

