Set Implicit Arguments.

Require Import String.

Require Import StringMap.
Import StringMap.

Section ADTSection.

  (* Syntax *)

  Require Import Memory IL.

  Inductive Ty := 
  | TSCA
  | TADT.

  Inductive Binop :=
  | Plus
  | Minus
  | Times
  | Eq
  | Ne
  | Lt
  | Le.

  Record Var :=
    {
      vartype : Ty;
      varname : string
    }.

  Inductive Expr : Ty -> Type :=
  | ExprVarSCA : string -> Expr TSCA
  | ExprVarADT : string -> Expr TADT
  | ExprConst : W -> Expr TSCA
  | ExprBinop : Binop -> Expr TSCA -> Expr TSCA -> Expr TSCA.

  Require Import GLabel.

  Inductive Stmt :=
  | Skip
  | Seq : Stmt -> Stmt -> Stmt
  | If : Expr TSCA-> Stmt -> Stmt -> Stmt
  | While : Expr TSCA -> Stmt -> Stmt
  | Call : Var -> Expr TSCA -> list Var -> Stmt
  | Label : string -> glabel -> Stmt
  | Assign : string -> Expr TSCA -> Stmt.

  (* Semantics *)

  Variable ADTValue : Type.

  Record State := 
    {
      sca_map : string -> W;
      adt_map : StringMap.t ADTValue
    }.

  Require Import Word.

  Definition eval_binop op a b :=
    match op with
      | Plus => wplus a b
      | Minus => wminus a b
      | Times => wmult a b
      | Eq => if weqb a b then $1 else $0
      | Ne => if wneb a b then $1 else $0
      | Lt => if wltb a b then $1 else $0
      | Le => if wleb a b then $1 else $0
    end.

  Fixpoint eval (st : string -> W) (e : Expr TSCA) : W :=
    match e with
      | ExprVarSCA x => st x
      | ExprConst w => w
      | ExprBinop op a b => eval_binop op (eval st a) (eval st b)
    end.

  Definition eval_st st e := eval (sca_map st) e.
  Definition eval_bool st e : bool := wneb (eval st e) $0.
  Definition is_true st e := eval_bool (sca_map st) e = true.
  Definition is_false st e := eval_bool (sca_map st) e = false.

  Require Import StringMapFacts.
  Import FMapNotations.
  Open Scope fmap.
  
  Definition add_remove elt k (v : option elt) st :=
    match v with
      | Some v' => add k v' st
      | None => remove k st
    end.

  Require Import List.

  Definition addM elt k (v : elt) st :=
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

  Section interp_types.

    Variable interp : Ty -> Type.

    Inductive interp_types : list Ty -> Type :=
    | Nil : interp_types nil
    | Cons : forall {type}, interp type -> forall types, interp_types types -> interp_types (type :: types).

  End interp_types.

  Definition interp_type ty : Type :=
    match ty with
      | TSCA => W
      | TADT => ADTValue
    end.
  
  Definition interp_output ty : Type :=
    match ty with
      | TSCA => unit
      | TADT => option ADTValue
    end.

  Record AxiomaticSpec :=
    {
      arg_types : list Ty;
      ret_type : Ty;
      pre_cond : interp_types interp_type arg_types -> Prop;
      post_cond : interp_types interp_type arg_types -> interp_types interp_output arg_types -> interp_type ret_type -> Prop
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

  Record Env := 
    {
      Label2Word : glabel -> option W ;
      Word2Spec : W ->option FuncSpec
    }.
  
  Definition type_dec (type : Ty) : {type = TSCA} + {type = TADT}.
    destruct type; eauto.
  Defined.

  Definition cast_sca type (v : interp_type type) (h : type = TSCA) : W.
    rewrite h in *; simpl in *.
    exact v.
  Defined.

  Definition cast_adt type (v : interp_type type) (h : type = TADT) : ADTValue.
    rewrite h in *; simpl in *.
    exact v.
  Defined.

  Definition find_adt x st := StringMap.find x (adt_map st).

  Definition match_type st x {type} (v : interp_type type) :=
    match type_dec type with
      | left h => sca_map st x = cast_sca v h
      | right h => find_adt x st = Some (cast_adt v h)
    end.

  Fixpoint match_st st keys types (values : interp_types interp_type types) :=
    match keys, values with
      | k :: keys', Cons _ v _ values' => 
        match_type st k v /\
        match_st st keys' values'
      | nil, Nil => True
      | _, _ => False
    end.

  Definition cast_option_adt type (v : interp_output type) (h : type = TADT) : option ADTValue.
    rewrite h in *; simpl in *.
    exact v.
  Defined.

  Definition add_remove_typed k {type} (o : interp_output type) st :=
    match type_dec type with
      | right h => add_remove k (cast_option_adt o h) st
      | _ => st
    end.

  Fixpoint add_remove_many keys types (output : interp_types interp_output types) st :=
    match keys, output with 
      | k :: keys', Cons _ o _ output' => 
        add_remove_many keys' output' (add_remove_typed k o st)
      | _, _ => st
    end.

  Definition upd_st keys types (output : interp_types interp_output types) (st : State) : State :=
    {| sca_map := sca_map st ; adt_map := add_remove_many keys output (adt_map st) |}.

  Require Import Locals.

  Definition add_sca x w (st : State) : State := {| sca_map := Locals.upd (sca_map st) x w; adt_map := adt_map st |}.

  Definition add_adt x v (st : State) : State := {| sca_map := sca_map st; adt_map := add x v (adt_map st) |}.

  Definition add_st k {type} (v : interp_type type) st :=
    match type_dec type with
      | left h => add_sca k (cast_sca v h) st
      | right h => add_adt k (cast_adt v h) st
    end.

  Definition add_var x (v : interp_type (vartype x)) st := add_st (varname x) v st.

  Require Import Basics.

  Infix "*" := compose : program_scope.
  Delimit Scope program_scope with program.

  Definition is_adt type := match type with TADT => true | TSCA => false end.

  Definition NoDupADT := (@List.NoDup _ * (List.map varname) * (List.filter (is_adt * vartype)))%program.

(*
  Fixpoint make_state keys values :=
    match keys, values with
      | k :: keys', v :: values' => add k v (make_state keys' values')
      | _, _ => @empty Value
    end.
*)

  Definition cast_back_unit type (v : unit) (h : type = TSCA) : interp_output type.
    rewrite h in *; simpl in *.
    exact v.
  Defined.

  Definition cast_back_option_adt type (v : option ADTValue) (h : type = TADT) : interp_output type.
    rewrite h in *; simpl in *.
    exact v.
  Defined.

  Definition get_one_output st k type : interp_output type :=
    match type_dec type with
      | left h => cast_back_unit tt h
      | right h => cast_back_option_adt (find_adt k st) h
    end.

  Definition empty_output type : interp_output type :=
    match type_dec type with
      | left h => cast_back_unit tt h
      | right h => cast_back_option_adt None h
    end.

  Fixpoint empty_outputs types : interp_types interp_output types :=
    match types with
      | type :: types' => Cons (empty_output type) (empty_outputs types')
      | nil => @Nil _
    end.

  Fixpoint get_output st keys types : interp_types interp_output types :=
    match types with
      | type :: types' =>
        match keys with
          | k :: keys' => Cons (get_one_output st k type) (get_output st keys' types')
          | nil => empty_outputs (type :: types')
        end
      | nil => @Nil _
    end.

  Definition cast_back_sca type (v : W) (h : type = TSCA) : interp_type type.
    rewrite h in *; simpl in *.
    exact v.
  Defined.

  Definition cast_back_adt type (v : ADTValue) (h : type = TADT) : interp_type type.
    rewrite h in *; simpl in *.
    exact v.
  Defined.

  Definition find_var type name st : option (interp_type type) :=
    match type_dec type with
      | left h => Some (cast_back_sca (sca_map st name) h)
      | right h => 
        match find_adt name st with
          | Some a => Some (cast_back_adt a h)
          | None => None
        end
    end.

  Definition st_equiv (a b : State) :=
    (forall x, sca_map a x = sca_map b x) /\
    adt_map a == adt_map b.

  Infix "==" := st_equiv.

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
        forall x e st st',
          let w := eval_st st e in
          st' == add_sca x w st ->
          RunsTo (Assign x e) st st'
    | RunsToLabel :
        forall x lbl st st' w,
          Label2Word env lbl = Some w ->
          st' == add_sca x w st ->
          RunsTo (Label x lbl) st st'
    | RunsToCallAx :
        forall x f args st spec,
          NoDupADT args ->
          let f_w := eval_st st f in
          Word2Spec env f_w = Some (Axiomatic spec) ->
          List.map vartype args = arg_types spec ->
          vartype x = ret_type spec ->
          forall input,
            let names := List.map varname args in
            match_st st names input ->
            pre_cond spec input ->
            forall output ret,
              post_cond spec input output ret ->
              let st' := upd_st names output st in
              let st' := add_st (varname x) ret st' in
              forall st'',
                st'' == st' ->
                RunsTo (Call x f args) st st''
    | RunsToCallOp :
        forall x f args st spec,
          NoDupADT args ->
          let f_w := eval_st st f in
          Word2Spec env f_w = Some (Operational spec) ->
          length args = length (ArgVars spec) ->
          let argtypes := List.map vartype args in
          forall input,
            let names := List.map varname args in
            @match_st st names argtypes input ->
            forall callee_st callee_st',
              match_st callee_st (ArgVars spec) input ->
              RunsTo (Body spec) callee_st callee_st' ->
              let output := get_output callee_st' (ArgVars spec) argtypes in
              forall ret,
                find_var (vartype x) (RetVar spec) callee_st' = Some ret ->
                let st' := upd_st names output st in
                let st' := add_st (varname x) ret st' in
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
          Safe (Call x f args) st.

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

  Definition CitoInOut_FacadeInOut (in_out : Cito.ArgIn * Cito.ArgOut) : Value * option Value :=
    match fst in_out, snd in_out with
      | inl w, _ => (SCA _ w, Some (SCA _ w))
      | inr a, Some a' => (ADT a, Some (ADT a'))
      | inr a, None => (ADT a, None)
    end.

  Definition compile_ax (spec : AxiomaticSpec) : Cito.Callee :=
    Semantics.Foreign 
      {|
        Semantics.PreCond args := PreCond spec (List.map CitoIn_FacadeIn args) ;
        Semantics.PostCond pairs ret := PostCond spec (List.map CitoInOut_FacadeInOut pairs) (CitoIn_FacadeIn ret)
      |}.

  Definition compile_op (specs : Env) (spec : OperationalSpec) : Cito.Callee :=
    Semantics.Foreign
      {|
        Semantics.PreCond args := 
          let st := make_state (ArgVars spec) (List.map CitoIn_FacadeIn args) in
          Safe specs (Body spec) st ;
        Semantics.PostCond pairs ret := 
          List.length pairs = List.length (ArgVars spec) /\
          let input := List.map (fun x => CitoIn_FacadeIn (fst x)) pairs in
          let output := List.map (fun x => snd (CitoInOut_FacadeInOut x)) pairs in
          let st := make_state (ArgVars spec) input in
          let st' := add_remove_many (ArgVars spec) input output st in
          let st' := add (RetVar spec) (CitoIn_FacadeIn ret) st' in
          RunsTo specs (Body spec) st st'
      |}.

  Definition FuncSpec := @FuncSpec ADTValue.

  Definition compile_spec specs (spec : FuncSpec) : Cito.Callee :=
    match spec with
      | Axiomatic s => compile_ax s
      | Operational s => compile_op specs s
    end.

  Definition compile_env (env : Env) : CitoEnv :=
    (Label2Word env, 
     fun w => option_map (compile_spec env) (Word2Spec env w)).
    
  Theorem compile_runsto : forall t t_env t_st t_st', Cito.RunsTo t_env t t_st t_st' -> forall s, t = compile s -> forall s_env s_st, t_env = compile_env s_env -> related_state s_st t_st -> exists s_st', RunsTo s_env s s_st s_st' /\ related_state s_st' t_st'.
  Proof.
    induction 1; simpl; intros; destruct s; simpl in *; intros; try discriminate.
    eexists; split.
    eapply RunsToSkip.
    eauto.

    admit.

    injection H1; intros; subst; clear H1.
    edestruct IHRunsTo.
    eauto.
    eauto.
    eauto.
    Require Import GeneralTactics.
    openhyp.
    eexists.
    split.
    eapply RunsToIfTrue.
    unfold is_true.
    unfold eval_bool.


    admit.

    eauto.
    eauto.

    admit.
    admit.
    admit.

    Require Import GeneralTactics3.
    unfold_all.
    injection H2; intros; subst.
    simpl in *.
    destruct (Word2Spec s_env (SemanticsExpr.eval (fst v) e)); simpl in *.
    injection H; intros; subst.
    destruct f; simpl in *.
    destruct a; simpl in *.
    unfold compile_ax in *; simpl in *; discriminate.
    unfold compile_op in *; simpl in *; discriminate.
    discriminate.

    unfold_all.
    injection H6; intros; subst; clear H6.
    simpl in *.
    destruct (option_dec (Word2Spec s_env (SemanticsExpr.eval (fst v) e))).
    destruct s.
    rewrite e0 in *; simpl in *.
    injection H; intros; subst; clear H.
    destruct x; simpl in *.
    destruct a; simpl in *.
    unfold compile_ax in *; simpl in *.
    injection H6; intros; subst; simpl in *; clear H6.
    admit.

    destruct o0; simpl in *.
    injection H6; intros; subst; simpl in *; clear H6.
    openhyp.
    eexists.
    split.
    eapply RunsToCallOp.
    admit.

  Qed.

End Make.

