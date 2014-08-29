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
        forall x f args st spec input output ret f_w,
          NoDup args ->
          eval st f = Some (SCA f_w) ->
          Word2Spec env f_w = Some (Axiomatic spec) ->
          mapM (sel st) args = Some input ->
          PreCond spec input ->
          length input = length output ->
          PostCond spec (combine input output) ret ->
          let st' := add_remove_many args input output st in
          let st' := addM x ret st' in
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
          let output := map (sel callee_st') (ArgVars spec) in
          sel callee_st' (RetVar spec) = Some ret ->
          let st' := add_remove_many args input output st in
          let st' := addM x ret st' in
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

  Definition compile_op (spec : OperationalSpec) : Cito.Callee.
    refine
      (Cito.Internal
         {|
           Semantics.Fun :=
             {|
               FuncCore.ArgVars := ArgVars spec;
               FuncCore.RetVar := RetVar spec;
               FuncCore.Body := compile (Body spec)
             |};
           Semantics.NoDupArgVars := _
         |}
      ).
    simpl.
    destruct spec.
    simpl.
    inversion NoDupArgVars0.
    eauto.
  Defined.

  Definition FuncSpec := @FuncSpec ADTValue.

  Definition compile_spec (spec : FuncSpec) : Cito.Callee :=
    match spec with
      | Axiomatic s => compile_ax s
      | Operational s => compile_op s
    end.

  Definition compile_env (env : Env) : CitoEnv :=
    (Label2Word env, 
     fun w => option_map compile_spec (Word2Spec env w)).
    
  Require Import GeneralTactics.
  Require Import GeneralTactics3.

  Ltac inject h := injection h; intros; subst; clear h.

  Definition get_ret (st : Cito.State) x : Value :=
    let w := fst st x in
    match Cito.heap_sel (snd st) w with
      | Some a => ADT a
      | None => SCA _ w
    end.

  Theorem compile_runsto : forall t t_env t_st t_st', Cito.RunsTo t_env t t_st t_st' -> forall s, t = compile s -> forall s_env s_st, t_env = compile_env s_env -> related_state s_st t_st -> Safe s_env s s_st -> exists s_st', RunsTo s_env s s_st s_st' /\ related_state s_st' t_st'.
  Proof.
    induction 1; simpl; intros; destruct s; simpl in *; intros; try discriminate.

    (* skip *)
    eexists; split.
    eapply RunsToSkip.
    eauto.

    (* seq *)
    subst.
    inject H1.
    edestruct IHRunsTo1; clear IHRunsTo1; eauto.
    Lemma safe_seq_1 : forall (env : Env) a b st, Safe env (Seq a b) st -> Safe env a st.
    Proof.
      intros.
      inversion H; subst.
      openhyp.
      eauto.
    Qed.
    eapply safe_seq_1; eauto.
    openhyp.
    edestruct IHRunsTo2; clear IHRunsTo2; eauto.
    Lemma safe_seq_2 : forall (env : Env) a b st, Safe env (Seq a b) st -> forall st', RunsTo env a st st' -> Safe env b st'.
    Proof.
      intros.
      inversion H; subst.
      openhyp.
      eauto.
    Qed.
    eapply safe_seq_2; eauto.
    openhyp.
    eexists.
    split.
    eapply RunsToSeq; eauto.
    eauto.

    (* if-true *)
    injection H1; intros; subst; clear H1.
    edestruct IHRunsTo.
    eauto.
    eauto.
    eauto.
    Notation ceval := SemanticsExpr.eval.
    Notation cRunsTo := Semantics.RunsTo.
    Lemma is_true_is_false : forall (st : State) e, is_true st e -> is_false st e -> False.
    Proof.
      intros.
      unfold is_true, is_false in *.
      rewrite H in *; discriminate.
    Qed.
    Lemma safe_if_true : forall (env : Env) e t f st, Safe env (If e t f) st -> is_true st e -> Safe env t st.
    Proof.
      intros.
      inversion H; subst.
      eauto.
      exfalso.
      eapply is_true_is_false; eauto.
    Qed.
    eapply safe_if_true; eauto.
    Definition is_bool (st : State) e := eval_bool st e <> None.
    Lemma wneb_is_true : forall s_st t_st e, wneb (ceval (fst t_st) e) $0 = true -> related_state s_st t_st -> is_bool s_st e -> is_true s_st e.
    Proof.
      intros.
      unfold is_true.
      unfold is_bool in *.
      eapply ex_up in H1.
      openhyp.
      Notation boolcase := Sumbool.sumbool_of_bool.
      destruct (boolcase x); subst.
      eauto.
      Lemma eval_bool_wneb : forall (s_st : State) t_st e b, eval_bool s_st e = Some b -> related_state s_st t_st -> wneb (ceval (fst t_st) e) $0 = b.
      Proof.
        admit.
      Qed.
      eapply eval_bool_wneb in H1; eauto.
      set (ceval _ _) in *.
      rewrite H in *; discriminate.
    Qed.
    eapply wneb_is_true; eauto.
    Lemma safe_if_is_bool : forall (env : Env) e t f st, Safe env (If e t f) st -> is_bool st e.
    Proof.
      admit.
    Qed.
    eapply safe_if_is_bool; eauto.
    openhyp.
    eexists.
    split.
    eapply RunsToIfTrue.
    eapply wneb_is_true; eauto.
    eapply safe_if_is_bool; eauto.

    eauto.
    eauto.

    (*here*)

    admit.
    admit.
    admit.

    unfold_all.
    injection H2; intros; subst; clear H2.
    simpl in *.
    destruct (option_dec (Word2Spec s_env (SemanticsExpr.eval (fst v) e))); simpl in *.
    destruct s.
    rewrite e0 in *; simpl in *.
    injection H; intros; subst; clear H.
    destruct x; simpl in *.
    destruct a; simpl in *; unfold compile_ax in *; simpl in *; discriminate.
    unfold compile_op in *; simpl in *.
    injection H2; intros; subst; simpl in *; clear H2.
    inversion H5; subst.
    replace f_w with (SemanticsExpr.eval (fst v) e) in * by admit.
    rewrite e0 in *.
    discriminate.
    
    unfold_all.
    replace f_w with (SemanticsExpr.eval (fst v) e) in * by admit.
    rewrite e0 in *.
    inject H8.

    edestruct IHRunsTo.
    eauto.
    eauto.
    Focus 3.
    openhyp.
    eexists.
    split.
    eapply RunsToCallOp.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    instantiate (1 := get_ret (vs_callee', heap') (RetVar spec)).
    admit.
    reflexivity.
    admit.
    admit.
    eauto.

    rewrite e0 in *; simpl in *; discriminate.

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
    (* eexists. *)
    (* split. *)
    (* eapply RunsToCallOp. *)
    admit.

    discriminate.
    
    rewrite e0 in *; simpl in *; discriminate.

    admit.

    admit.

  Qed.

End Make.