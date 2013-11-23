Require Import IL Memory String Word Locals.
Require Import Sets.
Require Import Syntax.
Require Import SemanticsExpr.
Require Import Dict.

Set Implicit Arguments.

Record ADT := {
  Model : Set;
}.

Record ADTValue := {
  Type_ : ADT;
  Value : Model Type_
}.
                    
Module Key <: MiniDecidableType.
  Definition t := W.
  Definition eq_dec := @weq
End Key.

Module Data <: Typ.
  Definition t := ADTValue.
End Data.

Module FMap := FMap.Make Key Data.
Definition heap_sel := FMap.sel.

Definition Heap := FMap.t.

Definition State := (vals * Heap)%type.

Definition ArgValue := (W + ADTValue)%type.

Definition OutValue := option ADTValue.

Definition RetValue := (W + ADTValue)%type.

Record ForeignFuncSpec := 
  {
    PreCond: list ArgValue -> Prop;
    PostCond : list (ArgValue * OutValue) -> RetValue -> Prop
  }.

Record InternalFuncSpec := {
  ArgVars : list string;
  RetVar : string;
  Body : Stmt
}.

Inductive Callee := 
  | Foreign : ForeignFuncSpec -> Callee
  | Internal : InternalFuncSpec -> Callee.

Definition match_heap (heap : Heap):= Forall2 (fun w (v : ArgValue) =>
  match v with
    | inl _ => True
    | inr adt_value => heap_sel heap w = Some adt_value
  end
).

Definition upd_lhs vs lhs addr (ret : RetValue) :=
  match lhs with
    | None => vs
    | Some x => 
      Locals.upd vs x 
                 (match ret with
                    | inr _ => addr
                    | inl w => w
                  end)
  end.

Fixpoint store_out (heap : Heap) ptrs (out : list OutValue) : Heap :=
  match ptrs, out with
    | w :: ws, v :: vs =>
      match v with 
        | None => store_out (heap_remove heap w) ws vs
        | Some adt_value => store_out (heap_upd heap w adt_value) ws vs
      end
    | _, _ => heap
  end.

Definition sel_all vs := map (fun x => Locals.sel vs x).

Definition new_return (heap : Heap) addr (ret : RetValue) :=
  match ret with
    | inr _ => ~ heap_mem heap addr
    | _ => True
  end.

Definition store_return (heap : Heap) addr (ret : RetValue) :=
  match ret with
    | inr adt_value => heap_upd heap addr adt_value
    | _ => heap
  end.

Definition upd_option vs var value :=
  match var with
    | None => vs
    | Some x => Locals.upd vs x value
  end.

(* Semantics *)

Section RunsTo.

  (* Map foreign function addresses to specifications. *)
  Variable functions : W -> option Callee.

  Inductive RunsTo : Stmt -> State -> State -> Prop :=
  | Skip : forall v, RunsTo Syntax.Skip v v
  | Seq : 
      forall v v' v'' a b,
        RunsTo a v v' -> 
        RunsTo b v' v'' -> 
        RunsTo (Syntax.Seq a b) v v''
  | IfTrue : 
      forall v v' cond t f, 
        wneb (exprDenote cond (fst v)) $0 = true -> 
        RunsTo t v v' -> 
        RunsTo (Syntax.If cond t f) v v'
  | IfFalse : 
      forall v v' cond t f, 
        wneb (exprDenote cond (fst v)) $0 = false -> 
        RunsTo f v v' -> 
        RunsTo (Syntax.If cond t f) v v'
  | WhileTrue : 
      forall v v' v'' cond body, 
        let statement := While cond body in
        wneb (exprDenote cond (fst v)) $0 = true -> 
        RunsTo body v v' -> 
        RunsTo statement v' v'' -> 
        RunsTo statement v v''
  | WhileFalse : 
      forall v cond body, 
        wneb (exprDenote cond (fst v)) $0 = false -> 
        RunsTo (While cond body) v v
  | CallInternal : 
      forall vs heap var f args spec vs_arg vs_arg' heap',
        let v := (vs, heap) in
        let args_v := map (fun e => exprDenote e vs) args in
        functions (exprDenote f vs) = Some (Internal spec)
        -> sel_all vs_arg (ArgVars spec) = args_v
        -> RunsTo (Body spec) (vs_arg, heap) (vs_arg', heap')
        -> RunsTo (Syntax.Call var f args) v (upd_option vs var (Locals.sel vs_arg' (RetVar spec)), heap')
  | CallForeign : 
      forall vs heap var f args spec bindings ret addr,
        let v := (vs, heap) in
        let args_v := map (fun e => exprDenote e vs) args in
        functions (exprDenote f vs) = Some (Foreign spec) ->
        let args_a := map fst bindings in 
        let out := map snd bindings in
        match_heap heap args_v args_v ->
        PreCond spec args_a ->
        PostCond spec bindings ret -> 
        let heap' := store_out heap args_v out in
        new_return heap' addr ret ->
        RunsTo (Syntax.Call var f args) v (upd_lhs vs var addr ret, store_return heap' addr ret).

End RunsTo.

Module Safety.

Section functions'.

Variable functions : W -> option Callee.

CoInductive Safe : Stmt -> st -> Prop :=
  | Skip : forall v, Safe Syntax.Skip v
  | Seq : forall a b v, 
      Safe a v ->
      (forall v', RunsTo functions a v v' -> Safe b v') -> 
      Safe (Syntax.Seq a b) v
  | IfTrue : forall v cond t f, 
      wneb (exprDenote cond (fst v)) $0 = true -> 
      Safe t v -> 
      Safe (Syntax.If cond t f) v
  | IfFalse : forall v cond t f, 
      wneb (exprDenote cond (fst v)) $0 = false -> 
      Safe f v -> 
      Safe (Syntax.If cond t f) v
  | WhileTrue : forall v cond body, 
      let statement := While cond body in
      wneb (exprDenote cond (fst v)) $0 = true -> 
      Safe body v ->
      (forall v', RunsTo functions body v v' -> Safe statement v') -> 
      Safe statement v
  | WhileFalse : forall v cond body, 
      wneb (exprDenote cond (fst v)) $0 = false -> 
<<<<<<< local
      Safe (While cond body) v
  | CallInternal : forall vs heap var f args spec,
      let v := (vs, heap) in
      let args_v := map (fun e => exprDenote e vs) args in
      functions (exprDenote f vs) = Some (Internal spec)
      -> (forall vs_arg, sel_all vs_arg (ArgVars spec) = args_v -> Safe (Body spec) (vs_arg, heap))
      -> Safe (Syntax.Call var f args) v
  | CallForeign : forall vs heap var f args spec adt_values ret,
      let v := (vs, heap) in
      let args_v := map (fun e => exprDenote e vs) args in
      functions (exprDenote f vs) = Some (Foreign spec)
      -> match_heap heap args_v (map fst adt_values)
      -> Pred spec {| Args := adt_values; Ret := ret |}
      -> Safe (Syntax.Call var f args) v.
=======
      Safe (Loop cond body) v
  | ConditionalTrue : forall v cond t f, 
      wneb (exprDenote cond (fst v)) $0 = true -> 
      Safe t v -> 
      Safe (Conditional cond t f) v
  | ConditionFalse : forall v cond t f, 
      wneb (exprDenote cond (fst v)) $0 = false -> 
      Safe f v -> 
      Safe (Conditional cond t f) v
  | Assignment : forall var value v,
      Safe (Syntax.Assignment var value) v
  | ReadAt : forall var arr idx vs (arrs : arrays),
      let v := (vs, arrs) in
      let arr_v := exprDenote arr vs in
      let idx_v := exprDenote idx vs in
      safe_access arrs arr_v idx_v -> 
      Safe (Syntax.ReadAt var arr idx) v
  | WriteAt : forall arr idx value vs (arrs : arrays), 
      let v := (vs, arrs) in
      let arr_v := exprDenote arr vs in
      let idx_v := exprDenote idx vs in
      safe_access arrs arr_v idx_v ->
      Safe (Syntax.WriteAt arr idx value) v
  | Skip : forall v, Safe Syntax.Skip v
  | Malloc : forall var size vs (arrs : arrays),
      let size_v := exprDenote size vs in
      goodSize (wordToNat size_v + 2) ->
      Safe (Syntax.Malloc var size) (vs, arrs)
  | Free : forall arr vs (arrs : arrays),
      let arr_v := exprDenote arr vs in
      arr_v %in fst arrs ->
      Safe (Syntax.Free arr) (vs, arrs)
  | Len : forall var arr vs (arrs : arrays),
      let arr_v := exprDenote arr vs in
      arr_v %in fst arrs ->
      Safe (Syntax.Len var arr) (vs, arrs)
  | CallForeign : forall vs arrs f arg precond spec,
      let arg_v := exprDenote arg vs in
      functions (exprDenote f vs) = Some (Foreign precond spec)
      -> precond arg_v arrs
      -> Safe (Syntax.Call f arg) (vs, arrs)
  | CallInternal : forall vs arrs f arg body,
      let arg_v := exprDenote arg vs in
      functions (exprDenote f vs) = Some (Internal body)
      -> (forall vs_arg, Locals.sel vs_arg "__arg" = arg_v -> Safe body (vs_arg, arrs))
      -> Safe (Syntax.Call f arg) (vs, arrs).

  Section Safe_coind.
    Variable R : Stmt -> st -> Prop.

    Import WMake.

    Hypothesis ReadAtCase : forall var arr idx vs arrs, R (Syntax.ReadAt var arr idx) (vs, arrs) -> safe_access arrs (exprDenote arr vs) (exprDenote idx vs).

    Hypothesis WriteAtCase : forall arr idx val vs arrs, R (Syntax.WriteAt arr idx val) (vs, arrs) -> safe_access arrs (exprDenote arr vs) (exprDenote idx vs).
    
    Hypothesis SeqCase : forall a b v, R (Syntax.Seq a b) v -> R a v /\ forall v', RunsTo functions a v v' -> R b v'.
    
    Hypothesis ConditionalCase : forall cond t f v, R (Syntax.Conditional cond t f) v -> (wneb (exprDenote cond (fst v)) $0 = true /\ R t v) \/ (wneb (exprDenote cond (fst v)) $0 = false /\ R f v).
    
    Hypothesis LoopCase : forall cond body v, R (Syntax.Loop cond body) v -> (wneb (exprDenote cond (fst v)) $0 = true /\ R body v /\ (forall v', RunsTo functions body v v' -> R (Loop cond body) v')) \/ (wneb (exprDenote cond (fst v)) $0 = false).
    
    Hypothesis MallocCase : forall var size vs arrs, R (Syntax.Malloc var size) (vs, arrs) -> goodSize (wordToNat (exprDenote size vs) + 2).
    
    Hypothesis FreeCase : forall arr vs arrs, R (Syntax.Free arr) (vs, arrs) -> (exprDenote arr vs) %in (fst arrs).
    
    Hypothesis LenCase : forall var arr vs arrs, R (Syntax.Len var arr) (vs, arrs) -> (exprDenote arr vs) %in (fst arrs).

    Hypothesis ForeignCallCase : forall vs arrs f arg,
      R (Syntax.Call f arg) (vs, arrs)
      -> (exists precond spec, functions (exprDenote f vs) = Some (Foreign precond spec)
        /\ precond (exprDenote arg vs) arrs) \/
      (exists body, functions (exprDenote f vs) = Some (Internal body) /\ forall vs_arg, Locals.sel vs_arg "__arg" = exprDenote arg vs -> R body (vs_arg, arrs)).

    Hint Constructors Safe.

    Ltac openhyp := 
      repeat match goal with
               | H : _ /\ _ |- _  => destruct H
               | H : _ \/ _ |- _ => destruct H
               | H : exists x, _ |- _ => destruct H
             end.

    Ltac break_pair :=
      match goal with
        V : (_ * _)%type |- _ => destruct V
      end.

    Theorem Safe_coind : forall c v, R c v -> Safe c v.
      cofix; unfold st; intros; break_pair; destruct c.

      eauto.
      Guarded.

      eapply ReadAtCase in H; openhyp; eauto.
      Guarded.

      eapply WriteAtCase in H; openhyp; eauto.
      Guarded.

      eapply SeqCase in H; openhyp; eauto.
      Guarded.

      eauto.
      Guarded.

      eapply ConditionalCase in H; openhyp; eauto.
      Guarded.

      eapply LoopCase in H; openhyp; eauto.
      Guarded.

      eapply MallocCase in H; openhyp; eauto.
      Guarded.

      eapply FreeCase in H; openhyp; eauto.
      Guarded.

      eapply LenCase in H; openhyp; eauto.
      Guarded.

      eapply ForeignCallCase in H; openhyp; eauto.
      Guarded.
    Qed.

  End Safe_coind.
>>>>>>> other

End functions'.

End Safety.
