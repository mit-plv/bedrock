Require Import IL Memory String Word Locals.
Require Import Sets.
Require Import Syntax.
Require Import SemanticsExpr.
Require Import Dict.

Set Implicit Arguments.

Record ADT := {
  Model : Set;
  Name : string
}.

Record ADTValue := {
  TheType : ADT;
  Value : Model TheType
}.
                    
Module MKey : KEY with Definition key := W.
  Definition key := W.
  Definition eq_dec := @weq 32.
End MKey.

Module MData : DATA with Definition data := ADTValue.
  Definition data := ADTValue.
End MData.

Module MHeap := Dict.Dict MKey MData.

Definition Heap := MHeap.dict.

Definition st := (vals * Heap)%type.

Definition ArgValue := (W + ADTValue)%type.

Definition ResultValue := option ADTValue.

Definition RetValue := (W + ADTValue)%type.

Record callTransition := {
  Args : list (ArgValue * ResultValue);
  Ret : RetValue
}.

Record ForeignFuncSpec := {
  Pred : callTransition -> Prop
}.

Record InternalFuncSpec := {
  ArgVars : list string;
  RetVar : string;
  Body : Statement
}.

Inductive Callee := 
  | Foreign : ForeignFuncSpec -> Callee
  | Internal : InternalFuncSpec -> Callee.

Definition match_heap (heap : Heap):= Forall2 (fun w (v : ArgValue) =>
  match v with
    | inl _ => True
    | inr adt_value => MHeap.mem heap w /\ MHeap.sel heap w = adt_value
  end
).

Definition upd_lhs vs lhs addr (ret : RetValue) :=
  match lhs with
    | None => vs
    | Some x => 
      let rhs :=
          match ret with
            | inr _ => addr
            | inl w => w
          end in
      Locals.upd vs x rhs
  end.

Fixpoint store_result (heap : Heap) ptrs (result : list ResultValue) : Heap :=
  match ptrs, result with
    | w :: ws, v :: vs =>
      match v with 
        | None => store_result (MHeap.remove heap w) ws vs
        | Some adt_value => store_result (MHeap.upd heap w adt_value) ws vs
      end
    | _, _ => heap
  end.

Definition sels vs xs := map (fun x => Locals.sel vs x) xs.

Definition new_return (heap : Heap) addr (ret : RetValue) :=
  match ret with
    | inr _ => ~ MHeap.mem heap addr
    | _ => True
  end.

Definition store_return (heap : Heap) addr (ret : RetValue) :=
  match ret with
    | inr adt_value => MHeap.upd heap addr adt_value
    | _ => heap
  end.

Definition upd_option vs var value :=
  match var with
    | None => vs
    | Some x => Locals.upd vs x value
  end.

(* Semantics *)

Section functions.

Variable functions : W -> option Callee.
(* Map foreign function addresses to specifications. *)

Inductive RunsTo : Statement -> st -> st -> Prop :=
  | Skip : forall v, RunsTo Syntax.Skip v v
  | Seq : forall v v' v'' a b,
      RunsTo a v v' -> 
      RunsTo b v' v'' -> 
      RunsTo (Syntax.Seq a b) v v''
  | IfTrue : forall v v' cond t f, 
      wneb (exprDenote cond (fst v)) $0 = true -> 
      RunsTo t v v' -> 
      RunsTo (Syntax.If cond t f) v v'
  | IfFalse : forall v v' cond t f, 
      wneb (exprDenote cond (fst v)) $0 = false -> 
      RunsTo f v v' -> 
      RunsTo (Syntax.If cond t f) v v'
  | WhileTrue : forall v v' v'' cond body, 
      let statement := While cond body in
      wneb (exprDenote cond (fst v)) $0 = true -> 
      RunsTo body v v' -> 
      RunsTo statement v' v'' -> 
      RunsTo statement v v''
  | WhileFalse : forall v cond body, 
      wneb (exprDenote cond (fst v)) $0 = false -> 
      RunsTo (While cond body) v v
  | CallInternal : forall vs heap var f args spec vs_arg vs_arg' heap',
      let v := (vs, heap) in
      let args_v := map (fun e => exprDenote e vs) args in
      functions (exprDenote f vs) = Some (Internal spec)
      -> sels vs_arg (ArgVars spec) = args_v
      -> RunsTo (Body spec) (vs_arg, heap) (vs_arg', heap')
      -> RunsTo (Syntax.Call var f args) v (upd_option vs var (Locals.sel vs_arg' (RetVar spec)), heap')
  | CallForeign : forall vs heap var f args spec adt_values ret addr,
      let v := (vs, heap) in
      let args_v := map (fun e => exprDenote e vs) args in
      functions (exprDenote f vs) = Some (Foreign spec)
      -> match_heap heap args_v (map fst adt_values)
      -> Pred spec {| Args := adt_values; Ret := ret |}
      -> let heap' := store_result heap args_v (map snd adt_values) in
         new_return heap' addr ret
      -> RunsTo (Syntax.Call var f args) v (upd_lhs vs var addr ret, store_return heap' addr ret).

End functions.

Module Safety.

Section functions'.

Variable functions : W -> option Callee.

CoInductive Safe : Statement -> st -> Prop :=
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
      Safe (While cond body) v
  | CallInternal : forall vs heap var f args spec,
      let v := (vs, heap) in
      let args_v := map (fun e => exprDenote e vs) args in
      functions (exprDenote f vs) = Some (Internal spec)
      -> (forall vs_arg, sels vs_arg (ArgVars spec) = args_v -> Safe (Body spec) (vs_arg, heap))
      -> Safe (Syntax.Call var f args) v
  | CallForeign : forall vs heap var f args spec adt_values ret,
      let v := (vs, heap) in
      let args_v := map (fun e => exprDenote e vs) args in
      functions (exprDenote f vs) = Some (Foreign spec)
      -> match_heap heap args_v (map fst adt_values)
      -> Pred spec {| Args := adt_values; Ret := ret |}
      -> Safe (Syntax.Call var f args) v.

End functions'.

End Safety.
