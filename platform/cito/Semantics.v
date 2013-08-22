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

Definition ArgType := (W + ADTValue)%type.

Definition ResultType := (W + option ADTValue)%type.

Definition RetType := (W * option ADTValue)%type.

Record callTransition := {
  Args : list ArgType;
  After : list ResultType;
  Ret : RetType
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

Definition match_heap (heap : Heap):= Forall2 (fun w (v : ArgType) =>
  match v with
    | inl _ => True
    | inr adt_value => MHeap.mem heap w /\ MHeap.sel heap w = adt_value
  end
).

Definition new_return (heap : Heap) (ret : RetType) :=
  match snd ret with
    | None => True
    | Some _ => ~ MHeap.mem heap (fst ret)
  end.

Definition upd_option vs var value :=
  match var with
    | None => vs
    | Some x => Locals.upd vs x value
  end.

Fixpoint store_result (heap : Heap) ptrs (result : list ResultType) : Heap :=
  match ptrs, result with
    | w :: ws, v :: vs =>
      match v with 
        | inl _ => store_result heap ws vs
        | inr v' => 
          match v' with
            | None => store_result (MHeap.remove heap w) ws vs
            | Some adt_value => store_result (MHeap.upd heap w adt_value) ws vs
          end
      end
    | _, _ => heap
  end.

Definition store_return (heap : Heap) ret :=
  match snd ret with
    | None => heap
    | Some adt_value => MHeap.upd heap (fst ret) adt_value
  end.

Definition sels vs xs := map (fun x => Locals.sel vs x) xs.

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
  | Assign : forall var value vs adts, 
      let v := (vs, adts) in
      let value_v := exprDenote value vs in
      RunsTo (Assign var value) v (Locals.upd vs var value_v, adts)
  | CallInternal : forall vs heap var f args spec vs_arg vs_arg' heap',
      let v := (vs, heap) in
      let args_v := map (fun e => exprDenote e vs) args in
      functions (exprDenote f vs) = Some (Internal spec)
      -> sels vs_arg (ArgVars spec) = args_v
      -> RunsTo (Body spec) (vs_arg, heap) (vs_arg', heap')
      -> RunsTo (Syntax.Call var f args) v (upd_option vs var (Locals.sel vs_arg' (RetVar spec)), heap')
  | CallForeign : forall vs heap var f args spec adt_values result ret,
      let v := (vs, heap) in
      let args_v := map (fun e => exprDenote e vs) args in
      functions (exprDenote f vs) = Some (Foreign spec)
      -> match_heap heap args_v adt_values
      -> Pred spec {| Args := adt_values; After := result; Ret := ret |}
      -> let heap' := store_result heap args_v result in
         new_return heap' ret
      -> RunsTo (Syntax.Call var f args) v (upd_option vs var (fst ret), store_return heap' ret).

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
  | Assign : forall var value v,
      Safe (Syntax.Assign var value) v
  | CallInternal : forall vs heap var f args spec,
      let v := (vs, heap) in
      let args_v := map (fun e => exprDenote e vs) args in
      functions (exprDenote f vs) = Some (Internal spec)
      -> (forall vs_arg, sels vs_arg (ArgVars spec) = args_v -> Safe (Body spec) (vs_arg, heap))
      -> Safe (Syntax.Call var f args) v
  | CallForeign : forall vs heap var f args spec adt_values result ret,
      let v := (vs, heap) in
      let args_v := map (fun e => exprDenote e vs) args in
      functions (exprDenote f vs) = Some (Foreign spec)
      -> match_heap heap args_v adt_values
      -> Pred spec {| Args := adt_values; Ret := ret; After := result |}
      -> Safe (Syntax.Call var f args) v.

End functions'.

End Safety.
