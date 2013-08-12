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

Inductive ArgSignature := 
  | SigWord : ArgSignature
  | SigADT : ADT -> ArgSignature.

Definition ArgType := (W + ADTValue)%type.

Definition RetType := (W * option ADTValue)%type.

Record callTransition := {
  Args : list ArgType;
  Ret : RetType;
  After : list ArgType
}.

Record ForeignFuncSpec := {
  Signature : list ArgSignature * ArgSignature;
  Pred : callTransition -> Prop
}.

Inductive Callee := 
  | Foreign : ForeignFuncSpec -> Callee
  | Internal : Statement -> Callee.

Definition set_value adt_value value := {| TheType := TheType adt_value; Value := value |}.

Definition match_heap (heap : Heap):= Forall2 (fun w (v : ArgType) =>
  match v with
    | inl _ => True
    | inr adt_value => MHeap.sel heap w = Some adt_value
  end
).

Definition match_signature := Forall2 (fun (v : ArgType) t =>
  match t with
    | SigWord => if v then True else False
    | SigADT adt => 
      match v with
        | inl _ => False
        | inr adt_value => TheType adt_value = adt
      end
  end).                                       

Definition good_return heap ret sig :=
  match sig with
    | SigWord => True
    | SigADT adt =>                    
      match snd ret with
        | None => False
        | Some adt_value => MHeap.sel heap (fst ret) = None /\ TheType adt_value = adt
      end
  end.

Definition upd_option vs var value :=
  match var with
    | None => vs
    | Some x => Locals.upd vs x value
  end.

Fixpoint store_result (heap : Heap) ptrs (result : list ArgType) : Heap :=
  match ptrs, result with
    | w :: ws, v :: vs =>
      match v with
        | inl _ => store_result heap ws vs
        | inr adt_value => store_result (MHeap.upd heap w adt_value) ws vs
      end
    | _, _ => heap
  end.

Definition store_return (heap : Heap) ret :=
  match snd ret with
    | None => heap
    | Some adt_value => MHeap.upd heap (fst ret) adt_value
  end.

Definition update_heap heap ptrs result ret := store_return (store_result heap ptrs result) ret.

Definition upd_st (v : st) var ptrs result ret : st := let (vs, adts) := v in (upd_option vs var (fst ret), update_heap adts ptrs result ret).

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
  | ConditionalTrue : forall v v' cond t f, 
      wneb (exprDenote cond (fst v)) $0 = true -> 
      RunsTo t v v' -> 
      RunsTo (Conditional cond t f) v v'
  | ConditionFalse : forall v v' cond t f, 
      wneb (exprDenote cond (fst v)) $0 = false -> 
      RunsTo f v v' -> 
      RunsTo (Conditional cond t f) v v'
  | LoopTrue : forall v v' v'' cond body, 
      let statement := Loop cond body in
      wneb (exprDenote cond (fst v)) $0 = true -> 
      RunsTo body v v' -> 
      RunsTo statement v' v'' -> 
      RunsTo statement v v''
  | LoopFalse : forall v cond body, 
      wneb (exprDenote cond (fst v)) $0 = false -> 
      RunsTo (Loop cond body) v v
  | Assignment : forall var value vs adts, 
      let v := (vs, adts) in
      let value_v := exprDenote value vs in
      RunsTo (Syntax.Assignment var value) v (Locals.upd vs var value_v, adts)
  | CallInternal : forall vs adts f adts' body arg vs_arg vs',
      let v := (vs, adts) in
      let arg_v := exprDenote arg vs in
      functions (exprDenote f vs) = Some (Internal body)
      -> Locals.sel vs_arg "__arg" = arg_v
      -> RunsTo body (vs_arg, adts) (vs', adts')
      -> RunsTo (Syntax.Call None f (arg :: nil)) v (vs, adts')
  | CallForeign : forall vs heap var f args adt_values spec ret result,
      let v := (vs, heap) in
      let args_v := map (fun e => exprDenote e vs) args in
      let sig := Signature spec in
      let (args_sig, ret_sig) := sig in 
      functions (exprDenote f vs) = Some (Foreign spec)
      -> match_heap heap args_v adt_values
      -> match_signature adt_values args_sig                        
      -> match_signature result args_sig             
      -> good_return heap ret ret_sig             
      -> Pred spec {| Args := adt_values; Ret := ret; After := result |}
      -> RunsTo (Syntax.Call var f args) v (upd_st v var args_v result ret).

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
  | ConditionalTrue : forall v cond t f, 
      wneb (exprDenote cond (fst v)) $0 = true -> 
      Safe t v -> 
      Safe (Conditional cond t f) v
  | ConditionFalse : forall v cond t f, 
      wneb (exprDenote cond (fst v)) $0 = false -> 
      Safe f v -> 
      Safe (Conditional cond t f) v
  | LoopTrue : forall v cond body, 
      let statement := Loop cond body in
      wneb (exprDenote cond (fst v)) $0 = true -> 
      Safe body v ->
      (forall v', RunsTo functions body v v' -> Safe statement v') -> 
      Safe statement v
  | LoopFalse : forall v cond body, 
      wneb (exprDenote cond (fst v)) $0 = false -> 
      Safe (Loop cond body) v
  | Assignment : forall var value v,
      Safe (Syntax.Assignment var value) v
  | CallForeign : forall vs adts var f args spec ret adts',
      let args_v := map (fun e => exprDenote e vs) args in
      functions (exprDenote f vs) = Some (Foreign spec)
      -> spec {| Args := args_v; Ret := ret; InitialHeap := adts; FinalHeap := adts' |}
      -> Safe (Syntax.Call var f args) (vs, adts)
  | CallInternal : forall vs adts f arg body,
      let arg_v := exprDenote arg vs in
      functions (exprDenote f vs) = Some (Internal body)
      -> (forall vs_arg, Locals.sel vs_arg "__arg" = arg_v -> Safe body (vs_arg, adts))
      -> Safe (Syntax.Call None f (arg :: nil)) (vs, adts)
  | CallMethod : forall vs adts var obj f args obj_adt spec new_value ret,
      let args_v := map (fun e => exprDenote e vs) args in
      let obj_v := exprDenote obj vs in
      Heap.sel adts obj_v = Some obj_adt
      -> Methods (TheType obj_adt) f = Some spec
      -> spec (Value obj_adt) args_v new_value ret
      -> Safe (Syntax.CallMethod var obj f args) (vs, adts).

End functions'.

End Safety.
