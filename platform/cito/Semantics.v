Require Import IL Memory String Word Locals.
Require Import Sets.
Require Import Syntax.
Require Import SemanticsExpr.

Set Implicit Arguments.

Module WKey : S with Definition A := W.
  Definition A := W.
  Definition eq_dec := @weq 32.
End WKey.

Module WSet := Make WKey.
Import WSet.

Section models.

Variables models : string -> option Set.

Definition get_model s :=
  match models s with
    | None => unit
    | Some t => t
  end.

Record ADTValue := {
  TypeName : string;
  Value : get_model TypeName
}.
                    
Definition Heap := (set * (W -> ADTValue))%type.

Definition upd_arrow A (m : W -> A) k v k' :=
  if weq k' k then v else m k'.

Definition heap_in w (heap : Heap) := WSet.mem w (fst heap).

Definition heap_sel (heap : Heap) w := snd heap w.

Definition heap_upd (heap : Heap) w v : Heap := (WSet.add (fst heap) w, upd_arrow (snd heap) w v).

Definition st := (vals * Heap)%type.

Inductive ArgSignature := 
  | SigWord : ArgSignature
  | SigADT : string -> ArgSignature.

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

Definition set_value adt_value value := {| TypeName := TypeName adt_value; Value := value |}.

Definition match_sig heap w t : Prop := 
  match t with
    | SigWord => True
    | SigADT adt => heap_in w heap /\ TypeName (heap_sel heap w) = adt
  end.

Definition match_signature heap := Forall2 (match_sig heap).

Definition match_result := Forall2 (fun (v : ArgType) t =>
  match t with
    | SigWord => if v then True else False
    | SigADT adt => 
      match v with
        | inl _ => False
        | inr adt_value => TypeName adt_value = adt
      end
  end).                                       

Definition good_return heap ret sig :=
  match sig with
    | SigWord => True
    | SigADT adt =>                    
      match snd ret with
        | None => False
        | Some adt_value => ~ heap_in (fst ret) heap /\ TypeName adt_value = adt
      end
  end.

Fixpoint get_args heap args sig : list ArgType :=
  match args, sig with
    | w :: ws, t :: ts => 
      match t with
        | SigWord => inl w :: get_args heap ws ts
        | SigADT _ => inr (heap_sel heap w) :: get_args heap ws ts
      end
    | _, _ => nil
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
        | inr adt_value => store_result (heap_upd heap w adt_value) ws vs
      end
    | _, _ => heap
  end.

Definition store_return (heap : Heap) ret :=
  match snd ret with
    | None => heap
    | Some adt_value => heap_upd heap (fst ret) adt_value
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
  | CallForeign : forall vs adts var f args spec ret result,
      let v := (vs, adts) in
      let args_v := map (fun e => exprDenote e vs) args in
      let sig := Signature spec in
      let (args_sig, ret_sig) := sig in 
      functions (exprDenote f vs) = Some (Foreign spec)
      -> match_signature adts args_v args_sig
      -> match_result result args_sig             
      -> good_return adts ret ret_sig             
      -> Pred spec {| Args := get_args adts args_v args_sig; Ret := ret; After := result |}
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
