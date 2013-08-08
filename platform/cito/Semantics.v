Require Import IL Memory String Word Locals.
Require Import Sets.
Require Import Syntax.
Require Import SemanticsExpr.
Require Import Dict.

Set Implicit Arguments.

Record ADT := {
  DataType : Set;
  Value : DataType;
  Methods : string -> option (DataType -> list W -> DataType -> W -> Prop)
}.

Definition ADTs := W -> option ADT.

Definition st := (vals * ADTs)%type.

Record callTransition := {
  Args : list W;
  Ret : W;
  InitialHeap : ADTs;
  FinalHeap : ADTs
}.

Inductive Callee := 
  | Foreign : (callTransition -> Prop) -> Callee
  | Internal : Statement -> Callee.

Definition upd_option vs var value :=
  match var with
    | None => vs
    | Some x => Locals.upd vs x value
  end.

Definition set_value adt value := {| DataType := DataType adt; Value := value; Methods := Methods adt |}.

Definition upd A (m : W -> A) k v k' :=
  if weq k' k then v else m k'.

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
  | CallForeign : forall vs adts var f args spec ret adts',
      let v := (vs, adts) in
      let args_v := map (fun e => exprDenote e vs) args in
      functions (exprDenote f vs) = Some (Foreign spec)
      -> spec {| Args := args_v; Ret := ret; InitialHeap := adts; FinalHeap := adts' |}
      -> RunsTo (Syntax.Call var f args) v (upd_option vs var ret, adts')
  | CallInternal : forall vs adts f adts' body arg vs_arg vs',
      let v := (vs, adts) in
      let arg_v := exprDenote arg vs in
      functions (exprDenote f vs) = Some (Internal body)
      -> Locals.sel vs_arg "__arg" = arg_v
      -> RunsTo body (vs_arg, adts) (vs', adts')
      -> RunsTo (Syntax.Call None f (arg :: nil)) v (vs, adts')
  | CallMethod : forall vs adts var obj f args obj_adt spec new_value ret,
      let v := (vs, adts) in
      let args_v := map (fun e => exprDenote e vs) args in
      let obj_v := exprDenote obj vs in
      adts obj_v = Some obj_adt
      -> Methods obj_adt f = Some spec
      -> spec (Value obj_adt) args_v new_value ret
      -> RunsTo (Syntax.CallMethod var obj f args) v (upd_option vs var ret, upd adts obj_v (Some (set_value obj_adt new_value))).

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
  | CallForeign : forall vs adts f arg spec adts',
      let arg_v := exprDenote arg vs in
      functions (exprDenote f vs) = Some (Foreign spec)
      -> spec {| Arg := arg_v; InitialHeap := adts; FinalHeap := adts' |}
      -> Safe (Syntax.Call f arg) (vs, adts)
  | CallInternal : forall vs adts f arg body,
      let arg_v := exprDenote arg vs in
      functions (exprDenote f vs) = Some (Internal body)
      -> (forall vs_arg, Locals.sel vs_arg "__arg" = arg_v -> Safe body (vs_arg, adts))
      -> Safe (Syntax.Call f arg) (vs, adts).

  | ReadAt : forall var arr idx vs (adts : arrays),
      let v := (vs, adts) in
      let arr_v := exprDenote arr vs in
      let idx_v := exprDenote idx vs in
      safe_access adts arr_v idx_v -> 
      Safe (Syntax.ReadAt var arr idx) v
  | WriteAt : forall arr idx value vs (adts : arrays), 
      let v := (vs, adts) in
      let arr_v := exprDenote arr vs in
      let idx_v := exprDenote idx vs in
      safe_access adts arr_v idx_v ->
      Safe (Syntax.WriteAt arr idx value) v
  | Malloc : forall var size vs (adts : arrays),
      let size_v := exprDenote size vs in
      goodSize (wordToNat size_v + 2) ->
      Safe (Syntax.Malloc var size) (vs, adts)
  | Free : forall arr vs (adts : arrays),
      let arr_v := exprDenote arr vs in
      arr_v %in fst adts ->
      Safe (Syntax.Free arr) (vs, adts)
  | Len : forall var arr vs (adts : arrays),
      let arr_v := exprDenote arr vs in
      arr_v %in fst adts ->
      Safe (Syntax.Len var arr) (vs, adts)

End functions'.


End Safety.
