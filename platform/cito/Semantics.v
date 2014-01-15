Require Import Syntax SemanticsExpr.
Require Import IL Memory String Word Locals List.
Require Import Label.

Set Implicit Arguments.

Record ADT := 
  {
    Model : Type
  }.

Record ADTValue := 
  {
    Type_ : ADT;
    Value : Model Type_
  }.
                    
Variable Heap : Type.

Variable heap_sel : Heap -> W -> option ADTValue.

Variable heap_mem : W -> Heap -> Prop.

Variable heap_upd : Heap -> W -> ADTValue -> Heap.

Variable heap_remove : Heap -> W -> Heap.

Variable heap_empty : Heap.

Variable heap_merge : Heap -> Heap -> Heap.

Variable heap_elements : Heap -> list (W * ADTValue).

Variable heap_diff : Heap -> Heap -> Heap.

Definition State := (vals * Heap)%type.

Definition ArgIn := (W + ADTValue)%type.

Definition ArgOut := option ADTValue.

Definition Ret := (W + ADTValue)%type.

Record ForeignFuncSpec := 
  {
    PreCond: list ArgIn -> Prop;
    PostCond : list (ArgIn * ArgOut) -> Ret -> Prop
  }.

Require Import FuncCore.
Export FuncCore.
Record InternalFuncSpec := 
  {
    Fun : FuncCore;
    NoDupArgVars : NoDup (ArgVars Fun)
  }.

Coercion Fun : InternalFuncSpec >-> FuncCore.

Inductive Callee := 
  | Foreign : ForeignFuncSpec -> Callee
  | Internal : InternalFuncSpec -> Callee.

Definition word_adt_match (heap : Heap) p :=
  let word := fst p in
  let in_ := snd p in
  match in_ with
    | inl w => word = w
    | inr a => heap_sel heap word = Some a
  end.

Definition is_adt (a : ArgIn) :=
  match a with
    | inl _ => false
    | inr _ => true
  end.

Definition disjoint_ptrs (pairs : list (W * ArgIn)) := 
  let pairs := filter (fun p => is_adt (snd p)) pairs in
  NoDup (map fst pairs).

Definition good_inputs heap pairs := 
  Forall (word_adt_match heap) pairs /\
  disjoint_ptrs pairs.

Record ArgTriple :=
  {
    Word : W;
    ADTIn : ArgIn;
    ADTOut : ArgOut
  }.

Fixpoint store_out (heap : Heap) t :=
  match ADTIn t, ADTOut t with 
    | inl _, _ => heap
    | inr _, None => heap_remove heap (Word t)
    | inr _, Some a => heap_upd heap (Word t) a
  end.

Definition decide_ret addr (ret : Ret) :=
  match ret with
    | inl w => (w, None)
    | inr a => (addr, Some a)
  end.

Definition separated heap ret_w (ret_a : option ADTValue) := 
  ret_a = None \/ ~ heap_mem ret_w heap.

Definition heap_upd_option m k v :=
  match v with
    | Some x => heap_upd m k x
    | None => m
  end.

Definition upd_option vs x value :=
  match x with
    | None => vs
    | Some s => Locals.upd vs s value
  end.

(* Semantics *)

Section Env.

  Variable env : (label -> option W) * (W -> option Callee).

  Inductive RunsTo : Stmt -> State -> State -> Prop :=
  | Skip : forall v, RunsTo Syntax.Skip v v
  | Seq : 
      forall a b v v' v'',
        RunsTo a v v' -> 
        RunsTo b v' v'' -> 
        RunsTo (Syntax.Seq a b) v v''
  | If : 
      forall cond t f v v', 
        let b := wneb (eval (fst v) cond) $0 in
        b = true /\ RunsTo t v v' \/ b = false /\ RunsTo f v v' ->
        RunsTo (Syntax.If cond t f) v v'
  | While : 
      forall cond body v v', 
        let loop := While cond body in
        RunsTo (Syntax.If cond (Syntax.Seq body loop) Syntax.Skip) v v' ->
        RunsTo loop v v'
  | CallInternal : 
      forall var f args v spec vs_callee vs_callee' heap',
        let vs := fst v in
        let heap := snd v in
        let fs := snd env in
        fs (eval vs f) = Some (Internal spec) ->
        map (Locals.sel vs_callee) (ArgVars spec) = map (eval vs) args ->
        RunsTo (Body spec) (vs_callee, heap) (vs_callee', heap') ->
        let vs := upd_option vs var (Locals.sel vs_callee' (RetVar spec)) in
        let heap := heap' in
        RunsTo (Syntax.Call var f args) v (vs, heap)
  | CallForeign : 
      forall var f args v spec triples addr ret,
        let vs := fst v in
        let heap := snd v in
        let fs := snd env in
        fs (eval vs f) = Some (Foreign spec) ->
        map (eval vs) args = map Word triples ->
        good_inputs heap (map (fun x => (Word x, ADTIn x)) triples) ->
        PreCond spec (map ADTIn triples) ->
        PostCond spec (map (fun x => (ADTIn x, ADTOut x)) triples) ret ->
        let heap := fold_left store_out triples heap in
        let t := decide_ret addr ret in
        let ret_w := fst t in
        let ret_a := snd t in
        separated heap ret_w ret_a ->
        let heap := heap_upd_option heap ret_w ret_a in
        let vs := upd_option vs var ret_w in
        RunsTo (Syntax.Call var f args) v (vs, heap)
  | Label : 
      forall x lbl v w,
        fst env lbl = Some w ->
        RunsTo (Syntax.Label x lbl) v (Locals.upd (fst v) x w, snd v)
  | Assign :
      forall x e v,
        let vs := fst v in
        RunsTo (Syntax.Assign x e) v (Locals.upd vs x (eval vs e), snd v).

End Env.