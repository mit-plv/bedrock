Require Import Syntax SemanticsExpr.
Require Import IL Memory String Word Locals List.

Set Implicit Arguments.

Record ADT := 
  {
    Model : Set
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

Definition State := (vals * Heap)%type.

Definition ArgIn := (W + ADTValue)%type.

Definition ArgOut := option ADTValue.

Definition Ret := (W + ADTValue)%type.

Record ForeignFuncSpec := 
  {
    PreCond: list ArgIn -> Prop;
    PostCond : list (ArgIn * ArgOut) -> Ret -> Prop
  }.

Record InternalFuncSpec := 
  {
    ArgVars : list string;
    RetVar : string;
    Body : Stmt
  }.

Inductive Callee := 
  | Foreign : ForeignFuncSpec -> Callee
  | Internal : InternalFuncSpec -> Callee.

Definition heap_match (heap : Heap) p :=
  let ptr := fst p in
  let in_ := snd p in
  match in_ with
    | inl w => ptr = w
    | inr a => heap_sel heap ptr = Some a
  end.

Record ArgTriple :=
  {
    Ptr : W;
    In : ArgIn;
    Out : ArgOut
  }.

Definition satisfy_foreign spec args v triples ret :=
  let vs := fst v in
  let heap := snd v in
  map (eval vs) args = map Ptr triples /\
  Forall (fun x => heap_match heap (Ptr x, In x)) triples /\
  PreCond spec (map In triples) /\
  PostCond spec (map (fun x => (In x, Out x)) triples) ret.

Fixpoint store_out (heap : Heap) t :=
  match In t, Out t with 
    | inl _, _ => heap
    | inr _, None => heap_remove heap (Ptr t)
    | inr _, Some a => heap_upd heap (Ptr t) a
  end.

Definition upd_option vs x value :=
  match x with
    | None => vs
    | Some s => Locals.upd vs s value
  end.

(* Semantics *)

Section fs.

  (* Map foreign function addresses to specifications. *)
  Variable fs : W -> option Callee.

  Inductive RunsTo : Stmt -> State -> State -> Prop :=
  | Skip : forall v, RunsTo Syntax.Skip v v
  | Seq : 
      forall a b v v' v'',
        RunsTo a v v' -> 
        RunsTo b v' v'' -> 
        RunsTo (Syntax.Seq a b) v v''
  | IfTrue : 
      forall cond t f v v', 
        wneb (eval (fst v) cond) $0 = true -> 
        RunsTo t v v' -> 
        RunsTo (Syntax.If cond t f) v v'
  | IfFalse : 
      forall cond t f v v', 
        wneb (eval (fst v) cond) $0 = false -> 
        RunsTo f v v' -> 
        RunsTo (Syntax.If cond t f) v v'
  | WhileTrue : 
      forall cond body v v' v'', 
        let statement := While cond body in
        wneb (eval (fst v) cond) $0 = true -> 
        RunsTo body v v' -> 
        RunsTo statement v' v'' -> 
        RunsTo statement v v''
  | WhileFalse : 
      forall cond body v, 
        wneb (eval (fst v) cond) $0 = false -> 
        RunsTo (While cond body) v v
  | CallInternal : 
      forall var f args v spec vs_callee vs_callee' heap',
        let vs := fst v in
        let heap := snd v in
        fs (eval vs f) = Some (Internal spec) ->
        map (Locals.sel vs_callee) (ArgVars spec) = map (eval vs) args ->
        RunsTo (Body spec) (vs_callee, heap) (vs_callee', heap') ->
        let vs := upd_option vs var (Locals.sel vs_callee' (RetVar spec)) in
        let heap := heap' in
        RunsTo (Syntax.Call var f args) v (vs, heap)
  | CallForeign1 : 
      forall var f args v spec triples ret_w,
        let vs := fst v in
        let heap := snd v in
        fs (eval vs f) = Some (Foreign spec) ->
        satisfy_foreign spec args v triples (inl ret_w) ->
        let vs := upd_option vs var ret_w in
        let heap := fold_left store_out triples heap in
        RunsTo (Syntax.Call var f args) v (vs, heap)
  | CallForeign2 : 
      forall var f args v spec triples addr ret_a,
        let vs := fst v in
        let heap := snd v in
        fs (eval vs f) = Some (Foreign spec) ->
        satisfy_foreign spec args v triples (inr ret_a) ->
        ~ heap_mem addr heap ->
        let vs := upd_option vs var addr in
        let heap := fold_left store_out triples heap in
        let heap := heap_upd heap addr ret_a in
        RunsTo (Syntax.Call var f args) v (vs, heap).

End fs.