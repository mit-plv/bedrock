Require Import IL Memory String Word Locals.
Require Import Sets.
Require Import Syntax.
Require Import SemanticsExpr.
Require Import Dict.

Set Implicit Arguments.

Module WKey : S with Definition A := W.

  Definition A := W.
  
  Definition eq_dec := @weq 32.

End WKey.

Module StoKEY (MKey : S) : KEY with Definition key := MKey.A.

  Definition key := MKey.A.

  Definition eq_dec := MKey.eq_dec.

End StoKEY.

Module WMake := Make WKey.

Import WMake.

Module WKey2 := StoKEY WKey.

Module ListWData : DATA with Definition data := list W.

  Definition data := list W.

End ListWData.

Module WDict := Dict.Dict WKey2 ListWData.

Import WDict.

Definition arrays := (set * dict)%type.

Definition st := (vals * arrays)%type.

Definition safe_access (arrs : arrays) (arr_v idx_v : W) :=       
  arr_v %in fst arrs /\
  idx_v < natToW (length (snd arrs arr_v)).

Fixpoint init_list A (value : A) size :=
  match size with
    | 0 => nil
    | S n => value :: init_list value n
  end.

(* Semantics *)

Record callTransition := {
  Arg : W;
  InitialHeap : arrays;
  FinalHeap : arrays
}.

Inductive Callee := 
  | Foreign : (W -> arrays -> Prop) -> (callTransition -> Prop) -> Callee
  | Internal : Statement -> Callee.

Section functions.
Variable functions : W -> option Callee.
(* Map foreign function addresses to specifications. *)

Inductive RunsTo : Statement -> st -> st -> Prop :=
  | Assignment : forall var value vs arrs, 
      let v := (vs, arrs) in
      let value_v := exprDenote value vs in
      RunsTo (Syntax.Assignment var value) v (Locals.upd vs var value_v, arrs)
  | ReadAt : forall var arr idx vs (arrs : arrays),
      let v := (vs, arrs) in
      let arr_v := exprDenote arr vs in
      let idx_v := exprDenote idx vs in
      safe_access arrs arr_v idx_v -> 
      let value_v := Array.sel (snd arrs arr_v) idx_v in  
      RunsTo (Syntax.ReadAt var arr idx) v (Locals.upd vs var value_v, arrs)
  | WriteAt : forall arr idx value vs (arrs : arrays), 
      let v := (vs, arrs) in
      let arr_v := exprDenote arr vs in
      let idx_v := exprDenote idx vs in
      safe_access arrs arr_v idx_v ->
      let value_v := exprDenote value vs in
      let new_arr := Array.upd (snd arrs arr_v) idx_v value_v in
      RunsTo (Syntax.WriteAt arr idx value) v (vs, (fst arrs, upd (snd arrs) arr_v new_arr))
  | Seq : forall v v' v'' a b,
      RunsTo a v v' -> 
      RunsTo b v' v'' -> 
      RunsTo (Syntax.Seq a b) v v''
  | Skip : forall v, RunsTo Syntax.Skip v v
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
  | Malloc : forall var size vs arrs addr ls,
      let v := (vs, arrs) in
      ~ (addr %in fst arrs) ->
      let size_v := wordToNat (exprDenote size vs) in
      goodSize (size_v + 2) ->
      length ls = size_v ->
      RunsTo (Syntax.Malloc var size) v (Locals.upd vs var addr, (fst arrs %+ addr, upd (snd arrs) addr ls))
  | Free : forall arr vs (arrs : arrays),
      let v := (vs, arrs) in
      let arr_v := exprDenote arr vs in
      arr_v %in fst arrs ->
      RunsTo (Syntax.Free arr) v (vs, (fst arrs %- arr_v, snd arrs))
  | Len : forall var arr vs arrs,
      let v := (vs, arrs) in
      let arr_v := exprDenote arr vs in
      arr_v %in fst arrs ->
      let len := natToW (length (snd arrs arr_v)) in
      RunsTo (Syntax.Len var arr) v (Locals.upd vs var len, arrs)
  | CallForeign : forall vs arrs f arrs' precond spec arg,
      let v := (vs, arrs) in
      let arg_v := exprDenote arg vs in
      functions (exprDenote f vs) = Some (Foreign precond spec)
      -> precond arg_v arrs
      -> spec {| Arg := arg_v; InitialHeap := arrs; FinalHeap := arrs' |}
      -> RunsTo (Syntax.Call f arg) v (vs, arrs')
  | CallInternal : forall vs arrs f arrs' body arg vs_arg vs',
      let v := (vs, arrs) in
      let arg_v := exprDenote arg vs in
      functions (exprDenote f vs) = Some (Internal body)
      -> Locals.sel vs_arg "__arg" = arg_v
      -> RunsTo body (vs_arg, arrs) (vs', arrs')
      -> RunsTo (Syntax.Call f arg) v (vs, arrs').

End functions.

Module Safety.

Section functions'.
Variable functions : W -> option Callee.

CoInductive Safe : Statement -> st -> Prop :=
  | Seq : forall a b v, 
      Safe a v ->
      (forall v', RunsTo functions a v v' -> Safe b v') -> 
      Safe (Syntax.Seq a b) v
  | LoopTrue : forall v cond body, 
      let statement := Loop cond body in
      wneb (exprDenote cond (fst v)) $0 = true -> 
      Safe body v ->
      (forall v', RunsTo functions body v v' -> Safe statement v') -> 
      Safe statement v
  | LoopFalse : forall v cond body, 
      wneb (exprDenote cond (fst v)) $0 = false -> 
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
    Variable R : Statement -> st -> Prop.

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

End functions'.


End Safety.
