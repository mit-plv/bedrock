Require Import List.
Require Import Expr.
Require Import SepTheory PropX.
Require Import IL.

Set Implicit Arguments.

Module SepExpr (B : SepLog).
  Module L := Make B.  

  Section env.

    Variable types : list type.
    Variable funcs : functions types.

    Variable pcType : tvar types.    
    Variable stateType : tvar types.
    Variable stateMem : tvarD stateType -> L.mem.

    Record ssignature := {
      SDomain : list (tvar types) ;
      SDenotation : functionTypeD (map (@tvarD types) SDomain) (L.smem -> PropX (tvarD pcType) (tvarD stateType))
    }.
    Variable sfuncs : list ssignature.

    Inductive sexpr : variables types -> Type :=
    | Inj : forall vars, expr funcs vars None -> sexpr vars
    | Star : forall vars, sexpr vars -> sexpr vars -> sexpr vars
    | Exists : forall vars t, sexpr (t :: vars) -> sexpr vars
    | Cptr : forall vars, expr funcs vars pcType -> sexpr (stateType :: vars) -> sexpr vars
    | Func : forall vars (f : fin sfuncs), 
      hlist (expr funcs vars) (SDomain (get sfuncs f)) -> sexpr vars
    | Const : forall vars, 
      PropX (tvarD pcType) (tvarD stateType) -> sexpr vars
    (** PtsTo should be derived, that way we can handle different sizes easily, 
     ** baking it in allows us to derive <> facts from points to 
     **)
      .

    Fixpoint sexprD (vars : variables types) (s : sexpr vars)
      : hlist (@tvarD types)  vars -> L.smem -> PropX (tvarD pcType) (tvarD stateType) :=
      match s in sexpr vars return hlist (@tvarD types) vars -> L.smem -> PropX (tvarD pcType) (tvarD stateType) with
        | Inj _ p => fun g _ => PropX.Inj (exprD g p)
        | Exists _ t b => fun g m => PropX.Exists (fun x : tvarD t => sexprD b (HCons x g) m)
        | Func _ f b => fun g =>
          applyD (exprD g) b _ (SDenotation (get sfuncs f))
        | Const _ p => fun _ _ => p
        | Star _ l r => fun g m => 
          PropX.Exists (fun ml : L.smem => PropX.Exists (fun mr : L.smem => 
            PropX.And (PropX.Inj (L.split m ml mr)) (And (sexprD l g ml) (sexprD l g mr))))
        | Cptr _ p t => fun g m =>
          PropX.Cptr (exprD g p) 
          (fun x : tvarD stateType => PropX.Exists (fun m => 
            PropX.And (PropX.Inj (L.satisfies m (stateMem x))) (sexprD t (HCons x g) m)))
      end.

  End env.

End SepExpr.
