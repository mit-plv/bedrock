Require Import List.
Require Import Bedrock.ndep.Expr.
Require Import Heaps SepTheoryX PropX.
Require Import PropXTac.
Require Import PMap.
Require Import RelationClasses.
Require Import EqdepClass.

Set Implicit Arguments.

Module SepExpr (B : Heap) (ST : SepTheoryX.SepTheoryXType B).

  Section env.
    Variable types : list type.
    Variable funcs : functions types.

    Variable pcType : tvar.
    Variable stateType : tvar.
    Variable stateMem : tvarD types stateType -> B.mem.

    Record ssignature := {
      SDomain : list tvar ;
      SDenotation : functionTypeD (map (@tvarD types) SDomain) 
        (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.
    Variable sfuncs : list ssignature.

    Inductive sexpr : Type :=
    | Emp : sexpr
    | Inj : expr types -> sexpr
    | Star : sexpr -> sexpr -> sexpr
    | Exists : tvar -> sexpr -> sexpr
    | Func : func -> list (expr types) -> sexpr
      (* this Const can not mention the higher-order variables *)
    | Const : ST.hprop (tvarD types pcType) (tvarD types stateType) nil
      -> sexpr
    .

    Fixpoint sexprD (s : sexpr) (uvs vs : list { t : tvar & tvarD types t })
      : option (ST.hprop (tvarD types pcType) (tvarD types stateType) nil) :=
    match s with 
      | Emp => 
        Some (ST.emp _ _)
      | Inj p =>
        match exprD funcs uvs vs p tvProp with
          | None => None
          | Some p => 
            Some (ST.inj (PropX.Inj p))
        end
      | Star l r =>
        match sexprD l uvs vs , sexprD r uvs vs with
          | Some l , Some r =>
            Some (ST.star l r)
          | _ , _ => None
        end                    
      | Exists t b =>
        Some (ST.ex (fun x : tvarD types t =>
          match sexprD b uvs (@existT _ _ t x :: vs) with
            | None => ST.inj (PropX.Inj False)
            | Some s => s
          end))
      | Func f b =>
        match nth_error sfuncs f with
          | None => None
          | Some f =>
            applyD (@exprD types funcs uvs vs) (SDomain f) b _ (SDenotation f)
        end
      | Const p => Some p
    end.

  End env.

End SepExpr.