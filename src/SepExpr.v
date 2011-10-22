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
      (** TODO: This const case doesn't work because there is no (reasonable) semi-decidable equality on propX **)
    | Const : forall vars, 
      PropX (tvarD pcType) (tvarD stateType) -> sexpr vars
    (** PtsTo should be derived, that way we can handle different sizes easily, 
     ** baking it in allows us to derive <> facts from points to 
     **)
      .
    (** NOTE: If I want to be able to reflect arbitrary propX terms (ExistsX,ForallX), then I'm going to need
     ** another index on sexpr to express the (type -> PropX)
     **)


    Fixpoint sexprD (vars : variables types) (s : sexpr vars)
      : hlist (@tvarD types)  vars -> L.smem -> PropX (tvarD pcType) (tvarD stateType) :=
      match s in sexpr vars return hlist (@tvarD types) vars -> L.smem -> PropX (tvarD pcType) (tvarD stateType) with
        | Inj _ p => fun g _ => PropX.Inj (exprD g p)
        | Exists _ t b => fun g m => PropX.Exists (fun x : tvarD t => @sexprD _ b (HCons x g) m)
        | Func _ f b => fun g =>
          applyD (exprD g) b _ (SDenotation (get sfuncs f))
        | Const _ p => fun g _ => p
        | Star _ l r => fun g m => 
          PropX.Exists (fun ml : L.smem => PropX.Exists (fun mr : L.smem => 
            PropX.And (PropX.Inj (L.split m ml mr)) (And (sexprD l g ml) (sexprD l g mr))))
        | Cptr _ p t => fun g m =>
          PropX.Cptr (exprD g p) 
          (fun x : tvarD stateType => PropX.Exists (fun m => 
            PropX.And (PropX.Inj (L.satisfies m (stateMem x))) (sexprD t (HCons x g) m)))
      end.

    Section Eq.
      Definition sexprEq vars (a : sexpr vars) : forall b, option (a = b).
        refine ((fix sexprEq vars (a : sexpr vars) {struct a} : forall b, option (a = b) :=
          match a in sexpr vars return forall b : sexpr vars, option (a = b) with
            | Inj v l => fun b =>
              match b in sexpr v' return forall l : expr funcs v' None, option (Inj l = b) with
                | Inj _ r => fun l => match exprEq l r with
                                        | Some pf => Some _
                                        | None => None
                                      end                  
                | _ => fun _ => None
              end l
            | Star v ll lr => fun b =>
              match b in sexpr v' 
                return forall (Heq : v' = v), (forall (x y : sexpr v'), option (Star ll lr = (match Heq in _ = t 
                                                                                                return sexpr t
                                                                                                with
                                                                                                | refl_equal => Star x y
                                                                                              end))
                ) -> option (Star ll lr = match Heq in _ = t return sexpr t with
                                            | refl_equal => b
                                          end)
                with
                | Star _ rl rr => fun _ cc => cc rl rr
                | _ => fun _ _ => None
              end (refl_equal _)
              (fun (x y : sexpr v) =>
                match sexprEq _ ll x , sexprEq _ lr y with
                  | Some _ , Some _ => Some _
                  | _ , _ => None
                end)
            | Exists v t body => fun b =>
              match b in sexpr v' 
                return forall (Heq : v' = v),
                  (forall t' (x : sexpr (t' :: v')), t' = t -> option (Exists body = match Heq in _ = t 
                                                                                       return sexpr t 
                                                                                       with
                                                                                       | refl_equal => Exists x
                                                                                     end)) ->
                  option (Exists body = match Heq in _ = t return sexpr t with
                                          | refl_equal => b
                                        end)
                with
                | Exists v' t' b' => fun Heq cc =>
                  match tvar_dec t' t with
                    | left pf => cc _ _ _
                    | right _ => None
                  end
                | _ => fun _ _ => None
              end (refl_equal _)
              (fun t x eqq => 
                match sexprEq _ body match eqq in _ = t' return sexpr (t' :: v) with
                                       | refl_equal => x
                                     end
                  with
                  | Some _ => Some _
                  | None => None
                end)
            | Cptr v lp ls => fun b =>
              match b in sexpr v' 
                return forall (Heq : v' = v), 
                  (forall (p : expr funcs v' pcType) (s : sexpr (stateType :: v')), option (Cptr lp ls = match Heq in _ = t
                                                                                                           return sexpr t
                                                                                                           with 
                                                                                                           | refl_equal => Cptr p s
                                                                                                         end)) ->
                option (Cptr lp ls = match Heq in _ = t return sexpr t with
                                       | refl_equal => b
                                     end)
                with
                | Cptr _ rp rs => fun _ cc => cc rp rs
                | _ => fun _ _ => None
              end (refl_equal _)
              (fun x y =>
                match exprEq lp x , sexprEq _ ls y with
                  | Some _ , Some _ => Some _
                  | _ , _ => None
                end)
            | Func v f args => fun b =>
              match b in sexpr v'
                return forall (Heq : v' = v), 
                  (forall args', option (args = args')) ->
                  option (Func f args = match Heq in _ = t 
                                          return sexpr t
                                          with
                                          | refl_equal => b
                                        end)
                with
                | Func v' f' args' => fun Heq cc => 
                  match finEq f f' with
                    | left pf => match cc match Heq in _ = t 
                                            return hlist (expr funcs t) (SDomain (get sfuncs f))
                                            with 
                                            | refl_equal => match sym_eq pf in _ = t 
                                                              return hlist (expr funcs v') (SDomain (get sfuncs t)) with
                                                              | refl_equal => args'
                                                            end
                                          end
                                   with
                                   | Some _ => Some _
                                   | None => None
                                 end                                     
                    | right _ => None 
                  end
                | _ => fun _ _ => None
              end (refl_equal _) (hlistEq (@exprEq _ _ _) args)
            | Const _ _ => fun _ => None
              (** TODO: Problem with Const **)
          end) vars a);
        clear sexprEq; try abstract (subst; reflexivity).
      Defined.
    End Eq.

    Definition Himp (cs : codeSpec (tvarD pcType) (tvarD stateType)) (gl gr : sexpr nil) 
(*      : PropX (tvarD pcType) (tvarD stateType) := *)
      : Prop :=
      L.himp (fun m => valid cs nil (sexprD gl HNil m)) (fun m => valid cs nil (sexprD gr HNil m)).

  End env.

  Section SProver.
    Variable types : list type.
    Variable funcs : functions types.
    Variable pcType : tvar types.    
    Variable stateType : tvar types.
    Variable stateMem : tvarD stateType -> L.mem.
    Variable sfuncs : list (ssignature pcType stateType).
    
    (** TODO: it looks like I need this in terms of PropX? **)
    Definition SProverT : Type := forall
      (cs : codeSpec (tvarD pcType) (tvarD stateType))
      (hyps : list (@Qexpr types funcs)) (** Guards **)
      (gl gr : @sexpr types funcs pcType stateType sfuncs nil), 
      option (Himp stateMem cs gl gr).

  End SProver.

  Section BabySep.
    Variable types : list type.
    Variable fs : functions types.
    Variable pcType : tvar types.    
    Variable stateType : tvar types.
    Variable stateMem : tvarD stateType -> L.mem.
    Variable sfuncs : list (ssignature pcType stateType).

    Definition BabySep : @SProverT types fs pcType stateType stateMem sfuncs.
    red.
    refine (fun _ _ gl gr =>
      if sexprEq gl gr then 
        Some _ 
      else 
        None).
    subst. unfold Himp. unfold L.himp. intros. auto.
  Defined.
  End BabySep.

  Section QSexpr.
    (** Guarded separation logic expressions **)
  End QSexpr.
    

End SepExpr.
