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

    Variable consts : list (PropX (tvarD pcType) (tvarD stateType)).

    Inductive sexpr : variables types -> Type :=
    | Emp : forall vars, sexpr vars
    | Inj : forall vars, expr funcs vars None -> sexpr vars
    | Star : forall vars, sexpr vars -> sexpr vars -> sexpr vars
    | Exists : forall vars t, sexpr (t :: vars) -> sexpr vars
    | Cptr : forall vars, expr funcs vars pcType -> sexpr (stateType :: vars) -> sexpr vars
    | Func : forall vars (f : fin sfuncs), 
      hlist (expr funcs vars) (SDomain (get sfuncs f)) -> sexpr vars
    | Const : forall vars, fin consts -> sexpr vars
    (** If PtsTo is derived: we can handle different sizes easily, 
     ** If PtsTo is built-in: we can derive <> facts easily (also precision)
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
        | Const _ p => fun _ _ => (*p*)
          get consts p
        | Star _ l r => fun g m => 
          PropX.Exists (fun ml : L.smem => PropX.Exists (fun mr : L.smem => 
            PropX.And (PropX.Inj (L.split m ml mr)) (And (sexprD l g ml) (sexprD r g mr))))
        | Emp _ => fun _ m => 
          PropX.Inj (L.semp m)
        | Cptr _ p t => fun g m =>
          PropX.Cptr (exprD g p) 
          (fun x : tvarD stateType => PropX.Exists (fun m => 
            PropX.And (PropX.Inj (L.satisfies m (stateMem x))) (sexprD t (HCons x g) m)))
      end.

    Section Eq.
      Definition sexprEq vars (a : sexpr vars) : forall b, option (a = b).
        refine ((fix sexprEq vars (a : sexpr vars) {struct a} : forall b, option (a = b) :=
          match a in sexpr vars return forall b : sexpr vars, option (a = b) with
            | Emp _ => fun b =>
              match b with
                | Emp _ => Some _ 
                | _ => None
              end
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
            | Const _ x => fun b => 
              match b with
                | Const _ y => if finEq x y then Some _ else None
                | _ => None
              end
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
    Variable consts : list (PropX (tvarD pcType) (tvarD stateType)).
    
    (** TODO: it looks like I need this in terms of PropX? **)
    Definition SProverT : Type := forall
      (cs : codeSpec (tvarD pcType) (tvarD stateType))
      (hyps : list (@Qexpr types funcs)) (** Guards **)
      (gl gr : @sexpr types funcs pcType stateType sfuncs consts nil), 
      option (Himp stateMem cs gl gr).

  End SProver.

  Section BabySep.
    Variable types : list type.
    Variable fs : functions types.
    Variable pcType : tvar types.    
    Variable stateType : tvar types.
    Variable stateMem : tvarD stateType -> L.mem.
    Variable sfuncs : list (ssignature pcType stateType).
    Variable consts : list (PropX (tvarD pcType) (tvarD stateType)).

    Definition ReflSep : @SProverT types fs pcType stateType stateMem sfuncs consts.
    red. refine (fun _ _ gl gr =>
      if sexprEq gl gr then 
        Some _ 
      else 
        None).
    subst. unfold Himp. unfold L.himp. intros. auto.
    Defined.

    Parameter dmap : forall (K : Type) (V : K -> Type), Type.
    Parameter map : Type -> Type -> Type.

    Parameter dmap_empty : forall K V, @dmap K V.
    Parameter dmap_fold : forall {A} {K} {V} (f : A -> forall k, V k -> A) (a : A) (m : @dmap K V), A.
    Parameter dmap_insert : forall {K} {V} k, V k -> @dmap K V -> dmap V.
    Parameter dmap_join : forall {K} {V}, @dmap K V -> dmap V -> dmap V.
    Parameter map_empty : forall K V, map K V.
    Parameter map_fold : forall {A} {K} {V} (f : A -> K -> V -> A) (a : A) (m : map K V), A.
    Parameter map_insert : forall {K} {V}, K -> V -> @map K V -> map K V.
    Parameter map_join : forall {K} {V}, map K V -> @map K V -> map K V.

    Parameter dmap_fold_empty : forall A K V f (a : A), dmap_fold f a (@dmap_empty K V) = a.
    Parameter map_fold_empty : forall A K V f (a : A), map_fold f a (@map_empty K V) = a.

    Record SHeap vars : Type :=
    { funcs  : @dmap (fin sfuncs) (fun f => hlist (expr fs vars) (SDomain (get sfuncs f)))
    ; cptrs  : map (expr fs vars pcType) (sexpr fs sfuncs consts (stateType :: vars))
    ; pures  : list (expr fs vars None)
    ; cnsts  : list (fin consts)
    ; other  : list (sexpr fs sfuncs consts vars)
    }.

    Definition denote vars (h : SHeap vars) :  sexpr fs sfuncs consts vars :=
      let acc := Emp _ _ _ _ in
      let acc := dmap_fold (fun a x y => Star a (Func _ x y)) acc (funcs h) in
      let acc := map_fold (fun a x y => Star a (Cptr x y)) acc (cptrs h) in
      let acc := fold_left (fun a x => Star a (Inj _ _ x)) (pures h) acc in
      let acc := fold_left (fun a x => Star a (Const _ _ _ x)) (cnsts h) acc in
      fold_left (fun a x => Star a x) (other h) acc.

    Fixpoint hash vars (s : sexpr fs sfuncs consts vars) : SHeap vars :=
      match s in @sexpr _ _ _ _ _ _ vs return SHeap vs with
        | Inj _ p => 
          {| funcs := dmap_empty _
           ; cptrs := map_empty _ _
           ; pures := p :: nil
           ; cnsts := nil
           ; other := nil
           |}
        | Star _ l r => 
          let ll := hash l in
          let rr := hash r in
          {| funcs := dmap_join (funcs ll) (funcs rr)
           ; cptrs := map_join (cptrs ll) (cptrs rr)
           ; pures := pures ll ++ pures rr
           ; cnsts := cnsts ll ++ cnsts rr
           ; other := other ll ++ other rr 
          |}
        | Func _ f args => 
          {| funcs := dmap_insert f args (dmap_empty _)
           ; cptrs := map_empty _ _ 
           ; pures := nil
           ; cnsts := nil
           ; other := nil
          |}
        | Cptr _ p s => 
          {| funcs := dmap_empty _
           ; cptrs := map_insert p s (map_empty _ _)
           ; pures := nil
           ; cnsts := nil
           ; other := nil
          |}
        | Emp _ => 
          {| funcs := dmap_empty _
           ; cptrs := map_empty _ _
           ; pures := nil
           ; cnsts := nil
           ; other := nil
           |}
        | Const _ c =>
          {| funcs := dmap_empty _
           ; cptrs := map_empty _ _ 
           ; pures := nil
           ; cnsts := c :: nil
           ; other := nil
          |}
        | x => 
          (** TODO : Other cases are problematic... **)
          {| funcs := dmap_empty _ ; cptrs := map_empty _ _ ; pures := nil ; cnsts := nil ; other := x :: nil |}
      end.

(*
    Fixpoint hash_cc T vars (s : sexpr fs sfuncs consts vars) 
      :  @dmap (fin sfuncs) (fun f => hlist (expr fs vars) (SDomain (get sfuncs f))) 
      -> map (expr fs vars pcType) (sexpr fs sfuncs consts (stateType :: vars))
      -> list (expr fs vars None)
      -> (   @dmap (fin sfuncs) (fun f => hlist (expr fs vars) (SDomain (get sfuncs f))) 
          -> map (expr fs vars pcType) (sexpr fs sfuncs consts (stateType :: vars))
          -> list (expr fs vars None)-> T) -> T :=
      match s in @sexpr _ _ _ _ _ _ vs 
        return @dmap (fin sfuncs) (fun f => hlist (expr fs vs) (SDomain (get sfuncs f))) 
        -> map (expr fs vs pcType) (sexpr fs sfuncs consts (stateType :: vs))
        -> list (expr fs vs None)
        -> (   @dmap (fin sfuncs) (fun f => hlist (expr fs vs) (SDomain (get sfuncs f))) 
          -> map (expr fs vs pcType) (sexpr fs sfuncs consts (stateType :: vs))
          -> list (expr fs vs None)-> T) -> T 
        with
        | Inj _ p => fun fs cps ps cc =>
          cc fs cps (p :: ps)
        | Star _ l r => fun fs cps ps cc =>
          hash_cc l fs cps ps (fun a b c => hash_cc r a b c cc)
        | Func _ f args => fun fs cps ps cc =>
          cc (dmap_insert f args fs) cps ps 
        | Cptr _ p s => fun fs cps ps cc =>
          cc fs (map_insert p s cps) ps
        | _ => fun fs cps ps cc =>
          (** TODO : Other cases are problematic... **)
          cc fs cps ps
      end.
*)

    Lemma denote_hash : forall (s :sexpr fs sfuncs consts nil) cs, 
      Himp stateMem cs (denote (hash s)) s.
    Proof.
      (** This is too weak, need to generalize with respect to the continuation,
       ** should probably switch to non-cps for the time being... 
       **)
      unfold Himp. intros.
      generalize (@HNil (option (@fin type types)) (@tvarD types)).
      revert s.
      unfold tvar.
      generalize dependent (@nil (option (@fin type types))).
      induction s; simpl; unfold denote, L.himp; simpl;
        repeat rewrite map_fold_empty in *; repeat rewrite dmap_fold_empty in *; intuition.
        (* *)
        admit.
        (* *)
        unfold L.himp in *. admit.
        (* *)
(*
        eapply Exists_E in H. eassumption. simpl. intros.
        eapply Exists_E. simpl. econstructor. simpl. left. reflexivity. simpl.
        intros. eapply And_E2. eapply And_E2. econstructor. simpl. left. 
        eapply And_E2. eapply And_E2. eapply Exists_E in H.  eassumption. simpl.
        

        intros.
        eapply Exists_I. 
        

        (** Admit *) admit.
        unfold denote in *. simpl in H.
        repeat eapply PropX.Exists_I.
        repeat eapply PropX.And_I.
*)
    Admitted.

    (** Procedure:
     ** - Hash the left hand side
     ** - ?? Handle implications...
     ** - ?? Generate <> constraints ??
     ** - For each right hand side conjunct
     **   - if it is in the SHeap
     **       cancel
     **     else 
     **       ?? is this automatically problematic, this procedure probably won't prove it
     ** - Discharge pure constraints with solver...
     **)

    Goal forall cs (a : fin consts), 
      Himp stateMem cs (Const fs sfuncs nil a) (Const fs sfuncs nil a).
      intros.
      pose (ReflSep cs nil (Const _ _ nil a) (Const _ _ nil a)). simpl in *.
      (** Note: everything has to be concrete in order for simplification to work! **)
      unfold ReflSep in *. unfold sexprEq in *.
      destruct (finEq a a). simpl in *. 
      match goal with
        | [ H := Some ?X |- _ ] => generalize X
      end. auto.
      congruence.
    Defined.

  End BabySep.

  


  Section QSexpr.
    (** Guarded separation logic expressions **)
  End QSexpr.
    

End SepExpr.
