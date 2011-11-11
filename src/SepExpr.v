Require Import List.
Require Import Expr.
Require Import Heaps SepTheoryX PropX.
Require Import PropXTac.
Require Import PMap.
Require Import Classes.RelationClasses.

Set Implicit Arguments.

Module SepExpr (B : Heap).
  Module ST := SepTheoryX.SepTheoryX B.  

  Section env.

    Variable types : list type.
    Variable funcs : functions types.

    Variable pcType : tvar types.    
    Variable stateType : tvar types.
    Variable stateMem : tvarD stateType -> B.mem.

    Record ssignature := {
      SDomain : list (tvar types) ;
      SDenotation : functionTypeD (map (@tvarD types) SDomain) (ST.hprop (tvarD pcType) (tvarD stateType) nil)
    }.
    Variable sfuncs : list ssignature.

    Inductive sexpr (uvars : variables types) : variables types -> Type :=
    | Emp : forall vars, sexpr uvars vars
    | Inj : forall vars, expr funcs vars uvars None -> sexpr uvars vars
    | Star : forall vars, sexpr uvars vars -> sexpr uvars vars -> sexpr uvars vars
    | Exists : forall vars t, sexpr uvars (t :: vars) -> sexpr uvars vars
    | Func : forall vars (f : fin sfuncs), 
      hlist (expr funcs vars uvars) (SDomain (get sfuncs f)) -> sexpr uvars vars
      (* this Const can not mention the higher-order variables *)
    | Const : forall vars, ST.hprop (tvarD pcType) (tvarD stateType) nil (*PropX (tvarD pcType) (tvarD stateType)*) -> sexpr uvars vars
    (** If PtsTo is derived: we can handle different sizes easily, 
     ** If PtsTo is built-in: we can derive <> facts easily (also precision)
     **)
    .

    (** NOTE: If I want to be able to reflect arbitrary propX terms (ExistsX,ForallX), then I'm going to need
     ** another index on sexpr to express the (type -> PropX)
     **)


    Fixpoint sexprD uvars vars (s : sexpr uvars vars)
      : hlist (@tvarD types) uvars -> hlist (@tvarD types) vars -> 
        ST.hprop (tvarD pcType) (tvarD stateType) nil :=
      match s in sexpr _ vs
        return hlist (@tvarD types) uvars -> hlist (@tvarD types) vs
            -> ST.hprop (tvarD pcType) (tvarD stateType) nil 
        with
        | Emp v => fun e g => 
          ST.emp _ _
        | Inj v p => fun e g =>
          ST.inj (PropX.Inj (exprD g e p)) 
        | Star _ l r => fun e g => 
          ST.star (sexprD l e g) (sexprD r e g)
        | Exists _ t b => fun e g => 
          ST.ex (fun x : tvarD t => @sexprD _ _ b e (HCons x g))
        | Func _ f b => fun e g =>
          applyD (exprD g e) b _ (SDenotation (get sfuncs f))
        | Const _ p => fun _ _ => p
      end.

(*
    Section Cmp.
      Definition sexprCmp vars (a : sexpr vars) : forall b, option (dcomp a b).
        refine ((fix sexprCmp vars (a : sexpr vars) {struct a} : forall b, option (dcomp a b) :=
          match a in sexpr vars return forall b : sexpr vars, option (dcomp a b) with
            | Emp _ => fun b =>
              match b with
                | Emp _ => Some (Env.Eq _)
                | _ => Some (Env.Lt _ _)
              end
            | Inj v l => fun b =>
              match b in sexpr v' return forall l : expr funcs v' None, option (dcomp (Inj l) b) with
                | Inj _ r => fun l => match exprEq l r with
                                        | Some _ => Some (Env.Eq _)
                                        | None => None
                                      end
                | Emp _ => fun _ => Some (Gt _ _)
                | _ => fun _ => Some (Lt _ _)
              end l
            | Star v ll lr => fun b =>
              match b in sexpr v' 
                return forall (Heq : v' = v), (forall (x y : sexpr v'), option (dcomp (Star ll lr) (match Heq in _ = t 
                                                                                                      return sexpr t
                                                                                                      with
                                                                                                      | refl_equal => Star x y
                                                                                                    end)))
                -> option (dcomp (Star ll lr) (match Heq in _ = t return sexpr t with
                                                 | refl_equal => b
                                               end))
                with
                | Star _ rl rr => fun _ cc => cc rl rr
                | Emp _ | Inj _ _ => fun _ _ => Some (Env.Gt _ _)
                | _ => fun _ _ => Some (Env.Lt _ _)
              end (refl_equal _)
              (fun (x y : sexpr v) =>
                match sexprCmp _ ll x with
                  | Some Env.Lt => Some (Env.Lt _ _)
                  | Some Env.Gt => Some (Env.Gt _ _)
                  | Some (Env.Eq _) => 
                    match sexprCmp _ lr y with
                      | Some Env.Lt => Some (Env.Lt _ _)
                      | Some Env.Gt => Some (Env.Gt _ _)
                      | Some (Env.Eq _) => Some (Env.Eq _)
                      | None => None
                    end
                  | None => 
                    match sexprCmp _ lr y with
                      | Some Env.Lt => Some (Env.Lt _ _)
                      | Some Env.Gt => Some (Env.Gt _ _)
                      | _ => None
                    end                    
                end)
            | Exists v t body => fun b =>
              match b in sexpr v' 
                return forall (Heq : v' = v),
                  (forall t' (x : sexpr (t' :: v')), t' = t -> option (dcomp (Exists body) (match Heq in _ = t 
                                                                                              return sexpr t 
                                                                                              with
                                                                                              | refl_equal => Exists x
                                                                                            end))) ->
                  option (dcomp (Exists body) (match Heq in _ = t return sexpr t with
                                                 | refl_equal => b
                                               end))
                with
                | Exists v' t' b' => fun Heq cc =>
                  match tvar_dec t' t with
                    | left pf => cc _ _ _
                    | right _ => None
                  end
                | Emp _ | Inj _ _ | Star _ _ _ => fun _ _ => Some (Env.Gt _ _)
                | _ => fun _ _ => Some (Env.Lt _ _)
              end (refl_equal _)
              (fun t x eqq => 
                match sexprCmp _ body match eqq in _ = t' return sexpr (t' :: v) with
                                        | refl_equal => x
                                      end
                  with
                  | Some Env.Lt => Some (Env.Lt _ _)
                  | Some Env.Gt => Some (Env.Gt _ _)
                  | Some (Env.Eq _) => Some (Env.Eq _)
                  | None => None
                end)
            | Cptr v lp ls => fun b =>
              match b in sexpr v' 
                return forall (Heq : v' = v), 
                  (forall (p : expr funcs v' pcType) (s : sexpr (stateType :: v')), 
                    option (dcomp (Cptr lp ls) (match Heq in _ = t
                                                  return sexpr t
                                                  with 
                                                  | refl_equal => Cptr p s
                                                end))) ->
                  option (dcomp (Cptr lp ls) (match Heq in _ = t return sexpr t with
                                                | refl_equal => b
                                              end))
                with
                | Cptr _ rp rs => fun _ cc => cc rp rs
                | Emp _ | Inj _ _ | Star _ _ _ | Exists _ _ _ => fun _ _ => Some (Env.Gt _ _)
                | _ => fun _ _ => Some (Env.Lt _ _)
              end (refl_equal _)
              (fun x y =>
                match exprEq lp x with
                  | Some _ => match sexprCmp _ ls y with
                                | Some (Env.Eq _) => Some (Env.Eq _)
                                | Some Env.Gt => Some (Env.Gt _ _)
                                | Some Env.Lt => Some (Env.Lt _ _)
                                | None => None
                              end                    
                  | _ => None
                end)
            | Func v f args => fun b =>
              match b in sexpr v'
                return forall (Heq : v' = v), 
                  (forall args', option (args = args')) ->
                  option (dcomp (Func f args) (match Heq in _ = t 
                                                 return sexpr t
                                                 with
                                                 | refl_equal => b
                                               end))
                with
                | Func v' f' args' => fun Heq cc => 
                  match finCmp f f' with
                    | Env.Eq pf => match cc match Heq in _ = t 
                                            return hlist (expr funcs t) (SDomain (get sfuncs f))
                                            with 
                                            | refl_equal => match sym_eq pf in _ = t 
                                                              return hlist (expr funcs v') (SDomain (get sfuncs t)) with
                                                              | refl_equal => args'
                                                            end
                                          end
                                   with
                                   | Some _ => Some (Env.Eq _)
                                   | None => None
                                 end                                     
                    | Env.Lt => Some (Env.Lt _ _)
                    | Env.Gt => Some (Env.Gt _ _)
                  end
                | Emp _ | Inj _ _ | Star _ _ _ | Exists _ _ _ | Cptr _ _ _ => fun _ _ => Some (Env.Gt _ _)
                | _ => fun _ _ => Some (Env.Lt _ _)
              end (refl_equal _) (hlistEq (@exprEq _ _ _) args)
            | Const _ x => fun b => 
              match b with
                | Const _ y => match finCmp x y with
                                 | Env.Eq _ => Some (Env.Eq _)
                                 | Env.Lt => Some (Env.Lt _ _)
                                 | Env.Gt => Some (Env.Gt _ _)
                               end
                | _ => Some (Env.Gt _ _)
              end
          end) vars a);
        clear sexprCmp; try abstract (subst; reflexivity).
      Defined.
    End Cmp.
*)

    Section SProver.
      Definition himp u1 u2 (vars : variables types) (U1 : hlist (@tvarD _) u1) (U2 : hlist (@tvarD _) u2) (G : hlist (@tvarD _) vars) (cs : codeSpec (tvarD pcType) (tvarD stateType))
        (gl : sexpr u1 vars) (gr : sexpr u2 vars) : Prop :=
        ST.himp cs (sexprD gl U1 G) (sexprD gr U2 G).
(*      Definition Himp := @himp nil nil nil HNil HNil HNil. *)
      Definition heq u1 u2 (vars : variables types) (U1 : hlist (@tvarD _) u1) (U2 : hlist (@tvarD _) u2) (G : hlist (@tvarD _) vars) (cs : codeSpec (tvarD pcType) (tvarD stateType))
        (gl : sexpr u1 vars) (gr : sexpr u2 vars) : Prop :=
        ST.heq cs (sexprD gl U1 G) (sexprD gr U2 G).
(*      Definition Heq := @heq nil HNil. *)

      Global Instance Trans_himp u v U g cs : Transitive (@himp u u v U U g cs).
      Proof.
        red. intros. unfold himp. etransitivity; eauto.
      Qed.

(*      Global Instance Trans_Himp cs : Transitive (@Himp cs).
      Proof.
        red. intros. unfold Himp, himp. etransitivity; eauto.
      Qed.
*)

      Global Instance Trans_heq u v U g cs : Transitive (@heq u u v U U g cs).
      Proof.
        red. intros. unfold heq. etransitivity; eauto.
      Qed.

(*
      Global Instance Trans_Heq cs : Transitive (@Heq cs).
      Proof.
        red. intros. unfold Heq, heq. etransitivity; eauto.
      Qed.
*)

      Section exists_subst.
        Variable u1 : variables types.
        Variable U1 : hlist (@tvarD _) u1.
  
        Fixpoint exists_subst (u : variables types)
          (U : hlist (fun t => option (expr funcs nil u1 t)) u) :
          (hlist (@tvarD _) u -> Prop) -> Prop :=
          match U in hlist _ u
            return (hlist (@tvarD _) u -> Prop) -> Prop
            with
            | HNil => fun cc => cc HNil
            | HCons _ _ v r => fun cc =>
              match v with
                | None => exists v, exists_subst r (fun z => cc (HCons v z))
                | Some v =>
                  let v := exprD HNil U1 v in
                    exists_subst r (fun z => cc (HCons v z))
              end
          end.

      End exists_subst.

      Inductive SepResult (cs : codeSpec (tvarD pcType) (tvarD stateType)) (gl gr : sexpr nil nil) : Type :=
      | Prove : forall u1 u2 (l : sexpr u1 nil) (r : sexpr u2 nil)
        (U2 : hlist (fun t => option (expr funcs nil u1 t)) u2),
        
        (forall U1 : hlist (@tvarD _) u1, 
          @exists_subst _ U1 _ U2 (fun k => 
          ST.himp cs (sexprD l U1 HNil) (sexprD r k HNil) -> himp HNil HNil HNil cs gl gr))
        -> SepResult cs gl gr.

      Definition SProverT : Type := forall
        (cs : codeSpec (tvarD pcType) (tvarD stateType)) 
(*        (hyps : list (@Qexpr types funcs)) (** Pure Premises **) *)
        (gl gr : sexpr nil nil),
        SepResult cs gl gr.
    
    End SProver.

  End env.

  Implicit Arguments Emp [ types funcs pcType stateType sfuncs uvars vars ].
  Implicit Arguments Inj [ types funcs pcType stateType sfuncs uvars vars ].
  Implicit Arguments Star [ types funcs pcType stateType sfuncs uvars vars ].
  Implicit Arguments Exists [ types funcs pcType stateType sfuncs uvars vars ].
  Implicit Arguments Func [ types funcs pcType stateType sfuncs uvars vars ].
  Implicit Arguments Const [ types funcs pcType stateType sfuncs uvars vars ].

(*
  Section lift.
    Variable types : list type.
    Variable funcs : functions types.
    Variable pcType : tvar types.    
    Variable stateType : tvar types.
    Variable stateMem : tvarD stateType -> B.mem.
    Variable sfuncs : list (ssignature pcType stateType).

    Fixpoint liftSExpr vars ext vars' (s : sexpr funcs sfuncs (vars ++ vars')) 
      : sexpr funcs sfuncs (vars ++ ext ++ vars') :=
      match s in sexpr _ _ vs 
        return vs = vars ++ vars' -> sexpr funcs sfuncs (vars ++ ext ++ vars') with
        | Emp _ => fun _ => Emp
        | Inj _ p => fun pf => 
          Inj (liftExpr vars ext vars' match
                                         pf in _ = t return expr funcs t None with
                                         | refl_equal => p
                                       end)
        | Star v' l r => fun pf => 
          Star 
            (liftSExpr vars ext vars' match pf in _ = t return sexpr funcs sfuncs t with
                                        | refl_equal => l
                                      end) 
            (liftSExpr vars ext vars' match pf in _ = t return sexpr funcs sfuncs t with
                                        | refl_equal => r
                                      end)
        | Exists v t b => fun pf => 
          let b := 
            match pf in _ = v' return sexpr funcs sfuncs (t :: v') with
              | refl_equal => b
            end
          in
          Exists t (liftSExpr (t :: vars) ext vars' b)
        | Func v f a => fun pf =>
          let a :=
            match pf in _ = v' return hlist (expr funcs v') (SDomain (get sfuncs f)) with
              | refl_equal => a
            end
          in
          Func f (@hlist_map (tvar types) (expr funcs (vars ++ vars')) (expr funcs (vars ++ ext ++ vars')) (fun _ e => liftExpr vars ext vars' e) _ a)
        | Const v p => fun _ => Const p
      end (refl_equal _).

  End lift.
*)

  Section BabySep.
    Variable types : list type.
    Variable fs : functions types.
    Variable pcType : tvar types.    
    Variable stateType : tvar types.
    Variable stateMem : tvarD stateType -> B.mem.
    Variable sfuncs : list (ssignature pcType stateType).

    Record SHeap uvars vars : Type :=
    { funcs  : @dmap (fin sfuncs) (fun f => list (hlist (expr fs vars uvars) (SDomain (get sfuncs f))))
    ; pures  : list (expr fs vars uvars None)
    ; other  : list (ST.hprop (tvarD pcType) (tvarD stateType) nil)
    }.
  
    Definition SHeap_empty uvars vars : SHeap uvars vars := 
      {| funcs := dmap_empty
       ; pures := nil
       ; other := nil
       |}.

    Definition denote uvars vars (h : SHeap uvars vars) :  sexpr fs sfuncs uvars vars :=
      let a := dmap_fold (fun a x y => fold_left (fun a y => Star (Func x y) a) y a) Emp (funcs h) in
(*      let b := fmap_fold (fun a x y => Star (Cptr x y) a) Emp (cptrs h) in *)
      let c := fold_right (fun x a => Star (Inj x) a) Emp (pures h) in
(*      let d := fold_right (fun x a => Star (Const x) a) Emp (cnsts h) in *)
      let e := fold_right (fun x a => Star (Const x) a) Emp (other h) in
      Star a (Star c e).

    Definition liftFunctions uvars vars' ext vars
      : dmap (fin sfuncs) (fun f : fin sfuncs => list (hlist (expr fs (vars' ++ vars) uvars) (SDomain (get sfuncs f)))) ->
        dmap (fin sfuncs) (fun f : fin sfuncs => list (hlist (expr fs (vars' ++ ext ++ vars) uvars) (SDomain (get sfuncs f))))
      :=
      dmap_map _ _ _ (fun t' => @List.map _ _ (@hlist_map _ _ _ (liftExpr vars' ext vars) _)).

    Definition liftPures uvars vars' ext vars 
      : list (expr fs (vars' ++ vars) uvars None) -> list (expr fs (vars' ++ ext ++ vars) uvars None)
      := map (liftExpr vars' ext vars (T := None)).

    Definition liftSHeap uvars vars ext vars' (s : SHeap uvars (vars ++ vars')) : SHeap uvars (vars ++ ext ++ vars') :=
      {| funcs := liftFunctions vars ext vars' (funcs s)
       ; pures := liftPures vars ext vars' (pures s)
       ; other := other s
       |}.

    Parameter join_SHeap : forall uvars vars, 
      SHeap uvars vars -> SHeap uvars vars -> SHeap uvars vars.

    Fixpoint hash uvars vars (s : sexpr fs sfuncs uvars vars) : { vars' : variables types & SHeap uvars (vars' ++ vars) } :=
      match s in sexpr _ _ vars return { vars' : variables types & SHeap (vars' ++ vars) } with
        | Emp _ => @existT _ _ nil (SHeap_empty _)
        | Inj _ p => @existT _ _ nil
          {| funcs := dmap_empty
           ; pures := p :: nil
           ; other := nil
           |}
        | Star vs l r =>
          match hash l, hash r with
            | existT vl hl , existT vr hr => 
              @existT _ _ (vl ++ vr) 
              (join_SHeap 
                match sym_eq (app_ass vl vr vs) in _ = t return SHeap t with
                  | refl_equal => liftSHeap vl vr vs hl
                end 
                match sym_eq (app_ass vl vr vs) in _ = t return SHeap t with
                  | refl_equal => liftSHeap nil vl (vr ++ vs) hr
                end)
          end
        | Exists vs t b =>
          match hash b with
            | existT v b =>
              @existT _ (fun x => SHeap (x ++ vs)) (v ++ t :: nil)
                match eq_sym (pf_list_simpl t vs v) in _ = t' return SHeap t' with
                  | refl_equal => b
                end
          end
        | Func v f a =>
          @existT _ _ nil
            {| funcs := dmap_insert (fun x y => Some (@finCmp _ sfuncs x y)) f (a :: nil) dmap_empty
             ; pures := nil
             ; other := nil
             |}
        | Const vars c => 
          @existT _ _ nil
            {| funcs := dmap_empty
             ; pures := nil
             ; other := c :: nil
             |}
      end.
    
    Fixpoint existsEach (vars vars' : variables types) 
      : sexpr fs sfuncs (vars ++ vars') -> sexpr fs sfuncs vars' :=
      match vars as vars return sexpr fs sfuncs (vars ++ vars') -> sexpr fs sfuncs vars'
        with
        | nil => fun s => s
        | a :: b => fun s => @existsEach b vars' (Exists a s)
      end.
    

(*
    Definition hash_rec vars'' vars (s : sexpr fs sfuncs vars) 
      :  (forall vs,
             @dmap (fin sfuncs) (fun f => list (hlist (expr fs (vs ++ vars)) (SDomain (get sfuncs f))))
          -> list (expr fs (vs ++ vars) None)
          -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
          -> { vars' : variables types & SHeap (vars' ++ vs ++ vars) })
      -> @dmap (fin sfuncs) (fun f => list (hlist (expr fs (vars'' ++ vars)) (SDomain (get sfuncs f))))
      -> list (expr fs (vars'' ++ vars) None)
      -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
      -> { vars' : variables types & SHeap (vars' ++ vars'' ++ vars) }.
    refine ((fix hash_rec vars (s : sexpr fs sfuncs vars) 
      :  forall vars'', (forall vs,
             @dmap (fin sfuncs) (fun f => list (hlist (expr fs (vs ++ vars)) (SDomain (get sfuncs f))))
          -> list (expr fs (vs ++ vars) None)
          -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
          -> { vars' : variables types & SHeap (vars' ++ vs ++ vars) })
      -> @dmap (fin sfuncs) (fun f => list (hlist (expr fs (vars'' ++ vars)) (SDomain (get sfuncs f))))
      -> list (expr fs (vars'' ++ vars) None)
      -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
      -> { vars' : variables types & SHeap (vars' ++ vars'' ++ vars) } :=
      match s in @sexpr _ _ _ _ _ vs 
        return forall vars'',
           (forall vs', 
               @dmap (fin sfuncs) (fun f => list (hlist (expr fs (vs' ++ vs)) (SDomain (get sfuncs f))))
            -> list (expr fs (vs' ++ vs) None)
            -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
            -> { vars' : variables types & SHeap (vars' ++ vs' ++ vs) })
        -> @dmap (fin sfuncs) (fun f => list (hlist (expr fs (vars'' ++ vs)) (SDomain (get sfuncs f))))
        -> list (expr fs (vars'' ++ vs) None)
        -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
        -> { vars' : variables types & SHeap (vars' ++ vars'' ++ vs) }
        with
        | Emp vars => fun vars'' cc => _
        | Inj _ p => fun cc fs ps ot =>
          _ (*cc nil fs (p :: ps) ot  *)
        | Star _ l r => fun cc => _
(*          hash_rec l (fun vs => hash_rec (liftSExpr vs r) cc () () () *)
        | Func _ f args => fun cc fs ps ot => _
(*
          match dmap_remove (fun a b => Some (@finCmp _ _ a b)) f fs with
            | None =>
              cc (dmap_insert (fun a b => Some (@finCmp _ _ a b)) f (args :: nil) fs) ps ot
            | Some (v,fs') =>
              cc (dmap_insert (fun a b => Some (@finCmp _ _ a b)) f (args :: v) fs') ps ot
          end
*)
        | Exists vv t b => fun cc fs' ps ot => _
        | Const _ x => fun cc fs ps ot =>
          _ (* cc nil fs ps (x :: ot) *)
      end) vars s vars'').
    Focus.
    intros. eapply cc.
    

    Definition hash_rec vars (s : sexpr fs sfuncs vars) 
      :  (forall vs,
             @dmap (fin sfuncs) (fun f => list (hlist (expr fs (vs ++ vars)) (SDomain (get sfuncs f))))
          -> list (expr fs (vs ++ vars) None)
          -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
          -> { vars' : variables types & SHeap (vars' ++ vs ++ vars) })
      -> @dmap (fin sfuncs) (fun f => list (hlist (expr fs vars) (SDomain (get sfuncs f))))
      -> list (expr fs vars None)
      -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
      -> { vars' : variables types & SHeap (vars' ++ vars) }.
    revert s; revert vars.
    refine (Fix hash_rec vars (s : sexpr fs sfuncs vars) {struct s}
      :  (forall vs,
             @dmap (fin sfuncs) (fun f => list (hlist (expr fs (vs ++ vars)) (SDomain (get sfuncs f))))
          -> list (expr fs (vs ++ vars) None)
          -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
          -> { vars' : variables types & SHeap (vars' ++ vs ++ vars) })
      -> @dmap (fin sfuncs) (fun f => list (hlist (expr fs vars) (SDomain (get sfuncs f))))
      -> list (expr fs vars None)
      -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
      -> { vars' : variables types & SHeap (vars' ++ vars) } :=
      match s in @sexpr _ _ _ _ _ vs 
        return 
           (forall vs', 
               @dmap (fin sfuncs) (fun f => list (hlist (expr fs (vs' ++ vs)) (SDomain (get sfuncs f))))
            -> list (expr fs (vs' ++ vs) None)
            -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
            -> { vars' : variables types & SHeap (vars' ++ vs' ++ vs) })
        -> @dmap (fin sfuncs) (fun f => list (hlist (expr fs vs) (SDomain (get sfuncs f))))
        -> list (expr fs vs None)
        -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
        -> { vars' : variables types & SHeap (vars' ++ vs) }
        with
        | Emp vars => fun cc => cc nil
        | Inj _ p => fun cc fs ps ot =>
          cc nil fs (p :: ps) ot 
        | Star vv l r => fun cc =>
          let cc' vs :=
            hash_rec (vs ++ vv) (liftSExpr nil vs vv r)
            (fun vs' => match app_ass _ _ _ in _ = t 
                          return 
                          dmap (fin sfuncs)
                          (fun f : fin sfuncs =>
                            list (hlist (expr fs t) (SDomain (get sfuncs f)))) ->
                          list (expr fs t None) ->
                          list (ST.Hprop (tvarD pcType) (tvarD stateType)) ->
                          {vars' : variables types & SHeap (vars' ++ t)}
                          with
                          | refl_equal => cc (vs' ++ vs)
                        end)
          in
          hash_rec _ l cc'
        | Func _ f args => fun cc fs ps ot => _
(*
          match dmap_remove (fun a b => Some (@finCmp _ _ a b)) f fs with
            | None =>
              cc (dmap_insert (fun a b => Some (@finCmp _ _ a b)) f (args :: nil) fs) ps ot
            | Some (v,fs') =>
              cc (dmap_insert (fun a b => Some (@finCmp _ _ a b)) f (args :: v) fs') ps ot
          end
*)
        | Exists vv t b => fun cc fs' ps ot => 
          let cc := fun vs =>
            match pf_list_simpl t vv vs in _ = t' 
              return dmap (fin sfuncs)
              (fun f : fin sfuncs => list (hlist (expr fs t') (SDomain (get sfuncs f)))) ->
              list (expr fs t' None) ->
              list (ST.Hprop (tvarD pcType) (tvarD stateType)) ->
              {vars' : variables types & SHeap (vars' ++ t')}
              with
              | refl_equal => @cc (vs ++ t :: nil)
            end
          in
          let fs' := dmap_map _ _ _ (fun t' => @List.map _ _ (@hlist_map _ _ _ (liftExpr vv (t :: nil) nil) _)) fs' in
          let ps' := map (liftExpr vv (t :: nil) nil (T := None)) ps in
          match hash_rec _ b cc fs' ps' ot with
            | existT a b => @existT _ _ (a ++ t :: nil) match eq_sym (pf_list_simpl t vv a) in _ = t' return SHeap t' with
                                                          | refl_equal => b
                                                        end
          end
        | Const _ x => fun cc fs ps ot =>
          cc nil fs ps (x :: ot)
      end).

    Definition hash_rec vars (s : sexpr fs sfuncs vars) 
      :  (forall vs,
             @dmap (fin sfuncs) (fun f => list (hlist (expr fs (vs ++ vars)) (SDomain (get sfuncs f))))
          -> list (expr fs (vs ++ vars) None)
          -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
          -> { vars' : variables types & SHeap (vars' ++ vs ++ vars) })
      -> @dmap (fin sfuncs) (fun f => list (hlist (expr fs vars) (SDomain (get sfuncs f))))
      -> list (expr fs vars None)
      -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
      -> { vars' : variables types & SHeap (vars' ++ vars) }.
    revert s; revert vars.
    refine (fix hash_rec vars (s : sexpr fs sfuncs vars) {struct s}
      :  (forall vs,
             @dmap (fin sfuncs) (fun f => list (hlist (expr fs (vs ++ vars)) (SDomain (get sfuncs f))))
          -> list (expr fs (vs ++ vars) None)
          -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
          -> { vars' : variables types & SHeap (vars' ++ vs ++ vars) })
      -> @dmap (fin sfuncs) (fun f => list (hlist (expr fs vars) (SDomain (get sfuncs f))))
      -> list (expr fs vars None)
      -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
      -> { vars' : variables types & SHeap (vars' ++ vars) } :=
      match s in @sexpr _ _ _ _ _ vs 
        return 
           (forall vs', 
               @dmap (fin sfuncs) (fun f => list (hlist (expr fs (vs' ++ vs)) (SDomain (get sfuncs f))))
            -> list (expr fs (vs' ++ vs) None)
            -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
            -> { vars' : variables types & SHeap (vars' ++ vs' ++ vs) })
        -> @dmap (fin sfuncs) (fun f => list (hlist (expr fs vs) (SDomain (get sfuncs f))))
        -> list (expr fs vs None)
        -> list (ST.Hprop (tvarD pcType) (tvarD stateType))
        -> { vars' : variables types & SHeap (vars' ++ vs) }
        with
        | Emp vars => fun cc => cc nil
        | Inj _ p => fun cc fs ps ot =>
          cc nil fs (p :: ps) ot 
        | Star vv l r => fun cc =>
          let cc' vs :=
            hash_rec (vs ++ vv) (liftSExpr nil vs vv r)
            (fun vs' => match app_ass _ _ _ in _ = t 
                          return 
                          dmap (fin sfuncs)
                          (fun f : fin sfuncs =>
                            list (hlist (expr fs t) (SDomain (get sfuncs f)))) ->
                          list (expr fs t None) ->
                          list (ST.Hprop (tvarD pcType) (tvarD stateType)) ->
                          {vars' : variables types & SHeap (vars' ++ t)}
                          with
                          | refl_equal => cc (vs' ++ vs)
                        end)
          in
          hash_rec _ l cc'
        | Func _ f args => fun cc fs ps ot => _
(*
          match dmap_remove (fun a b => Some (@finCmp _ _ a b)) f fs with
            | None =>
              cc (dmap_insert (fun a b => Some (@finCmp _ _ a b)) f (args :: nil) fs) ps ot
            | Some (v,fs') =>
              cc (dmap_insert (fun a b => Some (@finCmp _ _ a b)) f (args :: v) fs') ps ot
          end
*)
        | Exists vv t b => fun cc fs' ps ot => 
          let cc := fun vs =>
            match pf_list_simpl t vv vs in _ = t' 
              return dmap (fin sfuncs)
              (fun f : fin sfuncs => list (hlist (expr fs t') (SDomain (get sfuncs f)))) ->
              list (expr fs t' None) ->
              list (ST.Hprop (tvarD pcType) (tvarD stateType)) ->
              {vars' : variables types & SHeap (vars' ++ t')}
              with
              | refl_equal => @cc (vs ++ t :: nil)
            end
          in
          let fs' := dmap_map _ _ _ (fun t' => @List.map _ _ (@hlist_map _ _ _ (liftExpr vv (t :: nil) nil) _)) fs' in
          let ps' := map (liftExpr vv (t :: nil) nil (T := None)) ps in
          match hash_rec _ b cc fs' ps' ot with
            | existT a b => @existT _ _ (a ++ t :: nil) match eq_sym (pf_list_simpl t vv a) in _ = t' return SHeap t' with
                                                          | refl_equal => b
                                                        end
          end
        | Const _ x => fun cc fs ps ot =>
          cc nil fs ps (x :: ot)
      end).
    Focus.
    refine (
          let cc' vs :=
            hash_rec (vs ++ vv) (liftSExpr nil vs vv r)
            (fun vs' => match app_ass _ _ _ in _ = t 
                          return 
                          dmap (fin sfuncs)
                          (fun f : fin sfuncs =>
                            list (hlist (expr fs t) (SDomain (get sfuncs f)))) ->
                          list (expr fs t None) ->
                          list (ST.Hprop (tvarD pcType) (tvarD stateType)) ->
                          {vars' : variables types & SHeap (vars' ++ t)}
                          with
                          | refl_equal => cc (vs' ++ vs)
                        end)
          in
          hash_rec _ l cc'

).
    


    Definition hash_cc vars (s : sexpr fs sfuncs vars)
      (cc : @dmap (fin sfuncs) (fun f => list (hlist (expr fs vars) (SDomain (get sfuncs f))))
       -> list (expr fs vars None)
       -> list (sexpr fs sfuncs vars) -> { vars' : variables types & SHeap (vars' ++ vars) }) : 
      { vars' : variables types & SHeap (vars' ++ vars) } :=
      @hash_rec vars s cc dmap_empty nil nil.
*)

    Section WithCS.
    Variable cs : codeSpec (tvarD pcType) (tvarD stateType).

    Ltac cancel_all :=
      let s :=
        (   reflexivity 
         || simple apply ST.himp_star_emp_c
         || simple apply ST.himp_star_emp_p
         || simple apply ST.heq_star_emp
         || (symmetry; simple apply ST.heq_star_emp; symmetry)
         || simple apply ST.himp_star_cancel
         || simple apply ST.heq_star_cancel
        )
      in
      let perm :=
        try ((eapply ST.himp_star_comm_p; repeat simple apply ST.himp_star_assoc_p) || 
             (eapply ST.heq_star_comm; symmetry; repeat simple apply ST.heq_star_assoc; symmetry)); 
        try do 10 (s || 
          match goal with
            | [ |- ST.heq _ _ _ _ _ ] =>
              symmetry; simple apply ST.heq_star_comm; symmetry; repeat simple apply ST.heq_star_assoc
            | [ |- ST.himp _ _ _ _ _ ] =>
              repeat (simple apply ST.himp_star_assoc_c)
          end)
      in
      do 10 perm.

    Theorem denote_hash : forall G s cs, 
      heq G cs s (existsEach (projT1 (hash s)) nil (denote (projT2 (hash s)))).
    Proof.
      clear. induction s; unfold denote, heq; simpl; intros.
        cancel_all.
        cancel_all.
        admit.
        admit.
        cancel_all.
        cancel_all.
    Admitted.


    Lemma fold_star : forall K V vars G (ctor : forall k : K, V k -> sexpr fs sfuncs vars) (B : @dmap K V) P Q,
      heq G cs 
        (Star Q (dmap_fold (fun (a : sexpr fs sfuncs vars) (k : K) (v : V k) => Star (ctor k v) a) P B))
        (Star P (dmap_fold (fun (a : sexpr fs sfuncs vars) (k : K) (v : V k) => Star (ctor k v) a) Q B)).
    Proof.
      induction B; unfold heq in *; simpl in *; intros. cancel_all.
      etransitivity. eapply IHB2. etransitivity. 2: eapply IHB2.
      etransitivity. eapply ST.heq_star_frame. etransitivity; [ | apply (IHB1 (Star (ctor k v) P) Emp); simpl ]; cancel_all.
      etransitivity; [ | apply (IHB2 Q Emp) ]; cancel_all.
      etransitivity. Focus 2.
      eapply ST.heq_star_frame. etransitivity; [ eapply (IHB1 Emp (Star (ctor k v) Q)) | ]; cancel_all.
      etransitivity; [ eapply (IHB2 Emp P) | ]; cancel_all. simpl; cancel_all.
    Qed.

    Lemma fold_star' : forall K V vars G (ctor : forall k : K, V k -> sexpr fs sfuncs vars) (B : @dmap K V) P,
      heq G cs 
        (dmap_fold (fun (a : sexpr fs sfuncs vars) (k : K) (v : V k) => Star (ctor k v) a) P B)
        (Star P (dmap_fold (fun (a : sexpr fs sfuncs vars) (k : K) (v : V k) => Star (ctor k v) a) Emp B)).
    Proof.
      intros. etransitivity; [ | eapply fold_star ]. unfold heq; simpl; cancel_all.
    Qed.

    Lemma fold_star'' : forall K V vars G (ctor : forall k : K, V k -> sexpr fs sfuncs vars) (B : @dmap K V) P,
      heq G cs
        (Star P (dmap_fold (fun (a : sexpr fs sfuncs vars) (k : K) (v : V k) => Star (ctor k v) a) Emp B))
        (dmap_fold (fun (a : sexpr fs sfuncs vars) (k : K) (v : V k) => Star (ctor k v) a) P B).
    Proof.
      intros. etransitivity; [ eapply fold_star | ]; unfold heq; simpl; cancel_all.
    Qed.

    Lemma star_insert : forall K V vars G (ctor : forall k : K, V k -> sexpr fs sfuncs vars)
      (cmp : forall a b : K, option (dcomp a b)) (B : @dmap K V) k (v : V k) P,
      heq G cs
        (dmap_fold
          (fun (a : sexpr fs sfuncs vars) (k : K) (v : V k) =>
            Star (ctor k v) a) P (@dmap_insert _ _ cmp k v B))
        (Star
          (dmap_fold
            (fun (a : sexpr fs sfuncs vars) (k : K) (v : V k) => Star (ctor k v) a) P B) (ctor k v)).
    Proof.      
      clear. induction B. simpl. intros. cancel_all. 
      simpl. intros. destruct (cmp k k0). destruct d; simpl in *. etransitivity; [ eapply fold_star' | ].
      unfold heq in *; simpl in *.
    Admitted.

(*
    Lemma denote_hash_rec : forall vars (s : sexpr fs sfuncs consts vars) P (cc : _ -> _ -> _ -> _ -> _ -> SHeap vars) G,
      (forall A B C D E, 
        heq stateMem G cs 
          (denote (cc D E A B C))
          (Star P (denote (Build_SHeap D E A B C)))) ->
      forall A B C D E,
      heq stateMem G cs (denote (hash_rec s cc A B C D E)) (Star (Star (denote (Build_SHeap A B C D E)) P) s).
    Proof.
      unfold hash_cc, Himp; do 2 intro. unfold heq.
      induction s; intros; simpl; instantiate.
(*
        try solve [ cancel_all; eauto | etransitivity; [ eapply H | ]; unfold denote; simpl; do 5 cancel_all ].
        (* Star *)
        etransitivity. eapply IHs1. intros. etransitivity. eapply IHs2. intros. etransitivity. eapply H. reflexivity.
        instantiate (1 := Star P s2). cancel_all. repeat cancel_all.
        (* Cptr *) Focus.
        etransitivity. eapply H. unfold denote; simpl. cancel_all. apply star_comm_p. cancel_all. cancel_all.
        clear.
        match goal with
          | [ |- context [ @Emp ?A ?B ?C ?D ?E ?F ?G ] ] => generalize (@Emp A B C D E F G)
        end. induction B; intros; simpl. apply star_comm_p. reflexivity. etransitivity. unfold fmap_fold. eapply fold_star'.
        etransitivity. eapply star_frame. eapply IHB1. reflexivity. cancel_all. etransitivity. eapply star_frame.
        unfold fmap_fold. eapply fold_star'. reflexivity. cancel_all. etransitivity. 2: eapply star_frame.
        2: unfold fmap_fold; eapply fold_star''. 2: reflexivity. apply star_assoc_c. etransitivity.
        2: eapply star_frame. 2: eapply fold_star''. 2: reflexivity. cancel_all.
        (** Func **) Focus.
*)
    Admitted.

    Lemma denote_hash_rec' : forall vars (s : sexpr fs sfuncs consts vars) P (cc : _ -> _ -> _ -> _ -> _ -> SHeap vars) G,
      (forall A B C D E, 
        himp stateMem G cs 
          (Star P (denote (Build_SHeap D E A B C)))
          (denote (cc D E A B C))) ->
      forall A B C D E,
      himp stateMem G cs (Star (Star (denote (Build_SHeap A B C D E)) P) s) (denote (hash_rec s cc A B C D E)).
    Proof.
    Admitted.



    Theorem denote_hash_cc : forall (s : sexpr fs sfuncs consts nil),
      Heq stateMem cs (denote (hash_cc s (@Build_SHeap nil))) s.
    Proof.
      unfold Himp. intros. unfold hash_cc. etransitivity. eapply denote_hash_rec.
      instantiate (1 := Emp). intros. 
      generalize (denote {| funcs := D; cptrs := E; pures := A; cnsts := B; other := C |}). unfold heq; simpl.
      intros; cancel_all. unfold denote. simpl. unfold Heq, heq; simpl.
      do 10 (try apply ST.heq_star_comm; symmetry; repeat apply ST.heq_star_assoc; symmetry; try apply ST.heq_star_emp).
      reflexivity.
    Qed.
*)


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

(*
    Goal forall cs (a : fin consts), 
      Himp stateMem cs (Const fs sfuncs nil a) (Const fs sfuncs nil a).
      intros.
      pose (ReflSep cs nil (Const _ _ nil a) (Const _ _ nil a)). simpl in *.
      (** Note: everything has to be concrete in order for simplification to work! **)
      unfold ReflSep in *. unfold sexprCmp in *.
      destruct (finCmp a a). simpl in *. 
      match goal with
        | [ H := Some ?X |- _ ] => generalize X
      end. auto.
      congruence.
    Defined.
*)

   Section TakeOut.
      Context {T : Type}.
      Variable Teq : T -> T -> bool.
      
      Require Import List.
      Fixpoint take_out (v : T) (ls : list T) (r : list T): option (list T) :=
        match ls with
          | nil => None
          | a :: b => if Teq a v then Some (r ++ b) else take_out v b (a :: r)
        end.
    End TakeOut.


    Fixpoint All vars (ls : list (expr fs vars None)) : hlist (@tvarD _) vars -> Prop :=
      match ls with
        | nil => fun _ => True
        | a :: b => fun G => exprD G a /\ All b G
      end.

    (** TODO: 
     ** - cancel with unification
     ** - 
     **)
    

    (** Eliminate e from the symbolic heap and return the set of pure facts that 
     ** imply the conclusion
     **)
    Fixpoint sepCancel vars (e : sexpr fs sfuncs vars) {struct e}
      : SHeap vars -> SHeap vars -> SHeap vars * SHeap vars :=
      match e in sexpr _ _ vars 
        return SHeap vars -> SHeap vars -> SHeap vars * SHeap vars
        with
        | Emp _ => fun h rem => (h, rem)
        | Func _ f a => fun h rem =>
          match dmap_remove (fun x y => Some (@finCmp _ _ x y)) f (funcs h) with
            | Some (ls, fs') => 
              match take_out (fun x y => if hlistEq (@exprEq _ _ _ ) x y then true else false) a ls nil with
                | None => (h,rem)
                | Some nil => 
                  ({| funcs := fs' 
                    ; pures := pures h
                    ; other := other h
                    |}, rem)
                | Some v =>
                  ({| funcs := dmap_insert (fun x y => Some (@finCmp _ _ x y)) f v fs'
                    ; pures := pures h
                    ; other := other h
                    |}, rem)
              end
            | None => (h,rem)
          end              
(*
          match fmap_remove (@exprCmp _ _ _ _) p (cptrs h) with
            | Some (s', cp') => 
              match sexprCmp s s' with
                | Some (Env.Eq _) => 
                ({| funcs := funcs h 
                  ; cptrs := cp'
                  ; pures := pures h
                  ; other := other h
                  ; cnsts := cnsts h
                  |}, rem)
                | _ => (h,rem)
              end
           | None => (h,rem)
          end
*)
        | Star _ l r => fun h rem =>
          let '(h',rem') := sepCancel l h rem in
          sepCancel r h' rem'
        | _ => fun h rem => (h,rem)
      end.
    
    Lemma sepCancel_cancels' : forall vars G e h r rl rr,
      @sepCancel vars e h r = (rl, rr) ->
      forall P,
      himp G cs (denote rl) (Star (denote rr) P) ->
      himp G cs (denote h) (Star (Star e (denote r)) P).
    Proof.
(*
      induction e; simpl; intros;
        repeat match goal with
                 | [ H : (_,_) = (_,_) |- _ ] => inversion H; clear H; subst
                 | [ H : sepCancel _ _ _ = (_,_) , H' : _ |- _ ] => apply H' in H; clear H'
               end;
        try solve [ etransitivity; [ eassumption | ]; do 5 cancel_all ].
      Focus 2.
      (* star *)
      case_eq (sepCancel e1 h r). intros. rewrite H1 in *.
      specialize (@IHe1 G _ _ _ _ H1).
      specialize (@IHe2 G _ _ _ _ H). 
      etransitivity. eapply IHe1. etransitivity. eapply IHe2. eassumption.
      instantiate (1 := (Star e2 P)). generalize (denote s0); intros; cancel_all.
      generalize (denote r); intros; cancel_all.
*)
    Admitted.

    Theorem sepCancel_cancels : forall e h rl rr,
      sepCancel e h (SHeap_empty nil) = (rl, rr) ->
      Himp cs (denote rl) (denote rr) ->
      Himp cs (denote h) e.
    Proof.
      unfold Himp; intros. etransitivity. eapply sepCancel_cancels'. eassumption.
      instantiate (1 := Emp). etransitivity. eassumption. generalize (denote rr).
      intros; cancel_all. unfold denote. simpl. 
      repeat (apply star_comm_p; repeat apply star_assoc_p; apply star_emp_p).
      unfold himp; simpl. cancel_all.
    Qed.
  
  End WithCS.

    Definition CancelSep : @SProverT types fs pcType stateType sfuncs.
(*
    red. refine (fun _ _ gl gr =>
      match hash gl , hash gr with
        | existT ql lhs , existT qr rhs =>
          match sepCancel gr lhs (SHeap_empty _) as k 
            return sepCancel gr lhs (SHeap_empty _) = k -> _ with
            | (lhs',rhs') => fun pf =>
              @existT _ _ (denote lhs', denote rhs') _
          end (eq_refl _)
      end).
      intros. etransitivity. 2: eapply sepCancel_cancels. 2: eassumption. 2: eauto.
      unfold lhs. etransitivity. eapply denote_hash_cc. unfold Himp, himp. reflexivity.
*)
    Admitted.

  End BabySep.

  (** Tests **)
  Section ProverTests.
    Require Import Arith.
    Variable pcType : Type.
    Variable stateType : Type.

    Definition types := 
      {| Impl := pcType ; Eq := fun _ _ => None |} ::
      {| Impl := stateType ; Eq := fun _ _ => None |} ::
      {| Impl := nat; Eq := fun x y => match eq_nat_dec x y with left Heq => Some Heq | _ => None end |} :: nil.

    Definition fs : functions types :=
       {| Domain := Some (FS (FS FO)) :: Some (FS (FS FO)) :: nil;
          Range := None; Denotation := eq |}
    :: {| Domain := (Some (FS (FS FO)) :: Some (FS (FS FO)) :: nil) : list (tvar types);
          Range := Some (FS (FS FO)); Denotation := plus |}
    :: nil.

    Definition pcTypeV : tvar types := Some FO.
    Definition stateTypeV : tvar types := Some (FS FO).

    Definition consts : list (PropX (tvarD pcTypeV) (tvarD stateTypeV)) := nil.
    Definition vars : variables types := nil.

    Parameter repr : nat -> ST.Hprop (tvarD pcTypeV) (tvarD stateTypeV).

    Variable stateMem : tvarD stateTypeV -> B.mem.
    Definition sfuncs : list (@ssignature types pcTypeV stateTypeV) :=
      {| SDomain := Some (FS (FS FO)) :: nil
       ; SDenotation := repr
         : functionTypeD (map (@tvarD types) (Some (FS (FS FO)) :: nil)) (ST.Hprop (tvarD pcTypeV) (tvarD stateTypeV))
       |} :: nil.

  Goal forall cs,
    Himp cs (@Func types fs pcTypeV stateTypeV sfuncs vars FO (HCons (Expr.Const fs vars (Some (FS (FS FO))) 1) HNil))
            (@Func types fs pcTypeV stateTypeV sfuncs vars FO (HCons (Expr.Const fs vars (Some (FS (FS FO))) 1) HNil)).
  Proof.
    intros.
    (*
    match goal with
      | [ |- Himp ?M ?C ?L ?R ] =>
        let R := fresh in
        let rr := eval hnf in (@CancelSep types fs pcTypeV stateTypeV M sfuncs C nil L R) in
        match rr with
          | existT _ ?PF => apply PF; unfold denote; simpl
        end
    end. unfold Himp, himp. reflexivity.
*)
    Admitted.
  End ProverTests.
  
  Section QSexpr.
    (** Guarded separation logic expressions **)
  End QSexpr.
*)
End SepExpr.

Require Export Expr.