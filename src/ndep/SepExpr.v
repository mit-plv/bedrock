Require Import List.
Require Import Bedrock.ndep.Expr.
Require Import Heaps SepTheoryX PropX.
Require Import PropXTac.
Require Import PMap.
Require Import RelationClasses.
Require Import EqdepClass.

Set Implicit Arguments.

Require Bedrock.ndep.NatMap.

Module FM := Bedrock.ndep.NatMap.IntMap.    

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

    Section SProver.
      Definition himp (U1 U2 G : env types)
        (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
        (gl gr : sexpr) : Prop :=
        match sexprD gl U1 G , sexprD gr U2 G with
          | Some l , Some r => ST.himp cs l r
          | _ , _ => False
        end.

      Definition heq (U1 U2 G : env types)
        (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
        (gl gr : sexpr) : Prop :=
        match sexprD gl U1 G , sexprD gr U2 G with
          | Some l , Some r => ST.heq cs l r
          | _ , _ => False
        end.

      Global Instance Trans_himp U g cs : Transitive (@himp U U g cs).
      Proof.
        red. unfold himp. intros x y z. 
        destruct (sexprD x U g);
        destruct (sexprD y U g);
        destruct (sexprD z U g); try intuition.
        etransitivity; eauto.
      Qed.

      Global Instance Trans_heq U g cs : Transitive (@heq U U g cs).
      Proof.
        red. unfold heq. intros x y z. 
        destruct (sexprD x U g);
        destruct (sexprD y U g);
        destruct (sexprD z U g); try intuition.
        etransitivity; eauto.
      Qed.

      Theorem ST_himp_himp : forall (U1 U2 G : env types) cs L R,
        himp U1 U2 G cs L R ->
        match sexprD L U1 G , sexprD R U2 G with
          | Some l , Some r => ST.himp cs l r
          | _ , _ => False
        end.
      Proof.
        clear. auto.
      Qed.

      Theorem ST_heq_heq : forall (U1 U2 G : env types) cs L R,
        heq U1 U2 G cs L R ->
        match sexprD L U1 G , sexprD R U2 G with
          | Some l , Some r => ST.heq cs l r
          | _ , _ => False
        end.
      Proof.
        clear. auto.
      Qed.
(*
      Section exists_subst.
        Variable U1 : env types.
        
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

      Lemma exists_subst_exists : forall a (A : hlist _ a) 
        b (B : hlist (fun t => option (expr funcs nil a t)) b) P,
        exists_subst A B P ->
        exists C, P C.
      Proof.
        clear. induction B; simpl; intros.
          eauto.
          destruct b. eapply IHB in H. destruct H; eauto.
          destruct H. eapply IHB in H. destruct H; eauto.
      Qed.


      Fixpoint forallEach (ls : variables types) : (hlist (@tvarD types) ls -> Prop) -> Prop :=
        match ls with
          | nil => fun cc => cc HNil
          | a :: b => fun cc =>
            forall x : tvarD a, forallEach (fun r => cc (HCons x r))
        end.

      Lemma forallEach_forall : forall ls (P : hlist (@tvarD types) ls -> Prop),
        forallEach P -> forall V, P V.
      Proof.
        induction ls; simpl; intros. 
        rewrite (hlist_nil_only _ V). auto.
        rewrite (hlist_eta _ V). 
        specialize (H (hlist_hd V)). eapply IHls in H. eassumption.
      Qed.
*)

      Record SepResult (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
        (gl gr : sexpr) : Type :=
      { lhs : sexpr
      ; rhs : sexpr
      ; SUBST : list (expr types)
      }.

      Definition SProverT : Type := forall
        (cs : codeSpec (tvarD types pcType) (tvarD types stateType)) 
        (hyps : list (expr types)) (** Pure Premises **)
        (gl gr : sexpr),
        SepResult cs gl gr.
    
    End SProver.


    Record SHeap : Type :=
    { impures : FM.t (list (list (expr types)))
    ; pures   : list (expr types)
    ; other   : list (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.
  
    Definition SHeap_empty : SHeap := 
      {| impures := FM.empty _
       ; pures   := nil
       ; other   := nil
       |}.

    Fixpoint liftSExpr (a b : nat) (s : sexpr) : sexpr :=
      match s with
        | Emp => Emp
        | Inj p => Inj (liftExpr a b p)
        | Star l r => Star (liftSExpr a b l) (liftSExpr a b r)
        | Exists t s => 
          Exists t (liftSExpr (S a) b s)
        | Func f xs => Func f (map (liftExpr a b) xs)
        | Const c => Const c
      end.

    Definition liftSHeap (a b : nat) (s : SHeap) : SHeap :=
    {| impures := FM.map (map (map (liftExpr a b))) (impures s)
     ; pures   := map (liftExpr a b) (pures s)
     ; other   := other s
     |}.

    Parameter star_SHeap : SHeap -> SHeap -> SHeap.

    Fixpoint hash (s : sexpr) : ( variables * SHeap ) :=
      match s with
        | Emp => (nil, SHeap_empty)
        | Inj p => (nil,
          {| impures := FM.empty _
            ; pures := p :: nil
            ; other := nil
          |})
        | Star l r =>
          let (vl, hl) := hash l in
          let (vr, hr) := hash r in
          (vl ++ vr,
           star_SHeap hl (liftSHeap 0 (length vl) hr))
        | Exists t b =>
          let (v,b) := hash b in
          (v ++ t :: nil, b)
        | Func f a =>
          (nil,
           {| impures := FM.add f (a :: nil) (FM.empty _)
            ; pures := nil
            ; other := nil
           |})
        | Const c => 
          (nil,
           {| impures := FM.empty _
            ; pures := nil
            ; other := c :: nil
            |})
      end.


    Definition starred (T : Type) (F : T -> sexpr) (ls : list T)
      : sexpr :=
      fold_right (fun x a => Star (F x) a) Emp ls.

    Definition denote (h : SHeap) :  sexpr :=
      let a := FM.fold (fun k ls acc => 
        Star (starred (Func k) ls) acc) (impures h) Emp in
      let c := starred (fun x => Inj x) (pures h) in
      let e := starred (fun x => Const x) (other h) in
      Star a (Star c e).

    Fixpoint existsEach (ls : list tvar) {struct ls} : sexpr -> sexpr :=
      match ls with
        | nil => fun x => x
        | t :: ts => fun y => @existsEach ts (Exists t y)
      end.

    Theorem hash_denote : forall cs G (s : sexpr), 
      heq nil nil G cs s 
        (@existsEach (fst (hash s)) (denote (snd (hash s)))).
    Proof.
      induction s; simpl.
        unfold denote; simpl. unfold FM.fold. simpl. admit.
        unfold denote; simpl. unfold FM.fold. simpl. admit.
    Admitted.

(*
    Definition liftFunctions uvars vars' ext vars
      : dmap (fin sfuncs) (fun f : fin sfuncs => list (hlist (expr funcs uvars (vars' ++ vars)) (SDomain (get sfuncs f)))) ->
        dmap (fin sfuncs) (fun f : fin sfuncs => list (hlist (expr funcs uvars (vars' ++ ext ++ vars)) (SDomain (get sfuncs f))))
      :=
      

      dmap_map _ _ _ (fun t' => @List.map _ _ (@hlist_map _ _ _ (liftExpr vars' ext vars) _)).

    Definition liftFunctionsU uvars' ext uvars vars
      : dmap (fin sfuncs) (fun f : fin sfuncs => list (hlist (expr funcs (uvars' ++ uvars) vars) (SDomain (get sfuncs f)))) ->
        dmap (fin sfuncs) (fun f : fin sfuncs => list (hlist (expr funcs (uvars' ++ ext ++ uvars) vars) (SDomain (get sfuncs f))))
      :=
      dmap_map _ _ _ (fun t' => @List.map _ _ (@hlist_map _ _ _ (liftExprU uvars' ext uvars (vars := vars)) _)).
*)

  End env.

End SepExpr.