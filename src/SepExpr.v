Require Import List.
Require Import Expr ExprUnify.
Require Import Heaps SepTheoryX PropX.
Require Import PropXTac.
Require Import PMap.
Require Import Classes.RelationClasses.
Require Import EqdepClass.

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
    | Inj : forall vars, expr funcs uvars vars None -> sexpr uvars vars
    | Star : forall vars, sexpr uvars vars -> sexpr uvars vars -> sexpr uvars vars
    | Exists : forall vars t, sexpr uvars (t :: vars) -> sexpr uvars vars
    | Func : forall vars (f : fin sfuncs), 
      hlist (expr funcs uvars vars) (SDomain (get sfuncs f)) -> sexpr uvars vars
      (* this Const can not mention the higher-order variables *)
    | Const : forall vars, ST.hprop (tvarD pcType) (tvarD stateType) nil -> sexpr uvars vars
    .

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
          ST.inj (PropX.Inj (exprD e g p)) 
        | Star _ l r => fun e g => 
          ST.star (sexprD l e g) (sexprD r e g)
        | Exists _ t b => fun e g => 
          ST.ex (fun x : tvarD t => @sexprD _ _ b e (HCons x g))
        | Func _ f b => fun e g =>
          applyD (exprD e g) b _ (SDenotation (get sfuncs f))
        | Const _ p => fun _ _ => p
      end.

    Section SProver.
      Definition himp u1 u2 (vars : variables types) (U1 : hlist (@tvarD _) u1) (U2 : hlist (@tvarD _) u2) (G : hlist (@tvarD _) vars) (cs : codeSpec (tvarD pcType) (tvarD stateType))
        (gl : sexpr u1 vars) (gr : sexpr u2 vars) : Prop :=
        ST.himp cs (sexprD gl U1 G) (sexprD gr U2 G).

      Definition heq u1 u2 (vars : variables types) (U1 : hlist (@tvarD _) u1) (U2 : hlist (@tvarD _) u2) (G : hlist (@tvarD _) vars) (cs : codeSpec (tvarD pcType) (tvarD stateType))
        (gl : sexpr u1 vars) (gr : sexpr u2 vars) : Prop :=
        ST.heq cs (sexprD gl U1 G) (sexprD gr U2 G).

      Global Instance Trans_himp u v U g cs : Transitive (@himp u u v U U g cs).
      Proof.
        red. intros. unfold himp. etransitivity; eauto.
      Qed.

      Global Instance Trans_heq u v U g cs : Transitive (@heq u u v U U g cs).
      Proof.
        red. intros. unfold heq. etransitivity; eauto.
      Qed.

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
      | Prove : forall u1 u2 (l : sexpr nil u1) (r : sexpr u2 u1)
        (U2 : hlist (fun t => option (expr funcs nil u1 t)) u2),
        
        (forall U1 : hlist (@tvarD _) u1, 
          @exists_subst _ U1 _ U2 (fun k => 
          ST.himp cs (sexprD l HNil U1) (sexprD r k U1) -> himp HNil HNil HNil cs gl gr))
        -> SepResult cs gl gr.

      Definition SProverT : Type := forall
        (cs : codeSpec (tvarD pcType) (tvarD stateType)) 
        (hyps : list (@expr types funcs nil nil None)) (** Pure Premises **)
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

  Section lift.
    Variable types : list type.
    Variable funcs : functions types.
    Variable pcType : tvar types.    
    Variable stateType : tvar types.
    Variable sfuncs : list (ssignature pcType stateType).

    Fixpoint liftSExpr uvars vars ext vars' (s : sexpr funcs sfuncs uvars (vars ++ vars')) 
      : sexpr funcs sfuncs uvars (vars ++ ext ++ vars') :=
      match s in sexpr _ _ _ vs 
        return vs = vars ++ vars' -> sexpr funcs sfuncs uvars (vars ++ ext ++ vars') with
        | Emp _ => fun _ => Emp
        | Inj _ p => fun pf => 
          Inj (liftExpr vars ext vars' match pf in _ = t return expr funcs uvars t None with
                                         | refl_equal => p
                                       end)
        | Star v' l r => fun pf => 
          Star 
            (liftSExpr vars ext vars' match pf in _ = t return sexpr funcs sfuncs uvars t with
                                        | refl_equal => l
                                      end) 
            (liftSExpr vars ext vars' match pf in _ = t return sexpr funcs sfuncs uvars t with
                                        | refl_equal => r
                                      end)
        | Exists v t b => fun pf => 
          let b := 
            match pf in _ = v' return sexpr funcs sfuncs uvars (t :: v') with
              | refl_equal => b
            end
          in
          Exists t (liftSExpr (t :: vars) ext vars' b)
        | Func v f a => fun pf =>
          let a :=
            match pf in _ = v' return hlist (expr funcs uvars v') (SDomain (get sfuncs f)) with
              | refl_equal => a
            end
          in
          Func f (@hlist_map (tvar types) (expr funcs uvars (vars ++ vars')) (expr funcs uvars (vars ++ ext ++ vars')) (fun _ e => liftExpr vars ext vars' e) _ a)
        | Const v p => fun _ => Const p
      end (refl_equal _).

    Lemma liftSExpr_nil : forall uvars vars vars' (s : sexpr funcs sfuncs uvars (vars ++ vars')),
      liftSExpr vars nil vars' s = s.
    Proof.
      Require Import Program. 
      dependent induction s; simpl; eauto. rewrite liftExpr_nil. auto. rewrite IHs1; eauto. rewrite IHs2; eauto.
      rewrite IHs; eauto.
      clear. f_equal. induction h; auto. simpl. f_equal. rewrite liftExpr_nil. auto. auto.
    Qed.

  End lift.

  Section BabySep.
    Variable types : list type.
    Variable fs : functions types.
    Variable pcType : tvar types.    
    Variable stateType : tvar types.
    Variable stateMem : tvarD stateType -> B.mem.
    Variable sfuncs : list (ssignature pcType stateType).
      
    Record SHeap uvars vars : Type :=
    { funcs  : @dmap (fin sfuncs) (fun f => list (hlist (expr fs uvars vars) (SDomain (get sfuncs f))))
    ; pures  : list (expr fs uvars vars None)
    ; other  : list (ST.hprop (tvarD pcType) (tvarD stateType) nil)
    }.
  
    Definition SHeap_empty uvars vars : SHeap uvars vars := 
      {| funcs := dmap_empty
       ; pures := nil
       ; other := nil
       |}.

    Definition starred u v (T : Type) (F : T -> sexpr fs sfuncs u v) (ls : list T)
      : sexpr fs sfuncs u v :=
      fold_right (fun x a => Star (F x) a) Emp ls.

    Definition denote uvars vars (h : SHeap uvars vars) :  sexpr fs sfuncs uvars vars :=
      let a := dmap_fold (fun a x y => fold_left (fun a y => Star (Func x y) a) y a) Emp (funcs h) in
      let c := starred (fun x => Inj x) (pures h) in
      let e := starred (fun x => Const x) (other h) in
      Star a (Star c e).

    Definition liftFunctions uvars vars' ext vars
      : dmap (fin sfuncs) (fun f : fin sfuncs => list (hlist (expr fs uvars (vars' ++ vars)) (SDomain (get sfuncs f)))) ->
        dmap (fin sfuncs) (fun f : fin sfuncs => list (hlist (expr fs uvars (vars' ++ ext ++ vars)) (SDomain (get sfuncs f))))
      :=
      dmap_map _ _ _ (fun t' => @List.map _ _ (@hlist_map _ _ _ (liftExpr vars' ext vars) _)).

    Definition liftFunctionsU uvars' ext uvars vars
      : dmap (fin sfuncs) (fun f : fin sfuncs => list (hlist (expr fs (uvars' ++ uvars) vars) (SDomain (get sfuncs f)))) ->
        dmap (fin sfuncs) (fun f : fin sfuncs => list (hlist (expr fs (uvars' ++ ext ++ uvars) vars) (SDomain (get sfuncs f))))
      :=
      dmap_map _ _ _ (fun t' => @List.map _ _ (@hlist_map _ _ _ (liftExprU uvars' ext uvars (vars := vars)) _)).

    Definition liftPures uvars vars' ext vars 
      : list (expr fs uvars (vars' ++ vars) None) -> list (expr fs uvars (vars' ++ ext ++ vars) None)
      := map (liftExpr vars' ext vars (T := None)).

    Definition liftPuresU uvars' ext uvars vars 
      : list (expr fs (uvars' ++ uvars) vars None) -> list (expr fs (uvars' ++ ext ++ uvars) vars None)
      := map (liftExprU uvars' ext uvars (vars := vars) (T := None)).

    Definition liftSHeap uvars vars ext vars' (s : SHeap uvars (vars ++ vars')) : SHeap uvars (vars ++ ext ++ vars') :=
      {| funcs := liftFunctions vars ext vars' (funcs s)
       ; pures := liftPures vars ext vars' (pures s)
       ; other := other s
       |}.

    Definition liftSHeapU uvars ext uvars' vars (s : SHeap (uvars ++ uvars') vars) 
      : SHeap (uvars ++ ext ++ uvars') vars :=
      {| funcs := liftFunctionsU uvars ext uvars' (funcs s)
       ; pures := liftPuresU uvars ext uvars' (pures s)
       ; other := other s
       |}.

    Definition join_SHeap uvars vars (l r : SHeap uvars vars) : SHeap uvars vars :=
      let add_all acc k v :=
        match dmap_remove (fun x y => Some (@finCmp _ sfuncs x y)) k acc with
          | None =>
            dmap_insert (fun x y => Some (@finCmp _ sfuncs x y)) k v acc 
          | Some (vs, acc) =>
            dmap_insert (fun x y => Some (@finCmp _ sfuncs x y)) k (v ++ vs) acc
        end
      in
      {| funcs := dmap_fold add_all (funcs l) (funcs r)
       ; pures := pures l ++ pures r
       ; other := other l ++ other r
       |}.

    Lemma list_app_assoc : forall T (a b c : list T), (a ++ b) ++ c = a ++ b ++ c.
    Proof.
      induction a; simpl; intros.
        reflexivity.
        rewrite IHa. reflexivity.
    Defined.

    Fixpoint sheapSubstEx uvars vars vars' t (s : SHeap uvars (vars ++ t :: vars')) :
      SHeap (t :: uvars) (vars ++ vars').
  Admitted.

    Fixpoint hash_right uvars vars ext (s : sexpr fs sfuncs uvars vars) :
      { es : variables types & SHeap (es ++ uvars) (ext ++ vars) } :=
      match s in sexpr _ _ _ vars 
        return { es : variables types & SHeap (es ++ uvars) (ext ++ vars) } with
        | Emp _ => @existT _ _ nil (SHeap_empty _ _)
        | Inj v p => @existT _ _ nil
          {| funcs := dmap_empty
           ; pures := liftExpr nil ext v p :: nil
           ; other := nil
           |}
        | Star v l r => 
          match hash_right ext l, hash_right ext r with
            | existT vl hl , existT vr hr =>
              @existT (variables types) (fun ls => SHeap (ls ++ uvars) (ext ++ v)) (vl ++ vr)
                (match eq_sym (list_app_assoc vl vr uvars) in _ = t return SHeap t (ext ++ v) with
                   | refl_equal => 
                     join_SHeap (@liftSHeapU vl vr uvars _ hl)
                                (@liftSHeapU nil vl (vr ++ uvars) _ hr)
                 end)
          end
        | Exists vs t b =>
          match hash_right ext b with
            | existT vl hl =>
              @existT _ _ (t :: vl) (sheapSubstEx _ _ _ hl)
          end              
        | Func v f a => 
          @existT _ _ nil
            {| funcs := dmap_insert (fun x y => Some (@finCmp _ sfuncs x y)) f
                          (hlist_map (expr fs (nil ++ uvars) (ext ++ v))
                             (fun (x : tvar types) (X : expr fs uvars v x) =>
                              liftExpr nil ext v X) a :: nil) dmap_empty
             ; pures := nil
             ; other := nil
             |}
        | Const v c => 
          @existT _ _ nil
            {| funcs := dmap_empty
             ; pures := nil
             ; other := c :: nil
             |}
      end.
    
    Fixpoint hash_left uvars vars (s : sexpr fs sfuncs uvars vars) :
      { es : variables types & SHeap uvars (es ++ vars) } :=
      match s in sexpr _ _ _ vars return { es : variables types & SHeap uvars (es ++ vars) } with
        | Emp _ => @existT _ _ nil (SHeap_empty _ _)
        | Inj _ p => @existT _ _ nil
          {| funcs := dmap_empty
           ; pures := p :: nil
           ; other := nil
           |}
        | Star vs l r =>
          match hash_left l, hash_left r with
            | existT vl hl , existT vr hr =>
              @existT _ _ (vl ++ vr)
                (match eq_sym (list_app_assoc vl vr vs) in _ = t return SHeap _ t with
                   | refl_equal => 
                     join_SHeap (liftSHeap _ _ _ hl) (@liftSHeap uvars nil _ _ hr)
                 end)
          end
        | Exists vs t b =>
          match hash_left b with
            | existT v b =>
              @existT _ _ (v ++ t :: nil) 
              match eq_sym (list_app_assoc v (t :: nil) vs) in _ = t return SHeap _ t with
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

    Section Reasoning.
      Variable cs : codeSpec (tvarD pcType) (tvarD stateType).

      Lemma heq_subst : forall a b A B C (P Q R S : sexpr fs sfuncs a b),
        heq A A C cs S P ->
        heq A B C cs (Star P Q) R ->
        heq A B C cs (Star S Q) R.
      Proof.
        unfold heq. simpl. intros. eapply ST.heq_subst; eauto. 
      Qed.

      Global Instance Sym_heq : forall A B G G',
        Symmetric (@heq _ fs _ _ sfuncs A A B G G G' cs).
      Proof.
        unfold heq, Symmetric. intros. symmetry. auto.
      Qed.

      Global Instance Refl_heq : forall A B G G',
        Reflexive (@heq _ fs _ _ sfuncs A A B G G G' cs).
      Proof.
        unfold heq, Reflexive. intros. reflexivity.
      Qed.

      Lemma heq_star_assoc : forall a b A B C (P Q R S : sexpr fs sfuncs a b),
        heq A B C cs (Star P (Star Q S)) R ->
        heq A B C cs (Star (Star P Q) S) R.
      Proof.
        unfold heq. simpl. intros. eapply ST.heq_star_assoc. auto.
      Qed.

      Lemma heq_star_comm : forall a b A B C (P Q R : sexpr fs sfuncs a b),
        heq A B C cs (Star P Q) R ->
        heq A B C cs (Star Q P) R.
      Proof.
        unfold heq. simpl. intros. eapply ST.heq_star_comm. auto.
      Qed.

      Lemma heq_star_frame : forall a b X Y (P Q R S : sexpr fs sfuncs a b),
        heq X X Y cs P R ->
        heq X X Y cs Q S ->
        heq X X Y cs (Star P Q) (Star R S).
      Proof.
        clear. unfold heq. intros. simpl. eapply ST.heq_star_frame; eauto.
      Qed.

      Lemma heq_star_emp : forall a c A C (P Q : sexpr fs sfuncs a c), 
        heq A A C cs P Q -> 
        heq A A C cs (Star Emp P) Q.
      Proof.
        clear. unfold heq. intros. simpl. eapply ST.heq_star_emp; eauto.
      Qed.

      Lemma heq_ex : forall t a b A B C (P Q : sexpr fs sfuncs a (t :: b)), 
        (forall v, heq A B (HCons v C) cs P Q) ->
        heq A B C cs (Exists t P) (Exists t Q).
      Proof.
        unfold heq. simpl. intros. eapply ST.heq_ex. eauto.
      Qed.

      Fixpoint existsEach (uvars vars vars' : variables types) {struct vars}
        : sexpr fs sfuncs uvars (vars ++ vars') -> sexpr fs sfuncs uvars (vars') :=
        match vars as vars return sexpr fs sfuncs uvars (vars ++ vars') -> sexpr fs sfuncs uvars vars' with
          | nil => fun x => x
          | a :: b => fun y => @existsEach uvars _ vars' (Exists _ y)
        end.

      Parameter existsEachU : forall (uvars vars : variables types),
        sexpr fs sfuncs uvars vars -> sexpr fs sfuncs nil vars.

      Lemma existsEach_heq : forall u v v' X Y (P Q : sexpr fs sfuncs u (v ++ v')),
        (forall Z, heq X X (hlist_app Z Y) cs P Q) ->
        heq X X Y cs (existsEach v _ P) (existsEach v _ Q).
      Proof.
        induction v; simpl; intros.
        eapply H. econstructor.
        eapply IHv. intros. eapply heq_ex. intros; specialize (H (HCons v0 Z)).
        simpl in *. auto.
      Qed.

      Lemma hlist_app_assoc : forall F (a b c : variables types) (A : hlist F a) (B : hlist F b) (C : hlist F c),
        hlist_app (hlist_app A B) C = 
        match app_assoc a b c in _ = t return hlist F t with
          | refl_equal => hlist_app A (hlist_app B C)
        end.
      Proof.
        induction a; simpl. auto.
          intros; uip_all. simpl in *. generalize e; uip_all. reflexivity.
          intros. rewrite IHa. clear. generalize (hlist_app (hlist_tl A) (hlist_app B C)).
          generalize (hlist_hd A). uip_all. simpl in *. generalize e e0 h. uip_all. reflexivity.
      Qed.

      Lemma existsEach_peel_back : forall uvars x r t
        (P : sexpr fs sfuncs uvars ((x ++ t :: nil) ++ r)),
        existsEach (x ++ t :: nil) r P = 
        Exists t (existsEach x (t :: r) match app_ass _ _ _ in _ = t return sexpr _ _ _ t with
                                          | refl_equal => P
                                        end).
      Proof.
        clear. induction x; simpl; intros.
          uip_all. simpl in *. uip_all. reflexivity.
          rewrite IHx. f_equal. f_equal. uip_all. simpl in *. generalize P e e0.
          clear IHx P. unfold app in *. rewrite e0. uip_all. reflexivity.
      Qed.

      Lemma existsEach_app : forall u a b c X Y (P : sexpr fs sfuncs u (b ++ a ++ c)),
        heq X X Y cs (existsEach a c (existsEach b (a ++ c) P))
                     (existsEach (b ++ a) c match eq_sym (app_ass b a c) in _ = t 
                                              return sexpr _ _ _ t with
                                              | refl_equal => P
                                            end).
      Proof.
        clear. induction a. simpl. induction b; simpl.
          intros. uip_all. reflexivity.
          intros. etransitivity. eapply (@IHb _ _ _ (Exists a P)).
          clear. uip_all. generalize P e e0. uip_all. reflexivity.
          simpl. intros.
          assert (b ++ a :: a0 ++ c = (b ++ a :: nil) ++ a0 ++ c).
            clear. rewrite app_ass. reflexivity.
          specialize (IHa (b ++ a :: nil) c X Y 
            match H in _ = t return sexpr fs sfuncs u t with
              | refl_equal => P
            end).
          etransitivity. etransitivity. 2: eapply IHa. clear.
          eapply existsEach_heq; intros. symmetry. rewrite existsEach_peel_back.
          intros. uip_all.
          match goal with
            | [ |- heq _ _ ?H _ _ _ ] => generalize H
          end. clear. generalize H e. uip_all. simpl in *. uip_all. reflexivity.

          clear. generalize P H. uip_all. generalize e e0 Y P0.
          uip_all. clear. generalize Y0 e1 P1. clear. 
          cutrewrite ((b ++ a :: nil) ++ a0 = b ++ a :: a0). uip_all. reflexivity.
          rewrite app_ass. reflexivity.
      Qed.

      Lemma liftSExpr_denote : forall uvars vars' vs vars (e : sexpr fs sfuncs uvars (vars' ++ vars)) U G G' G'', 
        ST.heq cs (sexprD (liftSExpr vars' vs vars e) U (hlist_app G (hlist_app G' G''))) (sexprD e U (hlist_app G G'')).
      Proof.
        clear. intros. 
          assert (forall k (e : sexpr fs sfuncs uvars k) (E : k = vars' ++ vars), 
            ST.heq cs
            (sexprD (liftSExpr vars' vs vars match E in _ = t return sexpr _ _ _ t with
                                              | refl_equal => e
                                            end) U (hlist_app G (hlist_app G' G'')))
            (sexprD match E in _ = t return sexpr _ _ _ t with
                     | refl_equal => e 
            end U (hlist_app G G''))).
          2: apply (H _ e eq_refl).
          clear. intros k e. revert vars' G. 
          induction e; simpl; intros; 
            try solve [ generalize E; uip_all; simpl; reflexivity ].
            Focus.
            generalize E e; uip_all. simpl. f_equal. rewrite liftExpr_denote.
              reflexivity.
            Focus.
            specialize (IHe1 _ G E). specialize (IHe2 _ G E).
              generalize IHe1 IHe2. clear IHe1 IHe2.
              generalize E e1 e2. uip_all.
              rewrite (UIP_refl E0) in IHe1. rewrite (UIP_refl E0) in IHe2.
              simpl. eapply ST.heq_star_frame; auto.
           Focus.
           generalize E. generalize dependent e. uip_all. simpl.
             eapply ST.heq_ex. intros.
             specialize (IHe (t :: vars') (HCons v G) refl_equal). simpl in *.
             eauto.
           Focus.
           generalize E f h. uip_all. clear.
             simpl. destruct (get sfuncs f0); simpl in *.
            generalize dependent SDomain0. induction SDomain0.
            intros. rewrite (hlist_nil_only _ h0). simpl. eapply ST.Refl_heq.
            intros. rewrite (hlist_eta _ h0) in *. simpl in *.
            specialize (IHSDomain0 (SDenotation0 (exprD U (hlist_app G G'') (hlist_hd h0))) (hlist_tl h0)).
            generalize (liftExpr_denote (hlist_hd h0) U G G' G'').
            unfold tvar in *. intros. rewrite H. auto.
      Qed.

      Lemma lift_exists_star : forall uvars z Q t A C
        (P : sexpr fs sfuncs uvars (t :: z)),
        heq A A C cs (Star (Exists t P) Q)
                     (Exists t (Star P (liftSExpr nil (t :: nil) z Q))).
      Proof.
        clear. induction Q; simpl; intros; 
          try solve [ reflexivity | unfold heq; simpl; apply ST.heq_ex_star ].

          Focus.
          unfold heq. simpl. etransitivity. eapply ST.heq_ex_star.
            eapply ST.heq_ex. intros. eapply ST.heq_star_frame. reflexivity.
            generalize (@liftExpr_denote _ _ _ nil _ _ _ e A HNil (HCons v HNil) C).
            simpl. intro. rewrite <- H. reflexivity.

          etransitivity. etransitivity. 2: eapply heq_star_frame. 2: eapply IHQ1.
            instantiate (1 := Q2). instantiate (1 := P). 
            symmetry. apply heq_star_assoc. reflexivity.
            reflexivity. etransitivity. eapply IHQ2. apply heq_ex. intros.
            apply heq_star_assoc. reflexivity.
            
          Focus.
          etransitivity. 
            instantiate (1 := 
              Exists t (Exists t0 (Star (liftSExpr (t0 :: nil) (t :: nil) vars P)
                (liftSExpr nil (t0 :: nil) (t :: vars) Q)))).
            apply heq_star_comm. unfold heq. simpl. etransitivity. apply ST.heq_ex_star.
            eapply ST.heq_ex. intros; apply ST.heq_star_comm.
            unfold heq in IHQ. simpl in *. 
            specialize (IHQ t0 A (HCons v C) (liftSExpr (t0 :: nil) (t :: nil) vars P)).
            etransitivity. etransitivity. 2: eapply IHQ.
            eapply ST.heq_star_frame. eapply ST.heq_ex. intro.
            generalize (@liftSExpr_denote _ (t0 :: nil) (t :: nil) vars P A (HCons v0 HNil) (HCons v HNil) C). simpl. symmetry. auto. reflexivity. reflexivity.

            unfold heq; simpl. clear. split.
              do 2 (apply ST.himp_ex_p; intros);
                eapply ST.himp_ex_c. exists v0. eapply ST.himp_star_frame.
                destruct (@liftSExpr_denote uvars (t0 :: nil) (t :: nil) vars P
                  A (HCons v0 HNil) (HCons v HNil) C).
                simpl in *. auto.
                apply ST.himp_ex_c. exists v. 
                destruct (@liftSExpr_denote uvars nil (t0 :: nil) (t :: vars) Q 
                  A HNil (HCons v0 HNil) (HCons v C)).
                simpl in *. etransitivity. eapply H.
                destruct (@liftSExpr_denote uvars (t :: nil) (t0 :: nil) vars Q 
                  A (HCons v HNil) (HCons v0 HNil) C); simpl in *.
                eapply H2.

              apply ST.himp_ex_p; intros. etransitivity.
                eapply ST.himp_star_comm_p. apply ST.himp_ex_star.
                eapply ST.himp_ex_p. intros. eapply ST.himp_ex_c. exists v0.
                eapply ST.himp_ex_c. exists v. apply ST.himp_star_comm_p.
                apply ST.himp_star_frame.

              destruct (@liftSExpr_denote uvars (t0 :: nil) (t :: nil) vars P
                A (HCons v HNil) (HCons v0 HNil) C). auto.
              destruct (@liftSExpr_denote uvars nil (t0 :: nil) (t :: vars) Q 
                A HNil (HCons v HNil) (HCons v0 C)).
              destruct (@liftSExpr_denote uvars (t :: nil) (t0 :: nil) vars Q 
                A (HCons v0 HNil) (HCons v HNil) C); simpl in *.
              etransitivity. eassumption. eauto.

          Focus.
          unfold heq; simpl. etransitivity. eapply ST.heq_ex_star.
            eapply ST.heq_ex. intros. eapply ST.heq_star_frame; try reflexivity.

            clear. destruct (get sfuncs f); simpl in *.
            generalize dependent SDomain0. induction SDomain0.
            intros. rewrite (hlist_nil_only _ h). simpl. eapply ST.Refl_heq.
            intros. rewrite (hlist_eta _ h) in *. simpl in *.
            specialize (IHSDomain0 (SDenotation0 (exprD A C (hlist_hd h))) (hlist_tl h)).
            generalize (@liftExpr_denote _ _ _ nil (t :: nil) vars a (hlist_hd h) A HNil (HCons v HNil) C).
            simpl. intro. unfold tvar in *. rewrite H. auto.
      Qed.

      Lemma liftSExpr_liftSExpr_app : forall uvars x y z a
        (P : sexpr fs sfuncs uvars (x ++ z)),
        (liftSExpr x y (a ++ z) (liftSExpr x a z P)) = 
        (match app_ass _ _ _ in _ = t return sexpr _ _ _ (x ++ t) with
           | refl_equal => liftSExpr x (y ++ a) z P
         end).
      Proof.
        clear. intros. uip_all.
        assert (forall e' (P : sexpr fs sfuncs uvars e') (E : e' = x ++ z),
          liftSExpr x y (a ++ z) (liftSExpr x a z match E in _ = t return sexpr _ _ _ t with
                                                    | refl_equal => P
                                                  end) =
          match e in _ = t return sexpr _ _ _ (x ++ t) with
            | refl_equal => liftSExpr x (y ++ a) z match E in _ = t return sexpr _ _ _ t with
                                                     | refl_equal => P
                                                   end
          end).
        clear. do 2 intro. generalize dependent x. generalize dependent y.
        induction P; intros; simpl; uip_all; subst.
          generalize e. simpl. uip_all. reflexivity.
          simpl. rewrite liftExpr_liftExpr_app. uip_all. generalize e0 e1.
          rewrite <- e1. uip_all. reflexivity.
          simpl. specialize (IHP1 _ e _ refl_equal). specialize (IHP2 _ e _ refl_equal).
          simpl in *. rewrite IHP1. rewrite IHP2. clear. generalize e. rewrite <- e. uip_all.
          reflexivity.
          subst. specialize (IHP _ e (t :: x) refl_equal). simpl in *.
          rewrite IHP. clear. generalize e. rewrite <- e. uip_all. reflexivity.

          simpl. rewrite liftExpr_liftExpr_apps. uip_all. generalize e e0. rewrite <- e.
          uip_all. reflexivity.

          simpl. generalize e; uip_all. reflexivity.
          eapply (H _ P refl_equal).
      Qed.

      Lemma lift_existsEach_star : forall uvars x z A C
        (P : sexpr fs sfuncs uvars (x ++ z)) Q,
        heq A A C cs (Star (existsEach x z P) Q)
                     (existsEach x _ (Star P (liftSExpr nil x z Q))).
      Proof.
        intros uvars x.
        induction x. simpl. intros; rewrite liftSExpr_nil. reflexivity.

        intros. simpl. etransitivity. eapply IHx.
          eapply existsEach_heq. intros.
          simpl in *.
          etransitivity. eapply lift_exists_star. eapply heq_ex. intros.
          eapply heq_star_frame. reflexivity. rewrite liftSExpr_liftSExpr_app.
          uip_all. simpl in *. generalize e. uip_all. reflexivity.
      Qed.

      Lemma liftSExpr_existsEach : forall uvars x y z (P : sexpr fs sfuncs uvars _),
        liftSExpr nil x z (existsEach y z P) = 
        existsEach y (x ++ z) (liftSExpr y x z P).
      Proof.
        induction y; simpl; auto.
          intros. rewrite IHy. f_equal.
      Qed.

      Lemma lift_existsEach_existsEach_star : forall uvars x y z A C (P : sexpr fs sfuncs uvars (x ++ z))  Q,
        heq A A C cs (Star (existsEach x z P) (existsEach y z Q))
        (existsEach x _ (existsEach y _ (Star (liftSExpr nil y (x ++ z) P) (liftSExpr y x z Q)))).
      Proof.
        clear. intros.
          etransitivity. eapply lift_existsEach_star. eapply existsEach_heq.
          intros. unfold heq; simpl. rewrite liftSExpr_existsEach.
          match goal with
            | [ |- ?G ] => change G with (heq A A (hlist_app Z C) cs (Star P (existsEach y (x ++ z) (liftSExpr y x z Q))) (existsEach y (x ++ z) (Star (liftSExpr nil y (x ++ z) P) (liftSExpr y x z Q))))
          end.
          apply heq_star_comm. etransitivity. apply lift_existsEach_star.
          eapply existsEach_heq. intros. apply heq_star_comm. reflexivity.
      Qed.

      Lemma lift_denote_lift : forall u a b c (s : SHeap u (a ++ c)) X Y,
        heq X X Y cs (liftSExpr a b c (denote s)) (denote (liftSHeap a b c s)).
      Proof. Admitted.

      Lemma starred_Star : forall u v T (F : T -> sexpr fs sfuncs u v) a b X Y,
        heq X X Y cs (starred F (a ++ b)) (Star (starred F a) (starred F b)).
      Proof.
        clear. induction a; simpl.
          intros. symmetry. apply heq_star_emp. reflexivity.
          intros. symmetry. apply heq_star_assoc. apply heq_star_frame. reflexivity.
          symmetry. eauto.
      Qed.

       Ltac cancel_heq :=
         repeat apply heq_star_assoc;
           symmetry; (repeat apply heq_star_assoc; 
             (apply heq_star_frame; [ reflexivity | ]) || apply heq_star_comm).

      Lemma denote_join : forall a b (P Q : SHeap a b) X Y,
        heq X X Y cs (denote (join_SHeap P Q)) (Star (denote P) (denote Q)).
      Proof.
        clear. unfold join_SHeap. destruct P; destruct Q; simpl in *. 
        unfold denote; simpl. intros. etransitivity.
        instantiate (1 := Star
          (Star (dmap_fold
            (fun (a0 : sexpr fs sfuncs a b) (x : fin sfuncs)
               (y : list (hlist (expr fs a b) (SDomain (get sfuncs x)))) =>
             fold_left
               (fun (a1 : sexpr fs sfuncs a b)
                  (y0 : hlist (expr fs a b) (SDomain (get sfuncs x))) =>
                Star (Func x y0) a1) y a0) Emp funcs0)
          (dmap_fold
            (fun (a0 : sexpr fs sfuncs a b) (x : fin sfuncs)
               (y : list (hlist (expr fs a b) (SDomain (get sfuncs x)))) =>
             fold_left
               (fun (a1 : sexpr fs sfuncs a b)
                  (y0 : hlist (expr fs a b) (SDomain (get sfuncs x))) =>
                Star (Func x y0) a1) y a0) Emp funcs1))
          (Star (Star (fold_right
               (fun (x : expr fs a b None) (a0 : sexpr fs sfuncs a b) =>
                Star (Inj x) a0) Emp pures0) (fold_right
               (fun (x : expr fs a b None) (a0 : sexpr fs sfuncs a b) =>
                Star (Inj x) a0) Emp pures1))
          (Star (fold_right
               (fun (x : ST.hprop (tvarD pcType) (tvarD stateType) nil)
                 (a0 : sexpr fs sfuncs a b) => Star (Const x) a0) Emp other0)
          (fold_right
            (fun (x : ST.hprop (tvarD pcType) (tvarD stateType) nil)
              (a0 : sexpr fs sfuncs a b) => Star (Const x) a0) Emp other1)))).
       Focus 2.
       repeat (reflexivity || cancel_heq). 
        apply heq_star_frame; [ | apply heq_star_frame ]; try eapply starred_Star.
        (** TODO: this is the annoying case **)

      Admitted.

      Lemma heq_change_dom : forall b c (E : b = c) a (A : hlist _ a) (B : hlist _ b) P Q,
        heq A A match E in _ = t return hlist _ t with
                  | refl_equal => B
                end cs
                match E in _ = t return sexpr fs sfuncs _ t with
                  | refl_equal => P
                end
                match E in _ = t return sexpr _ _ _ t with
                  | refl_equal => Q
                end ->
        heq A A B cs P Q.
      Proof.
        clear. intros. subst. auto.
      Qed.

      Lemma star_cast_cancel : forall a b c P Q (E : b = c) (E' : c = b),
        match E in _ = t return sexpr fs sfuncs a t with
          | refl_equal => 
            Star match E' in _ = t return sexpr _ _ _ t with
                   | refl_equal => P
                 end
            match E' in _ = t return sexpr _ _ _ t with
              | refl_equal => Q
            end
        end = Star P Q.
      Proof.
        clear. intros. generalize E E'. rewrite E. uip_all. auto.
      Qed.

      Lemma cast_cast_cancel : forall T (F : T -> Type) (a b : T) (E : a = b) (E' : b = a) x,
        EqDec T (@eq T) ->
        match E in _ = t return F t with
          | refl_equal => match E' in _ = t return F t with
                            | refl_equal => x
                          end
        end = x.
      Proof.
        intros. generalize E E'. uip_all. reflexivity.
      Qed.

      Lemma denote_cast_cancel : forall a b c P (E : b = c) (E' : c = b),
        match E in _ = t return sexpr fs sfuncs a t with
          | refl_equal => 
            denote match E' in _ = t return SHeap _ t with
                     | refl_equal => P
                   end
        end = denote P.
      Proof.
        clear. intros. generalize E E'. rewrite E. uip_all. auto.
      Qed.

      Theorem denote_hash_left : forall G (s : sexpr fs sfuncs _ _), 
        heq HNil HNil G cs s 
          (@existsEach _ (projT1 (@hash_left _ _  s)) nil (denote (projT2 (hash_left s)))).
      Proof.
        clear. induction s; 
          try solve [ simpl; intros; unfold denote; simpl;
            unfold heq; simpl; symmetry; 
              do 10 (apply ST.heq_star_emp || (try apply ST.heq_star_comm)); reflexivity ].
          (** Star **)
          Focus.
          intros. eapply heq_subst. eapply IHs1. eapply heq_star_comm. eapply heq_subst.
            eapply IHs2. clear IHs2 IHs1.
            simpl. destruct (hash_left s1). destruct (hash_left s2). simpl.
            etransitivity. eapply lift_existsEach_existsEach_star. etransitivity.
            eapply existsEach_app. 
            uip_all. eapply existsEach_heq. intros. generalize (hlist_app Z G). clear.
            intros. apply (heq_change_dom (eq_sym e)).
            rewrite cast_cast_cancel; eauto with typeclass_instances.
            rewrite denote_cast_cancel.

            etransitivity. 2: symmetry; eapply denote_join.
            apply heq_star_comm. apply heq_star_frame; try apply lift_denote_lift.
            apply (@lift_denote_lift _ nil x (x0 ++ vars) s0 HNil
              match eq_sym e in _ = t return hlist _ t with
                | refl_equal => h
              end).

          (** Exists **)
          Focus.
          intros. simpl. destruct (hash_left s); simpl in *.
            rewrite existsEach_peel_back. eapply heq_ex. intros.
            etransitivity. eapply IHs. eapply existsEach_heq. intros.
            uip_all. generalize e e0. simpl in *. uip_all. unfold eq_rect_r, eq_rect; simpl.
            reflexivity.

          (** Func **)
          Focus.
          simpl. unfold denote. simpl. unfold heq. symmetry. simpl.
            apply ST.heq_star_comm. apply ST.heq_star_assoc. 
            repeat apply ST.heq_star_emp. apply ST.heq_star_comm. apply ST.heq_star_emp.
            reflexivity.
      Qed.

(* TODO : Important!
      Theorem denote_hash_right : forall ext G (s : sexpr fs sfuncs _ _), 
        heq HNil HNil G cs 
          (liftSExpr _ _ _ s)
          (@existsEach _ (projT1 (@hash_right _ _ s)) nil (denote (projT2 (hash_right s)))).
      Admitted.
*)

      (** TODO: This can be more efficient if they are sorted b/c I can do a merge elim **)
      (** This is the simplest cancelation procedure, it just cancels functions in which
       ** the arguments unify pointwise
       **)
      Definition sepCancel_refl_func uL uR vars (f : fin sfuncs)
        (r : hlist (expr fs uR vars) (SDomain (get sfuncs f)))
        : list (hlist (expr fs uL vars) (SDomain (get sfuncs f))) ->
        ExprUnify.Subst fs uR uL vars ->
        option (list (hlist (expr fs uL vars) (SDomain (get sfuncs f))) * ExprUnify.Subst fs uR uL vars).
      refine (fix find (l : list (hlist (expr fs uL vars) (SDomain (get sfuncs f)))) 
        : ExprUnify.Subst fs uR uL vars ->
        option (list (hlist (expr fs uL vars) (SDomain (get sfuncs f))) * ExprUnify.Subst fs uR uL vars) := 
        match l with
          | nil => fun _ => None
          | l :: lr => fun s =>
            match exprUnifyArgs r l s with
              | None => match find lr s with
                          | None => None
                          | Some (k,v) => Some (l :: k, v)
                        end
              | Some s => Some (lr, s)
            end
        end).
    Defined.
    
    Definition sepCancel_refl_funcs uL uR vars (f : fin sfuncs) : forall
      (rs : list (hlist (expr fs uR vars) (SDomain (get sfuncs f))))
      (ls : list (hlist (expr fs uL vars) (SDomain (get sfuncs f)))),
        ExprUnify.Subst fs uR uL vars ->
        list (hlist (expr fs uL vars) (SDomain (get sfuncs f))) *
        list (hlist (expr fs uR vars) (SDomain (get sfuncs f))) *
        ExprUnify.Subst fs uR uL vars.
    refine (fix run rs ls s : 
      list (hlist (expr fs uL vars) (SDomain (get sfuncs f))) *
      list (hlist (expr fs uR vars) (SDomain (get sfuncs f))) *
      ExprUnify.Subst fs uR uL vars :=
      match rs with
        | nil => (ls, rs, s)
        | r :: rs =>
          match sepCancel_refl_func f r ls s with
            | None => 
              let '(ls,rs,s) := run rs ls s in
              (ls, r :: rs, s)
            | Some (ls', s) =>
              run rs ls' s
          end
      end).
    Defined.


    Definition sepCancel uL uR vars (l : SHeap uL vars) (r : SHeap uR vars) : 
      SHeap uL vars * SHeap uR vars * ExprUnify.Subst fs uR uL vars.
    Admitted.

    End Reasoning.

    Definition CancelSep : @SProverT types fs pcType stateType sfuncs.
    red. refine (fun cs _ gl gr =>
    match hash_left gl with
      | existT ql lhs =>
        match @hash_right _ _ ql gr with
          | existT qr rhs =>
            match eq_sym (app_nil_r ql) in _ = t, eq_sym (app_nil_r qr) in _ = t' 
              return forall (l : SHeap nil t) (r : SHeap t' t), _
              with
              | refl_equal , refl_equal => fun lhs rhs => 
                let '(lhs',rhs',s') := sepCancel lhs rhs in
                (** TODO: I need to maintain the connection between 
                 ** hash_left, hash_right and lhs and rhs
                 **)
                @Prove _ fs _ _ sfuncs _ gl gr ql qr (denote lhs') (denote rhs')
                  (env_of_Subst s' qr) _
            end lhs rhs
        end
    end).
    admit.
    Defined.
  

  End BabySep.


  (** Reflection Tactics **)
  (************************)
  Require Import Reflect.

  Ltac collectTypes_sexpr s types :=
    match s with
      | @ST.emp _ _ _ => types
      | @ST.inj _ _ _ (PropX.Inj _ _ _ ?P) =>
        collectTypes_sexpr P types
      | @ST.inj _ _ _ ?PX => types
      | @ST.star _ _ _ ?L ?R =>
        let L := collectTypes_sexpr L types in
        let R := collectTypes_sexpr R L in
        R
      | @ST.ex _ _ _ ?T ?B =>
        (** TODO: How do I peek inside B so that I can reflect the body... 
         ** - I might need to CPS this so that I can do some fresh name generation in tactics...
         **)
        types
      | ?X =>
        let rec bt_args args types :=
          match args with
            | tt => types
            | (?a,?b) => 
              let k := Expr.collectTypes_expr a types in
              bt_args b k
          end
        in
        let cc _ Ts args := 
          let types := append_uniq Ts types in
          let types := bt_args args types in
          types
        in
        refl_app cc X
    end.


  (** Just a test separation logic predicate **)
  Section Tests.
    Variable f : forall a b, nat -> ST.hprop a b nil.
    Variable g : bool -> nat -> nat -> nat.

    Goal forall a b c d x, @ST.himp a b c (f _ _ (g d (x + x) x)) (f _ _ x).
      intros.
      match goal with
        | [ |- @ST.himp _ _ _ ?L ?R ] =>
          let r := constr:(@nil Type) in
          let lt := collectTypes_sexpr L r in
          let rt := collectTypes_sexpr R lt in
          idtac rt
      end.
    Abort.
  End Tests.

End SepExpr.

Require Export Expr.

