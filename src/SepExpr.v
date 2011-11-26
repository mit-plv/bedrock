Require Import List.
Require Import Expr ExprUnify.
Require Import Heaps SepTheoryX PropX.
Require Import PropXTac.
Require Import PMap.
Require Import Classes.RelationClasses.
Require Import Eqdep_dec.

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

    Lemma UIP_vars : forall (x y:variables types) (p1 p2:x = y), p1 = p2.
    Proof.
      eapply UIP_dec.
      intros. eapply list_eq_dec. eapply tvar_dec.
    Qed.
      
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

    Definition denote uvars vars (h : SHeap uvars vars) :  sexpr fs sfuncs uvars vars :=
      let a := dmap_fold (fun a x y => fold_left (fun a y => Star (Func x y) a) y a) Emp (funcs h) in
      let c := fold_right (fun x a => Star (Inj x) a) Emp (pures h) in
      let e := fold_right (fun x a => Star (Const x) a) Emp (other h) in
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

    Fixpoint hash_right uvars vars ext (s : sexpr fs sfuncs uvars vars) :
      { es : variables types & SHeap (es ++ uvars) (ext ++ vars) }.
    Admitted.

    Lemma list_app_assoc : forall T (a b c : list T), (a ++ b) ++ c = a ++ b ++ c.
    Proof.
      induction a; simpl; intros.
        reflexivity.
        rewrite IHa. reflexivity.
    Defined.
    
    Fixpoint hash_left uvars vars (s : sexpr fs sfuncs uvars vars) :
      { es : variables types & SHeap uvars (es ++ vars) }.
refine (
      match s in sexpr _ _ _ vars return { es : variables types & SHeap uvars (es ++ vars) } with
        | Emp _ => @existT _ _ nil (SHeap_empty _ _)
        | Inj _ p => @existT _ _ nil
          {| funcs := dmap_empty
           ; pures := p :: nil
           ; other := nil
           |}
        | Star vs l r =>
          match hash_left _ _ l, hash_left _ _ r with
            | existT vl hl , existT vr hr =>
              @existT _ _ (vl ++ vr)
                (join_SHeap _ _)
          end
        | Exists vs t b =>
          match hash_left _ _ b with
            | existT v b =>
              @existT _ _ _ _ (*(fun x : list (tvar types) => SHeap x vs) (v ++ t :: nil) _*)
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
(*        | _ => @existT _ _ nil {| funcs := dmap_empty
                                ; pures := nil
                                ; other := nil
                                |}
*)
      end).
    rewrite list_app_assoc. eapply liftSHeap. assumption.
    change (SHeap uvars (nil ++ (vl ++ vr) ++ vs)).
    rewrite list_app_assoc. eapply liftSHeap. assumption.
    instantiate (1 := v ++ t :: nil). rewrite list_app_assoc. simpl. assumption.
    Defined.

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

      Lemma heq_ex : forall t a b A B C (P Q : sexpr fs sfuncs a (t :: b)), 
        (forall v, heq A B (HCons v C) cs P Q) ->
        heq A B C cs (Exists t P) (Exists t Q).
      Proof.
        unfold heq. simpl. intros. eapply ST.heq_ex. eauto.
      Qed.

      Ltac notVar X :=
        match X with
          | _ _ => idtac
          | _ _ _ => idtac
          | _ _ _ _ => idtac
          | _ _ _ _ _ => idtac
          | _ _ _ _ _ _ => idtac
          | _ _ _ _ _ _ _ => idtac
          | _ _ _ _ _ _ _ _ => idtac
          | _ _ _ _ _ _ _ _ _ => idtac
          | _ _ _ _ _ _ _ _ _ _ => idtac
          | _ _ _ _ _ _ _ _ _ _ _ => idtac
          | _ _ _ _ _ _ _ _ _ _ _ _ => idtac
          | _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
          | _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
        end.

      Ltac uip_all :=
        repeat match goal with
                 | [ H : _ = _ |- _ ] => rewrite H
                 | [ |- context [ match ?X in _ = t return _ with 
                                    | refl_equal => _ 
                                  end ] ] => notVar X; generalize X
                 | [ |- context [ eq_rect_r _ _ ?X ] ] => notVar X; generalize X
               end;
        intros;
        repeat match goal with
                 | [ H : ?X = ?X |- _ ] => rewrite (UIP_vars H (refl_equal _)) in *
               end.


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

      Lemma existsEach_peel_back : forall uvars x r t A C 
        (P : sexpr fs sfuncs uvars ((x ++ t :: nil) ++ r))
        (Q : sexpr fs sfuncs uvars (x ++ t :: r)),
        (forall Z, heq A A (hlist_app Z C) cs P match eq_sym (app_ass x (t :: nil) r) in _ = t return sexpr _ _ _ t with
                                                  | refl_equal => Q
                                                end) ->
        heq A A C cs (existsEach (x ++ t :: nil) r P) (Exists t (existsEach x (t :: r) Q)).
      Proof.
        clear; induction x; simpl; intros.
          eapply heq_ex. intros. specialize (H (HCons v HNil)). etransitivity. eapply H.
          clear H. generalize (HCons v C). uip_all. reflexivity.
        etransitivity. eapply IHx. 
        instantiate (1 := match app_ass x (t :: nil) r in _ = t
                            return sexpr _ _ _ t with
                            | refl_equal => Exists a P
                          end). clear.
        intros. generalize (hlist_app Z C). generalize P. uip_all. generalize e e0 h P0.
        uip_all. reflexivity.
        
        eapply heq_ex. intros. eapply existsEach_heq. intros. uip_all.
        assert (a :: (x ++ t :: nil) ++ r = a :: x ++ (t :: nil) ++ r).
        f_equal; auto.
        etransitivity.
        instantiate (1 := Exists a match H0 in _ = t return sexpr _ _ _ t with
                                     | refl_equal => P
                                   end).
        clear. generalize P e H0. simpl. rewrite e. simpl. uip_all. reflexivity.

        eapply heq_ex. intros. specialize (H (HCons v0 (hlist_app Z (HCons v HNil)))).
        simpl in *. clear IHx. rewrite hlist_app_assoc in H. simpl in H.
        generalize dependent H. simpl. uip_all. unfold tvar in *.
        match goal with
          | [ |- heq _ _ (HCons _ (hlist_app ?H ?H')) _ _ _ ] => 
            generalize dependent (hlist_app H H')
        end.
        generalize P Q e0 H0 e1. simpl in *. uip_all. auto.
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
          eapply existsEach_heq; intros. symmetry. eapply existsEach_peel_back.
          intros.
          match goal with
            | [ |- heq _ _ ?H _ _ _ ] => generalize H
          end. clear. generalize H. uip_all. simpl in *.
          rewrite (UIP_vars H0 e). reflexivity.

          clear. generalize P H. uip_all. generalize e e0 Y P0.
          uip_all. clear. generalize Y0 e1 P1. clear. 
          cutrewrite ((b ++ a :: nil) ++ a0 = b ++ a :: a0). uip_all. reflexivity.
          rewrite app_ass. reflexivity.
      Qed.

      Lemma lift_exists_star : forall uvars x y z A C cs (P : sexpr fs sfuncs uvars (x ++ z))  Q,
        heq A A C cs (Star (existsEach x z P) (existsEach y z Q))
        (existsEach x _ (existsEach y _ (Star (liftSExpr nil y (x ++ z) P) (liftSExpr y x z Q)))).
      Proof.
        clear. induction x; simpl; intros.
        rewrite liftSExpr_nil; eauto. induction y. simpl. rewrite liftSExpr_nil. reflexivity.

        simpl. etransitivity. eapply IHy. eapply existsEach_heq. intros.
      Admitted.

      Lemma lift_denote_lift : forall u a b c (s : SHeap u (a ++ c)) X Y,
        heq X X Y cs (liftSExpr a b c (denote s)) (denote (liftSHeap a b c s)).
      Proof. Admitted.


      Lemma denote_join : forall a b (P Q : SHeap a b) X Y,
        heq X X Y cs (denote (join_SHeap P Q)) (Star (denote P) (denote Q)).
      Proof.
        clear. unfold join_SHeap. destruct P; destruct Q; simpl in *. 
        unfold denote; simpl.
      Admitted.

      Theorem denote_hash_left : forall G (s : sexpr fs sfuncs _ _), 
        heq HNil HNil G cs s 
          (@existsEach _ (projT1 (@hash_left _ _  s)) nil (denote (projT2 (hash_left s)))).
      Proof.
        clear. induction s; 
          try solve [ simpl; intros; unfold denote; simpl;
            unfold heq; simpl; symmetry; 
              do 10 (apply ST.heq_star_emp || (try apply ST.heq_star_comm)); reflexivity ].
          (** Star **)
          intros. eapply heq_subst. eapply IHs1. eapply heq_star_comm. eapply heq_subst.
            eapply IHs2. clear IHs2 IHs1.
            simpl. destruct (hash_left s1). destruct (hash_left s2). simpl.
            etransitivity. eapply lift_exists_star. etransitivity. eapply existsEach_app. 
            uip_all. eapply existsEach_heq. intros. generalize (hlist_app Z G). clear.

            intros. etransitivity. 2: symmetry; eapply denote_join.
            etransitivity. 
            instantiate (1 := Star match e0 in _ = t return sexpr _ _ _ t with
                                     | refl_equal => liftSExpr nil x (x0 ++ vars) (denote s0)
                                   end
                                   match e0 in _ = t return sexpr _ _ _ t with
                                     | refl_equal => liftSExpr x x0 vars (denote s)
                                   end).
            clear. generalize (liftSExpr nil x (x0 ++ vars) (denote s0)).
            generalize (liftSExpr x x0 vars (denote s)). generalize h e0. uip_all. reflexivity.

            eapply heq_star_comm. eapply heq_star_frame.

            generalize (@lift_denote_lift _ x x0 vars s HNil
              match app_ass x x0 vars in _ = t return hlist _ t with
                | refl_equal => h
              end). generalize h e e0. generalize (liftSExpr x x0 vars (denote s)).
            generalize (liftSHeap x x0 vars s). uip_all. unfold eq_rect_r, eq_rect. simpl. auto.

            generalize (@lift_denote_lift _ nil x (x0 ++ vars) s0 HNil
              match app_ass x x0 vars in _ = t return hlist _ t with
                | refl_equal => h
              end).
            Opaque liftSExpr. simpl. 
            generalize (liftSExpr nil x (x0 ++ vars) (denote s0)). 
            generalize (liftSHeap nil x (x0 ++ vars) s0).
            generalize h e0 e s0. simpl app in *. uip_all. unfold eq_rect_r, eq_rect. auto.
          (** Exists **)
          Focus.
          intros. simpl. destruct (hash_left s); simpl in *.
            etransitivity. 2: symmetry; eapply existsEach_peel_back.
            instantiate (1 := denote s0). eapply heq_ex. eauto.
            intros. clear IHs. generalize (hlist_app Z G). generalize s0. clear. uip_all. 
            generalize s0 h e e0. simpl in *. uip_all. unfold eq_rect_r, eq_rect; simpl.
            reflexivity.

          (** Func **)
          Focus.
          simpl. unfold denote. simpl. unfold heq. symmetry. simpl.
            apply ST.heq_star_comm. apply ST.heq_star_assoc. 
            repeat apply ST.heq_star_emp. apply ST.heq_star_comm. apply ST.heq_star_emp.
            reflexivity.
      Qed.

(*
      Theorem denote_hash_right : forall ext G (s : sexpr fs sfuncs _ _) cs, 
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

(*
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

    Fixpoint existsEach (vars vars' : variables types) 
      : sexpr fs sfuncs (vars ++ vars') -> sexpr fs sfuncs vars' :=
      match vars as vars return sexpr fs sfuncs (vars ++ vars') -> sexpr fs sfuncs vars'
        with
        | nil => fun s => s
        | a :: b => fun s => @existsEach b vars' (Exists a s)
      end.
*)

(*
      Fixpoint sepCancel vars (e : sexpr fs sfuncs vars) {struct e}
        : SHeap vars -> SHeap vars -> SHeap vars * SHeap vars.
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
*)



          
(*
          match sepCancel gr lhs (SHeap_empty _) as k 
            return sepCancel gr lhs (SHeap_empty _) = k -> _ with
            | (lhs',rhs') => fun pf =>
              @existT _ _ (denote lhs', denote rhs') _
          end (eq_refl _)
*)
(*
      end).
      intros. etransitivity. 2: eapply sepCancel_cancels. 2: eassumption. 2: eauto.
      unfold lhs. etransitivity. eapply denote_hash_cc. unfold Himp, himp. reflexivity.
*)

(*
    Fixpoint hash vars (s : sexpr fs sfuncs nil vars) :
      { vars' : variables types & SHeap vars' vars }.
    refine (
      match s in sexpr _ _ _ vars return { vars' : variables types & SHeap vars' vars } with
        | Emp _ => @existT _ _ nil (SHeap_empty _ _)
        | Inj _ p => @existT _ _ nil
          {| funcs := dmap_empty
           ; pures := p :: nil
           ; other := nil
           |}
        | Star vs l r =>
          match hash _ l, hash _ r with
            | existT vl hl , existT vr hr =>
              @existT _ _ (vl ++ vr)
                (join_SHeap 
                  match  (app_nil_r vr) in _ = t return SHeap (vl ++ t) vs with
                    | refl_equal => 
                      @liftSHeapU vl vr nil vs 
                        match eq_sym (app_nil_r vl) in _ = t return SHeap t vs with
                          | refl_equal => hl
                        end
                  end
                  (@liftSHeapU nil vl vr vs hr))
          end
        | Exists vs t b =>
          match hash _ b with
            | existT v b =>
              @existT _ (fun x : list (tvar types) => SHeap x vs) (v ++ t :: nil) _
          end
(*
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
             *)
        | _ => @existT _ _ nil {| funcs := dmap_empty
                                ; pures := nil
                                ; other := nil
                                |}
      end).

*)

(*
    Fixpoint hash_left' uvars vars ext (s : sexpr fs sfuncs uvars vars) {struct s} :
      { es : variables types & 
        { h : SHeap uvars (ext ++ es ++ vars) | forall A B C cs, heq A B C cs (existsEach _ es (denote h)) (liftSExpr nil ext _ s) } }.
    refine (
      match s in sexpr _ _ _ vars return { es : variables types & SHeap uvars (ext ++ es ++ vars) } with
        | Emp _ => @existT _ _ nil (SHeap_empty _ _)
        | Inj _ p => @existT _ _ nil 
          {| funcs := dmap_empty
           ; pures := @liftPures uvars nil ext _ (p :: nil) 
           ; other := nil
           |}
        | Star vs l r => _
        | _ => _
      end).
    refine (match @hash_left' uvars vs ext l with
              | existT vs' l' =>
                match hash_left' uvars vs (ext ++ vs') r with
                  | existT vs'' r' =>
                    @existT _ _ (vs' ++ vs'') _
                end
            end).
    Check liftFunctions.
    rewrite list_app_assoc. rewrite <- list_app_assoc. 
    eapply join_SHeap.
    refine (@liftSHeap uvars (ext ++ vs') vs'' vs match sym_eq (list_app_assoc ext vs' vs) in _ = t return SHeap uvars t with
                                                 | refl_equal => l'
                                               end).
    apply r'.
    clear hash_left'; admit.
    clear hash_left'; admit.
    clear hash_left'; admit.
    Defined.

    Fixpoint hlist_app T F (ll lr : list T) : hlist F ll -> hlist F lr -> hlist F (ll ++ lr) :=
      match ll with
        | nil => fun _ x => x
        | _ :: _ => fun l r => HCons (hlist_hd l) (hlist_app (hlist_tl l) r)
      end.

    Lemma existsEach_p : forall z z' z'' (A : hlist _ z) (B : hlist _ z') (C : hlist _ z'') cs vs l r , 
      (forall k : hlist _ vs, himp A B (hlist_app k C) cs l (liftSExpr nil vs _ r)) -> 
      himp A B C cs (existsEach vs _ l) r.
    Proof.
(*
      induction vs. simpl. split. unfold himp, ST.heq in *. intros. specialize (H HNil). auto.
        eauto.

      intros; simpl in *. split; intros.
      
      exists HNil. auto.
      intros. simpl in *. destruct (IHvs (Exists _ l) (Exists _ r)). clear IHvs. unfold heq in *.
      split; intros. simpl in *. destruct H0. 2: apply H. Focus 2. destruct H1. exists (hlist_tl x0). admit.
      destruct H1.


etransitivity. 2: eapply H. reflexivity. destruct H1. exists (hlist_tl x). simpl in *.
        
      
      
      .
      destruct H. unfold heq, ST.heq in *; tauto.
    unfold heq.
*)
    Admitted.

    Lemma existsEach_c : forall z z' z'' (A : hlist _ z) (B : hlist _ z') (C : hlist _ z'') cs vs l r , 
      (exists k : hlist _ vs, himp A B (hlist_app k C) cs (liftSExpr nil vs _ l) r) -> 
      himp A B C cs l (existsEach vs _ r).
    Proof.
(*
      induction vs. simpl. split. unfold himp, ST.heq in *. intros. specialize (H HNil). auto.
        eauto.

      intros; simpl in *. split; intros.
      
      exists HNil. auto.
      intros. simpl in *. destruct (IHvs (Exists _ l) (Exists _ r)). clear IHvs. unfold heq in *.
      split; intros. simpl in *. destruct H0. 2: apply H. Focus 2. destruct H1. exists (hlist_tl x0). admit.
      destruct H1.


etransitivity. 2: eapply H. reflexivity. destruct H1. exists (hlist_tl x). simpl in *.
        
      
      
      .
      destruct H. unfold heq, ST.heq in *; tauto.
    unfold heq.
*)
    Admitted.

    Lemma liftSExpr_existsEach_c : forall cs l E a A B C P Q,
      himp A B C cs P (existsEach E a (liftSExpr l E a Q)) ->
      himp A B C cs P (liftSExpr l E a (existsEach E a Q)).


    Ltac cancel_all :=
      let s :=
        (   reflexivity 
         || simple apply ST.himp_star_emp_c
         || simple apply ST.himp_star_emp_p
         || simple apply ST.himp_star_cancel
(*         || simple apply ST.heq_star_cancel
         || simple apply ST.heq_star_emp
         || (match goal with
               | [ |- ST.heq _ _ _ ] => symmetry; simple apply ST.heq_star_emp; symmetry
             end)
*)
        )
      in
      let perm :=
        try ((eapply ST.himp_star_comm_p; repeat simple apply ST.himp_star_assoc_p)
(*             (eapply ST.heq_star_comm; symmetry; repeat simple apply ST.heq_star_assoc; symmetry) *)); 
        try do 10 (s || 
          match goal with
            | [ |- ST.heq _ _ _ _ _ ] =>
              symmetry; simple apply ST.heq_star_comm; symmetry; repeat simple apply ST.heq_star_assoc
            | [ |- ST.himp _ _ _ _ _ ] =>
              repeat (simple apply ST.himp_star_assoc_c)
          end)
      in
      do 10 perm.


    Theorem denote_hash_left' : forall a E (s : sexpr fs sfuncs _ (E ++ a)) G cs, 
      heq HNil HNil G cs (@existsEach nil E _ s)
        (@existsEach _ E _ (@existsEach nil (projT1 (hash_left' nil s)) (E ++ a) (denote (projT2 (hash_left' nil s))))).
    Proof.
      clear. Require Import Program. dependent induction s; simpl; intros; unfold denote; simpl.
      Focus.
      split; eapply existsEach_p; intros; simpl. eapply existsEach_c.
      split; eapply existsEachPf; unfold himp; intros; simpl. simple apply ST.himp_star_emp_c. apply ST.himp_star_assoc_c. 
        apply ST.himp_star_comm_c. apply ST.himp_star_assoc_c. do 2 apply ST.himp_star_emp_c. 

        

        generalize (existsEachPf). unfold himp. intros. eapply H. intros. simpl. cancel_all.
        

      xxx.
      admit. (** SIMPLE **)
      admit. (** SIMPLE **)
      

      simpl.

generalize (@nil. induction s; simpl; intros; unfold denote; simpl. 
          admit. (** TRIVIAL **)
          admit. (** TRIVIAL **)
          unfold heq. simpl.

          
          admit. (** CHECK **)
          unfold heq. simpl. admit.
          admit. (** TRIVIAL **)
          admit. (** TRIVIAL **)
        
        
      Admitted.
*)