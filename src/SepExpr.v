Require Import List.
Require Import SepTheoryX PropX.
Require Import PropXTac.
Require Import RelationClasses EqdepClass.
Require Import Expr ExprUnify2.
Require Import DepList.
Require Import Setoid.
Require Import Prover.

Set Implicit Arguments.

Require NatMap.

Module FM := NatMap.IntMap.

Definition BadInj types (e : expr types) := False.
Definition BadPred (f : func) := False.
Definition BadPredApply types (f : func) (es : list (expr types)) := False.

Module Type SepExprType.
  Declare Module ST : SepTheoryX.SepTheoryXType.

  Section env.
    Variable types : list type.
    Variable pcType : tvar.
    Variable stateType : tvar.

    Record ssignature := SSig {
      SDomain : list tvar ;
      SDenotation : functionTypeD (map (@tvarD types) SDomain) (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.

    Definition predicates : Type := list ssignature.

    Parameter Default_predicate : ssignature.

    Inductive sexpr : Type :=
    | Emp : sexpr
    | Inj : expr types -> sexpr
    | Star : sexpr -> sexpr -> sexpr
    | Exists : tvar -> sexpr -> sexpr
    | Func : func -> list (expr types) -> sexpr
    | Const : ST.hprop (tvarD types pcType) (tvarD types stateType) nil -> sexpr
    .

    Section funcs_preds.
      Variable funcs : functions types.
      Variable preds : predicates.
      
      Fixpoint sexprD (meta_env var_env : env types) (s : sexpr)
        : ST.hprop (tvarD types pcType) (tvarD types stateType) nil :=
        match s with 
          | Emp => ST.emp _ _
          | Inj p =>
            match exprD funcs meta_env var_env p tvProp with
              | None => ST.inj (PropX.Inj (BadInj p))
              | Some p => ST.inj (PropX.Inj p)
            end
          | Star l r =>
            ST.star (sexprD meta_env var_env l) (sexprD meta_env var_env r)
          | Exists t b =>
            ST.ex (fun x : tvarD types t => sexprD meta_env (@existT _ _ t x :: var_env) b)
          | Func f b =>
            match nth_error preds f with
              | None => ST.inj (PropX.Inj (BadPred f))
              | Some f' =>
                match applyD (@exprD types funcs meta_env var_env) (SDomain f') b _ (SDenotation f') with
                  | None => ST.inj (PropX.Inj (BadPredApply f b))
                  | Some p => p
                end
            end
          | Const p => p
        end.

      Definition himp (meta_env var_env : env types)
        (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
        (gl gr : sexpr) : Prop :=
        ST.himp cs (sexprD meta_env var_env gl) (sexprD meta_env var_env gr).

      Definition heq (meta_env var_env : env types)
        (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
        (gl gr : sexpr) : Prop :=
        ST.heq cs (sexprD meta_env var_env gl) (sexprD meta_env var_env gr).

    End funcs_preds.

    Record SHeap : Type :=
    { impures : FM.t (list (list (expr types)))
    ; pures   : list (expr types)
    ; other   : list (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.

    Parameter star_SHeap : SHeap -> SHeap -> SHeap.

    Parameter sheapSubstU : nat -> nat -> nat -> SHeap -> SHeap.

    Parameter hash : sexpr -> variables * SHeap.


    (** TODO: What happens if I denote this directly to hprop?
     ** - fewer lemmas about concrete syntax!
     ** - can't re-hash (probably don't want to do this anyways...)
     ** * I think this is Ok for now
     **)
    Parameter sheapD : SHeap -> sexpr.

    Fixpoint existsEach (ls : list tvar) {struct ls} : sexpr -> sexpr :=
      match ls with
        | nil => fun x => x
        | t :: ts => fun y => Exists t (@existsEach ts y)
      end.

  End env.
End SepExprType.

Module Make (ST' : SepTheoryX.SepTheoryXType) <: SepExprType with Module ST := ST'.
  Module ST := ST'.

  Module SEP_FACTS := SepTheoryX_Rewrites ST.
  Section env.
    Variable types : list type.
    Variable pcType : tvar.
    Variable stateType : tvar.

    Record ssignature := SSig {
      SDomain : list tvar ;
      SDenotation : functionTypeD (map (@tvarD types) SDomain) (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.

    Definition predicates := list ssignature.

    Definition Default_predicate : ssignature :=
    {| SDomain := nil
     ; SDenotation := @ST.emp _ _ _
     |} .

    Variable funcs : functions types.
    Variable sfuncs : predicates.

    Inductive sexpr : Type :=
    | Emp : sexpr
    | Inj : expr types -> sexpr
    | Star : sexpr -> sexpr -> sexpr
    | Exists : tvar -> sexpr -> sexpr
    | Func : func -> list (expr types) -> sexpr
    | Const : ST.hprop (tvarD types pcType) (tvarD types stateType) nil -> sexpr
    .

    Fixpoint sexprD (meta_env var_env : env types) (s : sexpr)
      : ST.hprop (tvarD types pcType) (tvarD types stateType) nil :=
      match s with 
        | Emp => ST.emp _ _
        | Inj p =>
          match exprD funcs meta_env var_env p tvProp with
            | None => ST.inj (PropX.Inj (BadInj p))
            | Some p => ST.inj (PropX.Inj p)
          end
        | Star l r =>
          ST.star (sexprD meta_env var_env l) (sexprD meta_env var_env r)
        | Exists t b =>
          ST.ex (fun x : tvarD types t => sexprD meta_env (@existT _ _ t x :: var_env) b)
        | Func f b =>
          match nth_error sfuncs f with
            | None => ST.inj (PropX.Inj (BadPred f))
            | Some f' =>
              match applyD (@exprD types funcs meta_env var_env) (SDomain f') b _ (SDenotation f') with
                | None => ST.inj (PropX.Inj (BadPredApply f b))
                | Some p => p
              end
          end
        | Const p => p
      end.

    Definition himp (meta_env var_env : env types)
      (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
      (gl gr : sexpr) : Prop :=
      ST.himp cs (sexprD meta_env var_env gl) (sexprD meta_env var_env gr).

    Definition heq (meta_env var_env : env types)
      (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
      (gl gr : sexpr) : Prop :=
      ST.heq cs (sexprD meta_env var_env gl) (sexprD meta_env var_env gr).

    Section Facts.
      Variables U G : env types.
      Variable cs : codeSpec (tvarD types pcType) (tvarD types stateType).

      Global Instance Trans_himp : Transitive (@himp U G cs).
      Proof.
        red. unfold himp. intros; etransitivity; eauto.
      Qed.

      Global Instance Trans_heq : Transitive (@heq U G cs).
      Proof.
        red. unfold heq. intros; etransitivity; eauto.
      Qed.

      Global Instance Refl_himp : Reflexive (@himp U G cs).
      Proof.
        red; unfold himp; intros. reflexivity.
      Qed.

      Global Instance Refl_heq : Reflexive (@heq U G cs).
      Proof.
        red; unfold heq; intros. reflexivity.
      Qed.

      Global Instance Sym_heq : Symmetric (@heq U G cs).
      Proof.
        red; unfold heq; intros. symmetry. auto.    
      Qed.

      Global Instance Equiv_heq : Equivalence (heq U G cs).
      Proof.
        constructor; eauto with typeclass_instances.
      Qed.

      Add Parametric Relation : sexpr (@himp U G cs)
        reflexivity proved by  Refl_himp
        transitivity proved by Trans_himp
      as himp_rel.

      Add Parametric Relation : sexpr (@heq U G cs)
        reflexivity proved by  Refl_heq
        symmetry proved by Sym_heq
        transitivity proved by Trans_heq
      as heq_rel.

      Global Add Parametric Morphism : Star with
        signature (himp U G cs ==> himp U G cs ==> himp U G cs)      
        as star_himp_mor.
        unfold himp; simpl; intros; eapply SEP_FACTS.star_himp_mor; eauto.
      Qed.

      Global Add Parametric Morphism : Star with
        signature (heq U G cs ==> heq U G cs ==> heq U G cs)      
        as star_heq_mor.
        unfold himp; simpl; intros; eapply SEP_FACTS.star_heq_mor; eauto.
      Qed.

      Global Add Parametric Morphism : (himp U G cs) with 
        signature (heq U G cs ==> heq U G cs ==> Basics.impl)
        as himp_heq_mor.
        unfold heq; simpl; intros. eapply SEP_FACTS.himp_heq_mor; eauto.
      Qed.

      Global Add Parametric Morphism : (himp U G cs) with 
        signature (himp U G cs --> himp U G cs ++> Basics.impl)
        as himp_himp_mor.
        unfold himp; simpl; intros. eapply SEP_FACTS.himp_himp_mor; eauto.
      Qed.

      Global Add Parametric Morphism : (sexprD U G) with 
        signature (heq U G cs ==> ST.heq cs)
        as heq_ST_heq_mor.
        unfold heq; simpl; auto.
      Qed.

      Lemma heq_star_emp_r : forall P, 
        heq U G cs (Star P Emp) P.
      Proof.
        unfold heq; simpl; intros; autorewrite with hprop; reflexivity.
      Qed.

      Lemma heq_star_emp_l : forall P, 
        heq U G cs (Star Emp P) P.
      Proof.
        unfold heq; simpl; intros; autorewrite with hprop; reflexivity.
      Qed.

      Lemma heq_star_assoc : forall P Q R, 
        heq U G cs (Star (Star P Q) R) (Star P (Star Q R)).
      Proof.
        unfold heq; simpl; intros; autorewrite with hprop. rewrite ST.heq_star_assoc. reflexivity.
      Qed.

      Lemma heq_star_comm : forall P Q, 
        heq U G cs (Star P Q) (Star Q P).
      Proof.
        unfold heq; simpl; intros; apply ST.heq_star_comm.
      Qed.

      Lemma heq_star_frame : forall P Q R S, 
        heq U G cs P R ->
        heq U G cs Q S ->
        heq U G cs (Star P Q) (Star R S).
      Proof.
        unfold heq; simpl; intros. eapply ST.heq_star_frame; auto.
      Qed.
      
      Lemma himp_star_frame : forall a c cs P Q R S,
        himp a c cs P R ->
        himp a c cs Q S ->
        himp a c cs (Star P Q) (Star R S).
      Proof.
        unfold himp; simpl; intros. rewrite H; rewrite H0; reflexivity.
      Qed.
        
    End Facts.

    Lemma fold_left_star : forall T a c cs F (ls : list T)  base,
      heq a c cs (fold_left (fun acc x => Star (F x) acc) ls base)
      (Star (fold_left (fun acc x => Star (F x) acc) ls Emp) base).
    Proof.
      induction ls; simpl; intros.
      rewrite heq_star_emp_l. reflexivity.
      rewrite IHls. symmetry. rewrite IHls.
      repeat rewrite heq_star_assoc. rewrite heq_star_emp_l. reflexivity.
    Qed.

    Ltac heq_fold_left_opener :=
      match goal with
        | [ |- context [ fold_left _ _ ?B ] ] =>
          match B with
            | Emp => fail 1 
            | _ => rewrite fold_left_star with (base := B)
          end
      end.
    Ltac heq_canceler :=
      repeat (repeat rewrite heq_star_assoc; first [ apply heq_star_frame; [ reflexivity | try reflexivity ] | 
        rewrite heq_star_comm; symmetry ]).

    Existing Instance himp_rel_relation.
    Existing Instance heq_rel_relation.
    Hint Rewrite heq_star_emp_l heq_star_emp_r : hprop.

    Theorem ST_himp_himp : forall (U G : env types) cs L R,
      himp U G cs L R ->
      ST.himp cs (sexprD U G L) (sexprD U G R).
    Proof.
      clear. auto.
    Qed.

    Theorem ST_heq_heq : forall (U G : env types) cs L R,
      heq U G cs L R ->
      ST.heq cs (sexprD U G L) (sexprD U G R).
    Proof.
      clear. auto.
    Qed.

    (** A more efficient representation for sexprs. **)
    Record SHeap : Type :=
    { impures : FM.bst (list (list (expr types)))
    ; pures   : list (expr types)
    ; other   : list (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.
  
    Definition SHeap_empty : SHeap := 
      {| impures := @FM.empty _
       ; pures   := nil
       ; other   := nil
       |}.

    (** lift all the "real" variables in [a,...) 
     ** to the range [a+b,...)
     **)
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

    (** lift all the "real" variables in [a,...) 
     ** to the range [a+b,...)
     **)
    Definition liftSHeap (a b : nat) (s : SHeap) : SHeap :=
      {| impures := FM.map (map (map (liftExpr a b))) (impures s)
       ; pures   := map (liftExpr a b) (pures s)
       ; other   := other s
       |}.

    Definition multimap_add T (k : nat) (v : T) (m : FM.bst (list T)) : FM.bst (list T) :=
      match FM.find k m with
        | None => FM.add k (v :: nil) m
        | Some v' => FM.add k (v :: v') m
      end.

    Definition multimap_join T : FM.bst (list T) -> FM.bst (list T) -> FM.bst (list T) :=
      FM.fold (fun k v a => 
        match FM.find k a with
          | None => FM.add k v a
          | Some v' => FM.add k (v ++ v') a
        end).

    Fixpoint star_SHeap (l r : SHeap) : SHeap :=
      {| impures := multimap_join (impures l) (impures r)
       ; pures := pures l ++ pures r
       ; other := other l ++ other r
       |}.

    Definition sheap_liftVars (from : nat) (delta : nat) (h : SHeap) : SHeap :=
      {| impures := FM.map (map (map (liftExpr from delta))) (impures h)
       ; pures := map (liftExpr from delta) (pures h)
       ; other := other h
       |}.

    (** CURRENTLY NOT USED **)
    Fixpoint substV types (vs : list nat) (e : expr types) : expr types :=
      match e with
        | Expr.Const _ c => Expr.Const c
        | Var x => 
          Var (match nth_error vs x with
                 | None => x
                 | Some y => y
               end)
        | UVar x => UVar x
        | Expr.Func f xs => 
          Expr.Func f (map (substV vs) xs)
        | Equal t e1 e2 => Equal t (substV vs e1) (substV vs e2)
        | Not e1 => Not (substV vs e1)
      end.

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
          let nr := length vr in
          (vl ++ vr,
            star_SHeap (sheap_liftVars 0 nr hl) (sheap_liftVars nr (length vl) hr))
        | Exists t b =>
          let (v, b) := hash b in
          (t :: v, b)
        | Func f a =>
          (nil,
           {| impures := FM.add f (a :: nil) (FM.empty _)
            ; pures := nil
            ; other := nil
           |})
        | Const c => 
          (@nil tvar,
           {| impures := @FM.empty (list (list (expr types)))
            ; pures := @nil (expr types)
            ; other := c :: nil
            |})
      end.

    Definition starred (T : Type) (F : T -> sexpr) (ls : list T) (base : sexpr)
      : sexpr :=
      fold_right (fun x a => match a with 
                               | Emp => F x
                               | _ => Star (F x) a
                             end) base ls.

    Definition sheapD (h : SHeap) : sexpr :=
      let a := starred (fun x => Const x) (other h) Emp in
      let a := starred (fun x => Inj x) (pures h) a in
      let a := FM.fold (fun k => starred (Func k)) (impures h) a in
      a.

    Definition starred' (T : Type) (F : T -> sexpr) (ls : list T) (base : sexpr)
      : sexpr :=
      fold_right (fun x a => Star (F x) a) base ls.

    Definition sheapD' (h : SHeap) :  sexpr :=
      let a := FM.fold (fun k ls acc => 
        Star (starred' (Func k) ls Emp) acc) (impures h) Emp in
      let c := starred' (fun x => Inj x) (pures h) Emp in
      let e := starred' (fun x => Const x) (other h) Emp in
      Star a (Star c e).

    Lemma starred_starred' : forall a c cs T F F' base base' ls, 
      heq a c cs base base' ->
      (forall x, heq a c cs (F x) (F' x)) ->
      heq a c cs (@starred T F ls base) (@starred' T F' ls base').
    Proof.
      induction ls; simpl; intros.
        assumption.
        specialize (IHls H H0).
        etransitivity. instantiate (1 := (Star (F a0) (starred F ls base))).
        destruct (starred F ls base); try reflexivity.
        autorewrite with hprop. reflexivity.
        rewrite H0. rewrite IHls. reflexivity.
    Qed.

    Lemma starred'_base : forall a c cs T F base ls, 
      heq a c cs (Star (@starred' T F ls Emp) base) (@starred' T F ls base).
    Proof.
      unfold heq in *; simpl in *.
      induction ls; simpl; intros.
        autorewrite with hprop; reflexivity.
        rewrite <- IHls. rewrite ST.heq_star_assoc. reflexivity.
    Qed.

    Lemma starred_base : forall a c cs T F base ls, 
      heq a c cs (Star (@starred T F ls Emp) base) (@starred T F ls base).
    Proof.
      unfold heq in *; simpl in *.
      induction ls; simpl; intros.
        autorewrite with hprop; reflexivity.
        Opaque exprD.
        destruct (starred F ls base); destruct (starred F ls Emp);
          simpl in *; autorewrite with hprop in *; try rewrite ST.heq_star_assoc; try rewrite IHls;
            autorewrite with hprop; try reflexivity.
    Qed.

    Global Add Parametric Morphism a c cs : (fun k0 : FM.key => starred (Func k0)) with
      signature (eq ==> eq ==> heq a c cs ==> heq a c cs)
      as star_himp_mor'.
    Proof.
      intros.
      repeat match goal with
               | [ |- Morphisms.Proper _ _ ] => red; intros; subst
               | [ |- Morphisms.respectful _ _ _ _ ] => red; intros; subst
               | [ H : heq _ _ _ _ _ |- _ ] => rewrite H; clear H
               | [ |- heq _ _ _ _ ] => heq_canceler
             end.
      rewrite <- starred_base. symmetry. rewrite <- starred_base. heq_canceler.
      symmetry; auto.
    Qed.
    Lemma transpose_neqkey_starred a c cs : NatMap.IntMapProperties.transpose_neqkey (heq a c cs)
      (fun k0 : FM.key => starred (Func k0)).
    Proof.
      red. intros. rewrite <- starred_base. symmetry.
      rewrite <- starred_base. repeat rewrite <- starred_base with (base := a0).
      heq_canceler.
    Qed.
    Lemma transpose_neqkey_Star (X : Type) F a c cs : NatMap.IntMapProperties.transpose_neqkey (heq a c cs)
      (fun (k0 : FM.key) (ls : X) (a1 : sexpr) => Star (F k0 ls) a1).
    Proof.
      red. intros. heq_canceler.
    Qed.
    Hint Resolve transpose_neqkey_starred transpose_neqkey_Star : hprop.
    Hint Extern 1 (Morphisms.Proper _ _) =>
      (unfold Morphisms.Proper, Morphisms.respectful; intros; subst; 
        repeat match goal with
                 | [ H : heq _ _ _ _ _ |- _ ] => rewrite H
               end; reflexivity) : hprop.

    Lemma fold_starred : forall X a c cs (F : nat -> X -> sexpr) m b,
      heq a c cs (FM.fold (fun k ls a => Star (F k ls) a) m b)
      (Star (FM.fold (fun k ls a => Star (F k ls) a) m Emp) b).
    Proof.
      do 5 intro.
      intro. apply NatMap.IntMapProperties.fold_rec with (m := m).
        intros. rewrite NatMap.IntMapProperties.fold_Empty; eauto with typeclass_instances.
        autorewrite with hprop. reflexivity.

        intros. erewrite NatMap.IntMapProperties.fold_Add; eauto with typeclass_instances hprop.
        rewrite H2. heq_canceler.
    Qed.

    Lemma impures' : forall a c cs (i : FM.bst _)  b, 
      heq a c cs (FM.fold (fun k => starred (Func k)) i b)
      (Star (FM.fold (fun k ls a => Star (starred' (Func k) ls Emp) a) i Emp) b).
    Proof.
      do 4 intro. apply NatMap.IntMapProperties.fold_rec with (m := i); intros.
        rewrite NatMap.IntMapProperties.fold_Empty; eauto with typeclass_instances.
        autorewrite with hprop; reflexivity.

        erewrite NatMap.IntMapProperties.fold_Add; eauto with typeclass_instances hprop.
        rewrite <- starred_base. rewrite starred_starred'; try reflexivity.
        rewrite H2. heq_canceler.
    Qed.

    Theorem sheapD_sheapD' : forall a c cs h, 
      heq a c cs (sheapD h) (sheapD' h).
    Proof.
      destruct h; unfold sheapD, sheapD'; simpl.
      rewrite impures'. rewrite <- (@starred_base a c cs). 
      rewrite <- (@starred_base a c cs) with (ls := other0).
      eapply heq_star_frame. reflexivity.
      eapply heq_star_frame. eapply starred_starred'; reflexivity.
      autorewrite with hprop.
      eapply starred_starred'; reflexivity.
    Qed.

    Lemma starred_In : forall T (F : T -> sexpr) a c cs x ls' b ls,
      heq a c cs (starred F (ls ++ x :: ls') b) (Star (starred F (ls ++ ls') b) (F x)).
    Proof.
      induction ls; intros.
        symmetry; rewrite heq_star_comm.
        repeat rewrite starred_starred' by reflexivity.
        reflexivity.

        generalize dependent IHls.
        repeat rewrite starred_starred' by reflexivity.
        intro IHls. simpl. rewrite heq_star_assoc.
        rewrite IHls. reflexivity.
    Qed.

    Lemma sheapD_pures : forall stn sm cs uvars vars h,
      ST.satisfies cs (sexprD uvars vars (sheapD h)) stn sm ->
      AllProvable funcs uvars vars (pures h).
    Proof.
      intros. eapply ST.satisfies_himp in H.
      Focus 2. instantiate (1 := sexprD uvars vars (sheapD' h)). 
      match goal with
        | [ |- ?G ] => 
          change G with (himp uvars vars cs (sheapD h) (sheapD' h))
      end.
      rewrite sheapD_sheapD'. reflexivity.
      
      destruct h. unfold sheapD' in *.
      eapply ST.satisfies_himp in H.
      Focus 2.
      instantiate (1 := sexprD uvars vars
           (Star
              (starred' (fun x : expr types => Inj x)
                 (pures
                    {|
                    impures := impures0;
                    pures := pures0;
                    other := other0 |}) Emp)

        (Star
           (FM.fold
              (fun (k : nat) (ls : list (list (expr types)))
                 (acc : sexpr) =>
               Star (starred' (Func k) ls Emp) acc)
              (impures
                 {| impures := impures0; pures := pures0; other := other0 |})
              Emp)
              (starred'
                 (fun
                    x : ST.hprop (tvarD types pcType) 
                          (tvarD types stateType) nil => 
                  Const x)
                 (other
                    {|
                    impures := impures0;
                    pures := pures0;
                    other := other0 |}) Emp)))).
      match goal with
        | [ |- ST.himp ?C (sexprD ?U ?V ?L) (sexprD ?U ?V ?R) ] =>
          change (ST.himp C (sexprD U V L) (sexprD U V R)) with
            (himp U V C L R)
      end.

      simpl. rewrite heq_star_comm. rewrite heq_star_assoc.
      apply himp_star_frame; try reflexivity. rewrite heq_star_comm.
      reflexivity.
      
      match goal with
        | [ H : ST.satisfies _ (sexprD _ _ (Star _ ?X)) _ _ |- _ ] =>
          generalize dependent X
      end.
      simpl. clear.
      
      generalize sm. clear.
      induction pures0; simpl; intros; auto.
        rewrite ST.heq_star_assoc in H.
        apply ST.satisfies_star in H. do 2 destruct H.
        intuition eauto.
        unfold Provable. destruct (exprD funcs uvars vars a tvProp);
        apply ST.satisfies_pure in H; propxFo.
    Qed.

    Lemma sheapD_pull_impure : forall a c cs h f argss,
      FM.find f (impures h) = Some argss ->
      heq a c cs (sheapD h)
                 (Star (sheapD {| impures := FM.remove f (impures h)
                                ; pures   := pures h
                                ; other   := other h |})
                       (starred (Func f) argss Emp)).
    Proof.
      intros. 
      repeat rewrite sheapD_sheapD'.
      unfold sheapD'; destruct h; simpl.
      etransitivity.
      eapply heq_star_frame. 2: reflexivity.      
      instantiate (1 := (Star
         (FM.fold
            (fun (k : nat) (ls : list (list (expr types)))
               (acc : sexpr) =>
             Star (starred' (Func k) ls Emp) acc) (FM.remove f impures0) Emp)
         (starred (Func f) argss Emp))).
      Focus 2.
      rewrite heq_star_assoc. rewrite heq_star_comm. rewrite heq_star_assoc.
      rewrite heq_star_comm. rewrite heq_star_assoc.
      symmetry. rewrite heq_star_assoc. rewrite heq_star_comm.
      heq_canceler.

      rewrite NatMap.IntMapProperties.fold_Add with (m2 := impures0); eauto with typeclass_instances hprop.
      Focus 3. unfold NatMap.IntMapProperties.Add. instantiate (3 := f). instantiate (2 := argss).
      instantiate (1 := (FM.remove f impures0)). intros.
        rewrite NatMap.IntMapProperties.F.add_o. simpl in *.
        destruct (NatMap.Ordered_nat.eq_dec f y). subst; auto.
        rewrite NatMap.IntMapProperties.F.remove_neq_o; auto.

      Focus 2. apply FM.remove_1; auto.

      rewrite starred_starred'; try reflexivity. heq_canceler.
    Qed.

    Lemma heq_ex : forall X Y cs t P Q,
      (forall v : tvarD types t, heq X (existT (tvarD types) t v :: Y) cs P Q) ->
      heq X Y cs (Exists t P) (Exists t Q).
    Proof.
      unfold heq; simpl; intros; apply ST.heq_ex; auto.
    Qed.

    (** The first variable in the list is the first one quantified!
     **)
    Fixpoint existsEach (ls : list tvar) {struct ls} : sexpr -> sexpr :=
      match ls with
        | nil => fun x => x
        | t :: ts => fun y => Exists t (@existsEach ts y)
      end.
    
    Lemma heq_existsEach : forall cs X v Y (P Q : sexpr),
      (forall Z, map (@projT1 _ _) Z = rev v -> heq X (Z ++ Y) cs P Q) ->
      heq X Y cs (existsEach v P) (existsEach v Q).
    Proof.
      induction v; simpl; intros.
        specialize (H nil); simpl in *; auto.

        apply heq_ex. intros. eapply IHv. intros.
        simpl. specialize (H (Z ++ @existT _ _ _ v0 :: nil)). rewrite map_app in *. 
        rewrite H0 in *. simpl in *.
        rewrite app_ass in *. simpl in *. auto.
    Qed.

    Lemma existsEach_app : forall X cs b a Y (P : sexpr),
      heq X Y cs (existsEach a (existsEach b P)) (existsEach (a ++ b) P).
    Proof.
      induction a; simpl.
        reflexivity.
        intros. apply heq_ex; intros. apply IHa.
    Qed.

    Lemma liftSExpr_0 : forall b a, liftSExpr a 0 b = b.
    Proof.
      induction b; simpl; intros; auto.
      rewrite liftExpr_0; reflexivity.
      rewrite IHb1; rewrite IHb2; reflexivity.
      rewrite IHb. auto.
      f_equal. clear. induction l; simpl; auto. rewrite liftExpr_0. f_equal; auto.
    Qed.

    Lemma sexpr_lift_ext : forall EG cs G G' s G'',
      ST.heq cs (sexprD EG (G'' ++ G) s) (sexprD EG (G'' ++ G' ++ G) (liftSExpr (length G'') (length G') s)).
    Proof.
      induction s; simpl; intros; 
        repeat match goal with
                 | [ |- _ ] => rewrite <- liftExpr_ext
                 | [ H : forall a, ST.heq _ _ _ |- _ ] => rewrite <- H
               end; try reflexivity.
      eapply ST.heq_ex. intros. specialize (IHs (existT (tvarD types) t v :: G'')).
      simpl in *. auto.
      destruct (nth_error sfuncs f); try reflexivity.
      clear. destruct s; simpl; clear. generalize dependent SDomain0. induction l; simpl; try reflexivity.
      destruct SDomain0; try reflexivity.
      rewrite <- liftExpr_ext. destruct (exprD funcs EG (G'' ++ G) a t); try reflexivity.
      auto.
    Qed.

    Lemma star_pull_exists : forall EG cs a G s s2,
      heq EG G cs (Star (Exists a s) s2) (Exists a (Star s (liftSExpr 0 1 s2))).
    Proof.
      intros. unfold heq. simpl. rewrite ST.heq_ex_star. apply ST.heq_ex. intros.
      apply ST.heq_star_cancel.
      generalize (sexpr_lift_ext EG cs G (existT (tvarD types) a v :: nil) s2 nil); simpl; intro. auto.
    Qed.            

    Lemma liftSExpr_combine : forall s a b c,
      liftSExpr a b (liftSExpr a c s) = liftSExpr a (c + b) s.
    Proof.
      clear. induction s; intros; simpl; 
      repeat match goal with
               | [ H : _ |- _ ] => rewrite H
             end; try reflexivity. 
      rewrite liftExpr_combine. reflexivity.
      f_equal. rewrite map_map. apply map_ext. intros; apply liftExpr_combine.
    Qed.

    Lemma star_pull_existsEach : forall EG cs v G s s2,
      heq EG G cs (Star (existsEach v s) s2)
      (existsEach v (Star s (liftSExpr 0 (length v) s2))).
    Proof.
      induction v; simpl.
      intros; rewrite liftSExpr_0. reflexivity.

      intros.
      rewrite star_pull_exists. apply heq_ex. intros.
      rewrite IHv.
     
      rewrite liftSExpr_combine. reflexivity.
    Qed.

    Lemma starred'_app : forall EG G cs T (F : T -> _) a b B,
      heq EG G cs (starred' F (a ++ b) B) (starred' F a (starred' F b B)).
    Proof.
      induction a; simpl; intros; try reflexivity.     
      rewrite IHa. reflexivity.
    Qed.

    Lemma multimap_join_remove_acc : forall T k (a b : FM.bst _),
      ~FM.In k a ->
      FM.Equal (FM.remove k (multimap_join (T := T) a b)) (multimap_join a (FM.remove k b)).
    Proof.
      clear. do 3 intro. unfold multimap_join.
      intro.
      eapply NatMap.IntMapProperties.fold_rec with (m := a); intros.
      * rewrite NatMap.IntMapProperties.fold_Empty; eauto with typeclass_instances. reflexivity.
      * rewrite NatMap.IntMapProperties.fold_Add. 2: eauto with typeclass_instances.
        5: eassumption. 4: eauto.
        assert (~ FM.In (elt:=list T) k m').
        { clear H2.
          intro. unfold NatMap.IntMapProperties.Add in H1.
          specialize (H1 k).
          rewrite NatMap.IntMapProperties.F.not_find_in_iff in H3.
          rewrite H3 in *.
          eapply NatMap.IntMapProperties.F.in_find_iff in H2. apply H2.
          rewrite NatMap.IntMapFacts.add_o in H1.
          destruct (NatMap.Ordered_nat.eq_dec k0 k); try congruence.
        }
        apply H2 in H4. clear H2.
        rewrite <- H4.
        rewrite NatMap.IntMapProperties.F.remove_o.
        destruct (NatMap.Ordered_nat.eq_dec k k0).
        { subst. exfalso.
          unfold NatMap.IntMapProperties.Add in *.
          specialize (H1 k0).
          rewrite NatMap.IntMapProperties.F.not_find_in_iff in H3.
          rewrite H3 in *.
          rewrite NatMap.IntMapProperties.F.add_eq_o in H1; auto.
          congruence.
        }
        { destruct (FM.find (elt:=list T) k0 a0).
          unfold FM.Equal; intros.
          rewrite <- H4.
          repeat (rewrite NatMap.IntMapFacts.remove_o || rewrite NatMap.IntMapFacts.add_o).
          destruct (NatMap.Ordered_nat.eq_dec k y); destruct (NatMap.Ordered_nat.eq_dec k0 y); intros; subst; try congruence.
          red; intros.
          rewrite <- H4.
          repeat (rewrite NatMap.IntMapFacts.remove_o || rewrite NatMap.IntMapFacts.add_o).
          destruct (NatMap.Ordered_nat.eq_dec k y); destruct (NatMap.Ordered_nat.eq_dec k0 y); intros; subst; try congruence.
        }
        repeat (red; intros; subst).
        rewrite H4. destruct (FM.find (elt:=list T) y y1); try rewrite H4; reflexivity.
        
        clear. red. intros. 
        red; intros.
        repeat match goal with
                 | [ H : _ = _ |- _ ] => rewrite H in *
                 | [ H : context [ FM.find _ _ ] |- _ ] => 
                   rewrite NatMap.IntMapFacts.add_o in H
                 | [ |- context [ FM.find ?k ?a ] ] =>
                   match a with
                     | match _ with 
                         | Some _ => _
                         | None => _
                       end => fail 1
                     | _ => case_eq (FM.find k a); intros
                   end
               end;
        repeat match goal with
                 | [ H : context [ NatMap.Ordered_nat.eq_dec ?A ?B ] |- _ ] =>
                   destruct (NatMap.Ordered_nat.eq_dec A B); try congruence
               end.
    Qed. 

    Lemma add_remove_Equal : forall (elt : Type) k (v : elt) m,
      FM.Equal (FM.add k v m) (FM.add k v (FM.remove k m)).
    Proof.
      clear. unfold FM.Equal. intros.
      repeat (rewrite NatMap.IntMapFacts.add_o || rewrite NatMap.IntMapFacts.remove_o).
      destruct (NatMap.Ordered_nat.eq_dec k y); auto.
    Qed.

    Lemma multimap_join_star : forall (EG G : env types)
     (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
     (impures0 impures1 : SUBST.bst (list (list (expr types)))) B,
     heq EG G cs
       (FM.fold
         (fun (k : FM.key) (ls : list (list (expr types))) (acc : sexpr) =>
           Star (starred' (Func k) ls Emp) acc)
         (multimap_join impures0 impures1) B)
       (FM.fold
         (fun (k : FM.key) (ls : list (list (expr types))) (acc : sexpr) =>
           Star (starred' (Func k) ls Emp) acc) impures0 
         (FM.fold
           (fun (k : FM.key) (ls : list (list (expr types))) (acc : sexpr) =>
             Star (starred' (Func k) ls Emp) acc) impures1 B)).
    Proof.
      unfold multimap_join.
      do 4 intro. apply NatMap.IntMapProperties.map_induction with (m := impures0).
      * intros.
        repeat rewrite NatMap.IntMapProperties.fold_Empty with (m := m); eauto with typeclass_instances.
        reflexivity.

      * intros.
        generalize (@NatMap.IntMapProperties.fold_Add (list (exprs types)) _ (@FM.Equal (list (exprs types)))).
        intro. 
        rewrite NatMap.IntMapProperties.fold_Equal.
        5: eapply H2; eauto with typeclass_instances.
        clear H2. simpl in *.
        unfold exprs; simpl in *.
        match goal with
          | [ |- context [ FM.find ?x ?y ] ] => remember y
        end.
        case_eq (FM.find x t); intros.
        { subst.
          rewrite NatMap.IntMapProperties.fold_Equal; eauto with typeclass_instances.
          4: eapply add_remove_Equal.
          symmetry.
          rewrite NatMap.IntMapProperties.fold_Add.
          6: eassumption.
          5: eauto.
          2: eauto with typeclass_instances.
          rewrite fold_starred.
          rewrite NatMap.IntMapProperties.fold_Add with (m2 := impures1).
          2: eauto with typeclass_instances.
          instantiate (3 := x). instantiate (2 := l). 
          instantiate (1 := FM.remove x impures1). 
          rewrite NatMap.IntMapProperties.fold_add.
          rewrite starred'_app. rewrite <- starred'_base with (base := starred' _ _ _).
          repeat rewrite heq_star_assoc. apply heq_star_frame; try reflexivity.
          rewrite heq_star_comm. repeat rewrite heq_star_assoc. apply heq_star_frame; try reflexivity.
          
            generalize (@multimap_join_remove_acc _ x m impures1 H0). unfold multimap_join. intro.
            symmetry. rewrite NatMap.IntMapProperties.fold_Equal.
            5: eapply H3. clear H3.
            rewrite H. rewrite fold_starred. heq_canceler. eauto with typeclass_instances.
            
            try solve [ clear; eauto with typeclass_instances | clear; repeat (red; intros; subst); try rewrite H; heq_canceler ].
            try solve [ clear; eauto with typeclass_instances | clear; repeat (red; intros; subst); try rewrite H; heq_canceler ].
            try solve [ clear; eauto with typeclass_instances | clear; repeat (red; intros; subst); try rewrite H; heq_canceler ].
            try solve [ clear; eauto with typeclass_instances | clear; repeat (red; intros; subst); try rewrite H; heq_canceler ].
            try solve [ clear; eauto with typeclass_instances | clear; repeat (red; intros; subst); try rewrite H; heq_canceler ].
            apply FM.remove_1; auto.
            try solve [ clear; eauto with typeclass_instances | clear; repeat (red; intros; subst); try rewrite H; heq_canceler ].
            try solve [ clear; eauto with typeclass_instances | clear; repeat (red; intros; subst); try rewrite H; heq_canceler ].
            apply FM.remove_1; auto.

            { (*
              revert H0; revert H2; clear. unfold NatMap.IntMapProperties.Add. 
              intros. rewrite <- add_remove_Equal. 
              rewrite NatMap.IntMapFacts.add_o. destruct (NatMap.Ordered_nat.eq_dec x y); auto. subst.
              
              revert H2; revert H0. revert y.
              eapply NatMap.IntMapProperties.map_induction with (m := m); intros.
              rewrite NatMap.IntMapProperties.fold_Empty in H2; eauto with typeclass_instances.
              rewrite NatMap.IntMapProperties.fold_Add in H3. 6: eassumption.

              revert H3. case_eq (FM.find (elt:=list (list (expr types))) x
         (NatMap.IntMap.fold
            (fun (k : FM.key) (v : list (list (expr types)))
               (a : FM.t (list (list (expr types)))) =>
             match FM.find (elt:=list (list (expr types))) k a with
             | Some v' => FM.add k (v ++ v') a
             | None => FM.add k v a
             end) m0 impures1)); intros.

              rewrite NatMap.IntMapFacts.add_o in H4. destruct (NatMap.Ordered_nat.eq_dec x y). subst.
              
              
              specialize (H x). rewrite H in H3.
              
              

              destruct (FM.find k a).
               SearchAbout FM.find.
              
              *) admit.
            }

            try solve [ clear; eauto with typeclass_instances | clear; repeat (red; intros; subst); try rewrite H; heq_canceler ].
            try solve [ clear; eauto with typeclass_instances | clear; repeat (red; intros; subst); try rewrite H; heq_canceler ].
            try solve [ clear; eauto with typeclass_instances | clear; repeat (red; intros; subst); try rewrite H; heq_canceler ].
            try solve [ clear; eauto with typeclass_instances | clear; repeat (red; intros; subst); try rewrite H; heq_canceler ].
        }          
        { subst.
          rewrite NatMap.IntMapProperties.fold_add; eauto with typeclass_instances.
          rewrite H. symmetry. rewrite fold_starred. 
          rewrite NatMap.IntMapProperties.fold_Add; eauto with typeclass_instances.
          symmetry. rewrite fold_starred. heq_canceler.
          
          repeat (red; intros; subst). rewrite H3. heq_canceler.
          red; intros; heq_canceler.
          repeat (red; intros; subst). rewrite H3; heq_canceler.
          red; intros; heq_canceler.
          intro.
          apply NatMap.IntMapProperties.F.in_find_iff in H3. auto.
        }
        eauto with typeclass_instances.
        try solve [ clear; eauto with typeclass_instances | clear; repeat (red; intros; subst); try rewrite H; heq_canceler ].
        try solve [ clear; eauto with typeclass_instances | clear; repeat (red; intros; subst); try rewrite H; heq_canceler ].
        clear; repeat (red; intros; subst). rewrite H.
          destruct (FM.find (elt:=list (list (expr types))) y y1); try rewrite H; reflexivity.
        
        clear; repeat (red; intros; subst). unfold exprs in *.
        (repeat match goal with
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
               | [ H : _ = _ |- _ ] => rewrite H 
                | [ H : _ = _ |- _ ] => rewrite H in *
                | [ H : context [ FM.find _ _ ] |- _ ] => 
                  rewrite NatMap.IntMapFacts.add_o in H
                | [ |- context [ FM.find ?k ?a ] ] =>
                  match a with
                    | match _ with 
                        | Some _ => _
                        | None => _
                      end => fail 1
                    | _ => case_eq (FM.find k a); intros
                  end
                end);
              repeat match goal with
                       | [ H : Some _ = Some _ |- _ ] => inversion H ; clear H; subst
                       | [ H : context [ NatMap.Ordered_nat.eq_dec ?A ?B ] |- _ ] =>
                         destruct (NatMap.Ordered_nat.eq_dec A B); try congruence
                     end.
      Qed.
(* NOTE: this is the old proof....
      repeat rewrite FM.Proofs.fold_1; auto with bst_valid. 
      unfold multimap_join. repeat rewrite FM.Proofs.fold_1; auto with bst_valid. 
      generalize dependent (FM.elements impures0). clear H. intros. clear impures0.
      revert B; revert H0; revert impures1.
      induction l; simpl; intros; try reflexivity.

        rewrite IHl. 2: destruct (FM.find (fst a) impures1); auto with bst_valid.
        case_eq (FM.find (fst a) impures1); intros.

        rewrite fold_left_star. symmetry. rewrite fold_left_star.
        apply heq_star_frame; try reflexivity.
        
        apply NatMap.elements_find in H. do 2 destruct H. rewrite H.
        eapply NatMap.elements_add_over in H. rewrite H.
        repeat rewrite fold_left_app. simpl.
        rewrite fold_left_star.

        rewrite starred'_app.
        rewrite <- starred'_base with (base := (starred' (Func (fst a)) l0 Emp)).
        repeat heq_fold_left_opener.

        heq_canceler.
        
        eapply NatMap.elements_add_new in H. do 2 destruct H. intuition. rewrite H2. rewrite H1.
        repeat rewrite fold_left_app; simpl.
        do 2 heq_fold_left_opener. symmetry. do 2 heq_fold_left_opener.
        heq_canceler.
*)

    Lemma sheapD'_star : forall EG G cs s1 s2,
      heq EG G cs (sheapD' (star_SHeap s1 s2)) (Star (sheapD' s1) (sheapD' s2)).
    Proof.
      destruct s1; destruct s2; intros; simpl; unfold sheapD', star_SHeap; simpl.
      match goal with
        | [ |- heq _ _ _ _ (Star (Star ?FL (Star ?PL ?OL)) (Star ?FR (Star ?PR ?OR))) ] =>
          transitivity (Star (Star FL FR) (Star (Star PL PR) (Star OL OR)))
      end.
      repeat apply heq_star_frame.
      Focus.
      rewrite multimap_join_star; auto. 
      repeat rewrite FM.fold_1; auto.
      rewrite fold_left_star. reflexivity.

      (** **)
      clear; induction pures0; simpl.
        rewrite heq_star_emp_l. reflexivity.
        rewrite heq_star_assoc. rewrite IHpures0. reflexivity.

      clear; induction other0; simpl.
        rewrite heq_star_emp_l; reflexivity.
        rewrite heq_star_assoc. rewrite IHother0. reflexivity.

      repeat (repeat rewrite heq_star_assoc; repeat (eapply heq_star_frame; [ reflexivity | ]); rewrite heq_star_comm).
      (repeat rewrite heq_star_assoc; repeat (eapply heq_star_frame; [ reflexivity | ])). reflexivity.
    Qed.

    Lemma fold_left_Star : forall T EG G cs (F : T -> _) ls base base',
      heq EG G cs base base' ->
      heq EG G cs (fold_left (fun acc x => Star (F x) acc) ls base)
      (fold_left (fun acc x => Star (F x) acc) ls base').
    Proof.
      induction ls; simpl; intros; auto.
      rewrite IHls. reflexivity. apply heq_star_frame; auto; reflexivity.
    Qed.

    Lemma starred'_liftSExpr : forall EG G cs F a b (ls : list (expr types)) base,
      (forall a0, heq EG G cs (liftSExpr a b (F a0)) (F (liftExpr a b a0))) ->
      heq EG G cs
      (liftSExpr a b (starred' F ls base))
      (starred' F (map (liftExpr a b) ls) (liftSExpr a b base)).
    Proof.
      induction ls; simpl; intros; try reflexivity.
      rewrite IHls. rewrite H. reflexivity. eauto.
    Qed.


    Lemma sheapD'_sexprD_liftVars : forall EG G cs a b s,
      heq EG G cs (liftSExpr a b (sheapD' s)) (sheapD' (sheap_liftVars a b s)).
    Proof.
      destruct s; unfold sheap_liftVars, sheapD'; simpl; repeat apply heq_star_frame; intros.
(*
        SearchAbout FM.map.
         repeat rewrite FM.fold_1.
         rewrite NatMap.elements_map; eauto with bst_valid. clear.
         change Emp with (liftSExpr a b Emp) at 4; generalize Emp at 2 4.
         induction (FM.elements impures0); intros; simpl; try reflexivity.
         rewrite IHl. simpl. 
         eapply fold_left_Star. apply heq_star_frame; try reflexivity.
         destruct a0; simpl. change Emp with (liftSExpr a b Emp) at 2. generalize Emp. 
         clear; induction l0; simpl; intros; try reflexivity.
         rewrite IHl0. reflexivity.

         rewrite starred'_liftSExpr; reflexivity.
                   
        clear; change Emp with (liftSExpr a b Emp) at 2. generalize Emp; induction other0; try reflexivity; intros.
          simpl; rewrite IHother0. reflexivity.
*)
    Admitted. (** TODO: used to work when reasoning about elements **)

    Lemma liftSExpr_existsEach : forall EG cs v0 s G n v,
      heq EG G cs (liftSExpr n v (existsEach v0 s)) 
                  (existsEach v0 (liftSExpr (n + length v0) v s)).
    Proof.
      induction v0; simpl; intros.
        intros. rewrite Plus.plus_0_r. reflexivity.
      
        apply heq_ex; intros. rewrite IHv0. cutrewrite (S n + length v0 = n + S (length v0)); try reflexivity; omega.
    Qed.

    Lemma hash_denote' : forall EG cs (s : sexpr) G, 
      heq EG G cs s (@existsEach (fst (hash s)) (sheapD' (snd (hash s)))).
    Proof.
      Opaque star_SHeap.
      induction s; simpl; try solve [ unfold sheapD'; simpl; intros; repeat (rewrite heq_star_emp_r || rewrite heq_star_emp_l); reflexivity ].
        (** Exists **)
        Focus 2.
        unfold sheapD'; simpl; intros. case_eq (hash s); intros; simpl.
        eapply heq_ex. intros. specialize (IHs (existT (tvarD types) t v0 :: G)). simpl in *.
        rewrite H in IHs. simpl in *. eauto.

        (** Star **)
        Focus.
        intros. rewrite IHs1 at 1. intros.
        destruct (hash s1); destruct (hash s2); simpl in *.
        rewrite IHs2.
        rewrite <- (@existsEach_app EG cs) with (Y := G).
        rewrite star_pull_existsEach. apply heq_existsEach. intros.
        rewrite heq_star_comm.

        rewrite liftSExpr_existsEach.
        rewrite star_pull_existsEach. eapply heq_existsEach; intros.
        rewrite sheapD'_star. simpl plus.
        repeat rewrite sheapD'_sexprD_liftVars; auto. rewrite heq_star_comm. reflexivity.

        (** Func **)
        Focus.
        intros. unfold sheapD'. simpl. rewrite FM.fold_1. simpl.
        repeat rewrite heq_star_emp_r. reflexivity.
    Qed.
    
    Theorem hash_denote : forall EG cs (s : sexpr) G, 
      heq EG G cs s (@existsEach (fst (hash s)) (sheapD (snd (hash s)))).
    Proof.
      intros. specialize (@hash_denote' EG cs s G). etransitivity.
      eassumption. apply heq_existsEach. intros. rewrite sheapD_sheapD'. reflexivity.
    Qed.

    (** replace "real" variables [a,b) and replace them with
     ** uvars [c,..]
     **)
    Definition sheapSubstU (a b c : nat) (s : SHeap) : SHeap :=
      {| impures := FM.map (map (map (exprSubstU a b c))) (impures s)
       ; pures := map (exprSubstU a b c) (pures s)
       ; other := other s
       |}.

    (** The actual tactic code **)
    Variable Prover : ProverT types.
    Variable Prover_correct : ProverT_correct Prover funcs.

    Section fold_left3_opt.
      Variable T U V A : Type.
      Variable F : T -> U -> V -> A -> option A.

      Fixpoint fold_left_3_opt (ls : list T) (ls' : list U) (ls'' : list V) 
        (acc : A) : option A :=
        match ls, ls', ls'' with 
          | nil , nil , nil => Some acc
          | x :: xs , y :: ys , z :: zs => 
            match F x y z acc with
              | None => None
              | Some acc => fold_left_3_opt xs ys zs acc
            end
          | _ , _ , _ => None
        end.
    End fold_left3_opt.

    Definition unifyArgs (bound : nat) (summ : Facts Prover) (l r : list (expr types)) (ts : list tvar) (sub : Subst types)
      : option (Subst types) :=
      fold_left_3_opt 
        (fun l r t (acc : Subst _) =>
          if Prove Prover summ (Expr.Equal t l r)
            then Some acc
            else exprUnify bound l r acc)
        l r ts sub.

    Fixpoint unify_remove (bound : nat) (summ : Facts Prover) (l : exprs types) (ts : list tvar) (r : list (exprs types))
      (sub : Subst types)
      : option (list (list (expr types)) * Subst types) :=
        match r with 
          | nil => None
          | a :: b => 
            match unifyArgs bound summ l a ts sub with
              | None => 
                match unify_remove bound summ l ts b sub with
                  | None => None
                  | Some (x,sub) => Some (a :: x, sub)
                end
              | Some sub => Some (b, sub)
            end
        end.
(*
    Fixpoint unify_remove_all (bound : nat) (summ : Facts Prover) (l r : list (list (expr types))) (ts : list tvar)
      (sub : Subst types)
      : list (list (expr types)) * list (list (expr types)) * Subst types :=
        match l with
          | nil => (l, r, sub)
          | a :: b => 
            match unify_remove bound summ a ts r sub with
              | None => 
                let '(l,r,sub) := unify_remove_all bound summ b r ts sub in
                (a :: l, r, sub)
              | Some (r, sub) =>
                unify_remove_all bound summ b r ts sub
            end
        end.
*)

    Require Ordering.

    Definition cancel_list : Type := 
      list (exprs types * nat).

    (** This function determines whether an expression [l] is more "defined"
     ** than an expression [r]. An expression is more defined if it "uses UVars later".
     ** NOTE: This is a "fuzzy property" but correctness doesn't depend on it.
     **)
    Fixpoint expr_count_meta (e : expr types) : nat :=
      match e with
        | Expr.Const _ _
        | Var _ => 0
        | UVar _ => 1
        | Not l => expr_count_meta l
        | Equal _ l r => expr_count_meta l + expr_count_meta r
        | Expr.Func _ args =>
          fold_left plus (map expr_count_meta args) 0
      end.

    Definition meta_order_args (l r : exprs types) : Datatypes.comparison :=
      let cmp l r := Compare_dec.nat_compare (expr_count_meta l) (expr_count_meta r) in
      Ordering.list_lex_cmp _ cmp l r.


    Definition meta_order_funcs (l r : exprs types * nat) : Datatypes.comparison :=
      match meta_order_args (fst l) (fst r) with
        | Datatypes.Eq => Compare_dec.nat_compare (snd l) (snd r)
        | x => x
      end.

    Definition order_impures (imps : FM.bst (list (exprs types))) : cancel_list :=
      FM.fold (fun k => fold_left (fun (acc : cancel_list) (args : exprs types) => 
        Ordering.insert_in_order _ meta_order_funcs (args, k) acc)) imps nil.
    
    Fixpoint cancel_in_order (bound : nat) (summ : Facts Prover) 
      (ls : cancel_list) (acc rem : FM.bst (list (exprs types))) (sub : Subst types) 
      : FM.bst (list (exprs types)) * FM.bst (list (exprs types)) * Subst types :=
      match ls with
        | nil => (acc, rem, sub)
        | (args,f) :: ls => 
          match FM.find f rem with
            | None => cancel_in_order bound summ ls (multimap_add f args acc) rem sub
            | Some argss =>
              match nth_error sfuncs f with
                | None => cancel_in_order bound summ ls (multimap_add f args acc) rem sub (** Unused! **)
                | Some ts => 
                  match unify_remove bound summ args (SDomain ts) argss sub with
                    | None => cancel_in_order bound summ ls (multimap_add f args acc) rem sub
                    | Some (rem', sub) =>
                      cancel_in_order bound summ ls acc (FM.add f rem' rem) sub
                  end
              end                      
          end
      end.

    Definition sepCancel (bound : nat) (summ : Facts Prover) (l r : SHeap) :
      SHeap * SHeap * Subst types :=
      let ordered_r := order_impures (impures r) in
      let sorted_l := FM.map (fun v => Ordering.sort _ meta_order_args v) (impures l) in 
      let '(rf, lf, sub) := 
        cancel_in_order bound summ ordered_r (FM.empty _) sorted_l (empty_Subst _)
      in
      ({| impures := lf ; pures := pures l ; other := other l |},
       {| impures := rf ; pures := pures r ; other := other r |},
       sub).

    Theorem sepCancel_correct : forall U G cs bound summ l r l' r' sub ,
      Valid Prover_correct U G summ ->
      sepCancel bound summ l r = (l', r', sub) ->
      himp U G cs (sheapD l) (sheapD r) ->
      himp U G cs (sheapD l') (sheapD r').
    Proof.
      clear. destruct l; destruct r. unfold sepCancel. simpl.
      intros. repeat rewrite sheapD_sheapD'. repeat rewrite sheapD_sheapD' in H1.
      destruct l'; destruct r'. unfold sheapD' in *. simpl in *.
    Admitted.

  End env.

  Implicit Arguments Emp [ types pcType stateType ].
  Implicit Arguments Star [ types pcType stateType ].
  Implicit Arguments Exists [ types pcType stateType ].
  Implicit Arguments Func [ types pcType stateType ].
  Implicit Arguments Const [ types pcType stateType ].
  Implicit Arguments Inj [ types pcType stateType ].


  Lemma change_ST_himp_himp : forall (types : list type)
    (funcs : functions types) (pc st : tvar)
    (sfuncs : list (ssignature types pc st))
    EG G
    (cs : codeSpec (tvarD types pc) (tvarD types st))
    (L R : sexpr types pc st),
    himp funcs sfuncs EG G cs L R ->
    ST.himp cs
      (@sexprD types pc st funcs sfuncs EG G L)
      (@sexprD types pc st funcs sfuncs EG G R).
  Proof.
    unfold himp. intros. auto.
  Qed.

End Make.

Module ReifySepExpr (Import SEP : SepExprType).  

  (** Reflection **)
  Require Import Reflect.

  Ltac lift_ssignature s nt pc st :=
    let d := eval simpl SDomain in (SDomain s) in
    let f := eval simpl SDenotation in (SDenotation s) in
    let res := constr:(@SSig nt pc st d f) in 
    eval simpl in res.

  Ltac lift_ssignatures fs nt :=
    match type of fs with
      | list (ssignature _ ?pc ?st) =>
        let f sig := 
          lift_ssignature sig nt pc st
        in
        map_tac (ssignature nt pc st) f fs
    end.

  (** collect the types from an hprop expression.
   ** - s is an expression of type hprop
   ** - types is a list of raw types, i.e. of type [list Type]
   ** - k is the continuation, it must be an ltac function
   **   that takes a single argument of type [list Type]
   **)
  Ltac collectTypes_sexpr isConst s types k :=
    match s with
      | fun x : VarType ?T => @ST.star _ _ _ (@?L x) (@?R x) =>
        collectTypes_sexpr isConst L types ltac:(fun types =>
          collectTypes_sexpr isConst R types k)
      | fun x : ?T => @ST.ex _ _ _ ?T' (fun y : ?T' => @?B x y) =>
        let v := constr:(fun x : VarType (T * T') => 
          B (@openUp _ T (@fst _ _) x) (@openUp _ T' (@snd _ _) x)) in
        let v := eval simpl in v in
        collectTypes_sexpr isConst v types k
      | fun x : ?T => @ST.inj _ _ _ (PropX.Inj (@?P x)) =>
        k ltac:(collectTypes_expr isConst P types)
      | fun x : ?T => @ST.emp _ _ _ => k types
      | @ST.emp _ _ _ => k types
      | @ST.inj _ _ _ (PropX.Inj ?P) =>
        k ltac:(collectTypes_expr isConst P types)
      | @ST.inj _ _ _ ?PX => k types
      | @ST.star _ _ _ ?L ?R =>
        collectTypes_sexpr isConst L types
          ltac:(fun Ltypes => collectTypes_sexpr isConst R Ltypes k)
      | @ST.ex _ _ _ ?T (fun x : ?T => @?B x) =>
        let v := constr:(fun x : VarType T => B (@openUp _ T (fun x => x) x)) in
        let v := eval simpl in v in 
        collectTypes_sexpr isConst v types k
      | ?X =>
        let rec bt_args args types :=
          match args with
            | tt => k types
            | (?a,?b) => 
              let k := collectTypes_expr isConst a types in
              bt_args b k
          end
        in
        let cc _ Ts args := 
          let types := append_uniq Ts types in
          bt_args args types
        in
        refl_app cc X
    end.

  (** collect types from all of the separation logic goals given
   ** in goals. 
   ** - goals is a gallina list of type [list hprop]
   ** - types is a list of raw types.
   ** - isConst determines when an expression should be treated as a constant.
   **)
  Ltac collectAllTypes_sexpr isConst types goals :=
    match goals with
      | nil => types
      | ?a :: ?b =>
        collectTypes_sexpr isConst a types ltac:(fun ts => 
          collectAllTypes_sexpr isConst ts b)
    end.

  Ltac collectAllTypes_sfunc Ts T :=
    match T with
      | ?t -> ?T =>
        let t := constr:(t : Type) in
        let Ts := cons_uniq t Ts in
        collectAllTypes_sfunc Ts T
      | forall x , _ => 
        (** Can't reflect types for dependent function **)
        fail 100 "can't reflect types for dependent function!"
          "type is " T 
      | _ => Ts (** assume we are at the end **)
    end.

  Ltac collectAllTypes_sfuncs Ts Fs :=
    match Fs with
      | tt => Ts
      | (?Fl, ?Fr) =>
        let Ts := collectAllTypes_sfuncs Ts Fl in
        collectAllTypes_sfuncs Ts Fr
      | ?F =>
        let T := type of F in
        collectAllTypes_sfunc Ts T
    end.

  (** reflect a separation logic predicate. this is analagous 
   ** to reify_function except that it works on separation logic functions.
   **)
  Ltac reify_sfunction pcT stT types f :=
    match f with
      | fun _ => _ =>
        constr:(@SSig types pcT stT (@nil tvar) f)
      | _ =>
        let T := type of f in
          let rec refl dom T :=
            match T with
        (* no dependent types *)
              | ?A -> ?B =>
                let A := reflectType types A in
                  let dom := constr:(A :: dom) in
                    refl dom B 
              | _ =>
                let dom := eval simpl rev in (rev dom) in
                  constr:(@SSig types pcT stT dom f)
            end
            in refl (@nil tvar) T
    end.

  (** get the index for a separation logic predicate. this is analagous
   ** to getFunction.
   ** - k is the continutation which accepts the, possibly extended,
   **  list of separation logic predicates and the index of the desired
   **  predicate.
   **)
  Ltac getSFunction pcT stT types f sfuncs k :=
    let rec lookup sfuncs' acc :=
      match sfuncs' with
        | nil =>
          let F := reify_sfunction pcT stT types f in
          let sfuncs := eval simpl app in (sfuncs ++ (F :: nil)) in
          k sfuncs acc
        | ?F (*SSig _ _ _ ?F *) :: ?FS =>
          match F with 
            | @SSig _ _ _ _ ?F =>
              match F with
                | f => k sfuncs acc 
                | _ => 
                  let acc := constr:(S acc) in
                  lookup FS acc
              end
(*            | @SSig' _ _ _ ?F =>
              match F with
                | f => k sfuncs acc 
                | _ => 
                  let acc := constr:(S acc) in
                  lookup FS acc
              end
*)
          end
      end
    in lookup sfuncs 0.

  Ltac getAllSFunctions pcT stT types sfuncs' fs :=
    match fs with
      | tt => sfuncs'
      | ( ?fl , ?fr ) =>
        let sfuncs := getAllSFunctions pcT stT types sfuncs' fl in
        getAllSFunctions pcT stT types sfuncs fr
      | ?F =>
        getSFunction pcT stT types F sfuncs' ltac:(fun sfuncs _ => sfuncs)
    end.

  About ST.ex.

  (** reflect sexprs. simultaneously gather the unification variables, funcs and sfuncs
   ** k is called with the unification variables, functions, separation logic predicats and the reflected
   ** sexpr.
   **)
  Ltac reify_sexpr isConst s types funcs pcType stateType sfuncs uvars vars k :=
    let implicits ctor :=
      constr:(ctor types pcType stateType) (* (ST.hprop (@tvarD types pcType) (@tvarD types stateType) nil)) *)
    in
    let rec reflect s funcs sfuncs uvars vars k :=
      match s with
        | fun _ => ?s =>
          reflect s funcs sfuncs uvars vars k
        | fun x : VarType ?T => @ST.star _ _ _ (@?L x) (@?R x) =>
          reflect L funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs L =>
            reflect R funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs R => 
              let r := constr:(@Star types pcType stateType L R) in
              k uvars funcs sfuncs r))
        | fun x : ?T => @ST.ex _ _ _ ?T' (fun y => @?B x y) =>
          let v := constr:(fun x : VarType (T' * T) => 
            B (@openUp _ T (@snd _ _) x) (@openUp _ T' (@fst _ _) x)) in
          let v := eval simpl in v in
          let nv := reflectType types T' in
          reflect v funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs B =>
            let r := constr:(@Exists types pcType stateType nv B) in
            k uvars funcs sfuncs r)
        | fun x : ?T => @ST.emp _ _ _ => 
          let r := constr:(@Emp types pcType stateType) in
          k uvars funcs sfuncs r

        | fun x : ?T => @ST.inj _ _ _ (PropX.Inj (@?P x)) =>
          reify_expr isConst P types funcs uvars vars ltac:(fun uvars funcs P =>
            let r := constr:(@Inj types pcType stateType P) in
            k uvars funcs sfuncs r)

        | @ST.emp _ _ _ => 
          let r := constr:(@Emp types pcType stateType) in
          k uvars funcs sfuncs r

        | @ST.inj _ _ _ (PropX.Inj ?P) =>
          reify_expr isConst P types funcs uvars vars ltac:(fun uvars funcs P =>
            let r := constr:(@Inj types pcType stateType P) in
            k uvars funcs sfuncs r)
        | @ST.inj _ _ _ ?PX =>
          let r := constr:(@Const types pcType stateType PX) in
          k uvars funcs sfuncs r
        | @ST.star _ _ _ ?L ?R =>
          reflect L funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs L => 
            reflect R funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs R => 
              let r := constr:(@Star types pcType stateType L R) in
              k uvars funcs sfuncs r))
        | @ST.ex _ _ _ ?T (fun x => @?B x) =>
          let v := constr:(fun x : VarType (T * unit) => B (@openUp _ T (@fst _ _) x)) in
          let v := eval simpl in v in
          let nv := reflectType types T in
          reflect v funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs B =>
            let r := constr:(@Exists types pcType stateType nv B) in
            k uvars funcs sfuncs r)
        | ?X =>
          let rec bt_args args uvars funcs k :=
            match args with
              | tt => 
                let v := constr:(@nil (@expr types)) in
                k uvars funcs v
              | (?a,?b) =>
                reify_expr isConst a types funcs uvars vars ltac:(fun uvars funcs a =>
                  bt_args b uvars funcs ltac:(fun uvars funcs b => 
                  let v := constr:(@cons (@expr types) a b) in
                  k uvars funcs v))
            end
          in
          let cc f Ts As :=
            getSFunction pcType stateType types f sfuncs ltac:(fun sfuncs F =>
            bt_args As uvars funcs ltac:(fun uvars funcs args =>
            let r := constr:(@Func types pcType stateType F args) in
            k uvars funcs sfuncs r))
          in
          refl_app cc X
      end
    in
    reflect s funcs sfuncs uvars vars k.

(*
  (** reflect the list of goals. 
   ** - pcT and stT are raw types that are the pc type and state
   **   type of the goals.
   ** - isConst tells when an expression is a constant.
   ** - Ts is the list of reflected types that should be used as
   **   the base of the reflected types list, i.e. this is guaranteed
   **   to be a prefix of the resulting types list. 
   ** the return value is a 6-tuple containing:
   ** - the list of reflected types
   ** - the tvar corresponding to the pc type
   ** - the tvar corresponding to the state type
   ** - the environment of coq existentials
   ** - the list of reflected functions
   ** - the list of reflected separation logic predicates
   ** - the list of reflected sexpr.
   **)
  Ltac reify_sexprs pcT stT isConst types' funcs sfuncs goals k :=
    let Ts := collectAllTypes_props ltac:(fun _ => true) isConst (@nil Type) in
    let Ts := collectAllTypes_sexpr ltac:(isConst) Ts goals in
    let types := extend_all_types Ts types' in
    let types := eval simpl in types in
    let pcTyp := typesIndex pcT types in
    let stTyp := typesIndex stT types in
    let pcTyp := constr:(tvType pcTyp) in
    let stTyp := constr:(tvType stTyp) in
    let typesV := fresh "types_var" in
    pose (typesV := types) ;
    let funcs := 
      match funcs with
        | tt => constr:(@nil (@signature types))
        | _ => funcs 
      end
    in
    let sfuncs := 
      match sfuncs with
        | tt => constr:(@nil (@ssignature types pcTyp stTyp))
        | _ => sfuncs
      end
    in
    let vars := constr:(@nil tvar) in
    let uvars := constr:(@nil tvar) in
    reify_props ltac:(fun _ => true) isConst types funcs uvars vars ltac:(fun uvars funcs props proofs =>
      let rec reify_all ls uvars funcs sfuncs k :=
        match ls with
          | nil => 
            let r := constr:(@nil (@sexpr types pcTyp stTyp)) in
              k types pcTyp stTyp uvars funcs sfuncs r
          | ?e :: ?es =>
            reify_sexpr isConst e typesV funcs pcTyp stTyp sfuncs uvars vars ltac:(fun uvars funcs sfuncs e =>
              reify_all es uvars funcs sfuncs ltac:(fun types pcType stTyp uvars funcs sfuncs es =>
                let es := constr:(e :: es) in
                  k types pcType stTyp uvars funcs sfuncs es)) 
        end
      in
      let k' := k props proofs in
      match type of funcs with
        | list (signature types) =>
          reify_all goals uvars funcs sfuncs k'
        | ?X =>
          let funcs := lift_signatures funcs types in
            let sfuncs := lift_ssignatures sfuncs types in
              reify_all goals uvars funcs sfuncs k'
      end).
*)



  (** Base simplifier.  For now, copy all this and add your own extra entries to cover prover reductions. *)
(*
  Ltac simplifier :=
    cbv beta iota zeta delta [CancelSep sepCancel hash liftSHeap sheapSubstU liftExpr 
      FM.add FM.fold FM.map FM.find FM.remove FM.empty FM.insert_at_right
      other pures impures star_SHeap SHeap_empty
      unify_remove unify_remove_all exprUnifyArgs exprUnify empty_Subst Subst_lookup env_of_Subst
      Expr.Impl Expr.Eq
      List.map List.length List.app fold_left_2_opt List.fold_right List.nth_error
      starred sheapD exprD
      exprSubstU 
      Compare_dec.lt_eq_lt_dec Compare_dec.lt_dec Peano_dec.eq_nat_dec
      nat_rec nat_rect forallEach env exists_subst multimap_join equiv_dec seq_dec
      Domain Range
      EqDec_tvar tvar_rec tvar_rect 
      lookupAs sumbool_rec sumbool_rect
      fst snd
      eq_rec_r eq_rec eq_rect Logic.eq_sym f_equal get_Eq value 
      nat_eq_eqdec
      (* eq_summary eq_summarize eq_prove *)
   ].
*)
(*
  Ltac sep isConst proverR simplifier types := 
    reify_goal isConst types ltac:(fun props proofs =>
      apply ApplyCancelSep with (hyps := props) (prover := proverR _ _);
        [ exact proofs
          | simplifier; intros; hnf; simpl in * ]).
*)

End ReifySepExpr.

(*
Module ReifyTests (Import SEP : SepExprType).
  
  Parameter pc st : Type.

  Parameter hold : SEP.ST.hprop pc st nil -> Prop.

  Module SEP_REIFY := ReifySepExpr SEP.

  Goal hold (SEP.ST.star (SEP.ST.emp _ _) (SEP.ST.emp _ _)).
    match goal with
      | [ |- hold ?S ] => 
        let isConst x := false in
        SEP_REIFY.collectTypes_sexpr isConst S (@nil Type) ltac:(fun Ts =>
          idtac "0" ;
          let Ts := constr:(pc :: st :: Ts) in
          let types := constr:(@nil type) in
            idtac "1" ;
          let types := extend_all_types Ts types in
            idtac "2" ;
          let pcT := constr:(tvType 0) in
          let stT := constr:(tvType 1) in
          let funcs := constr:(@nil (signature types)) in
          let preds := constr:(@nil (SEP.ssignature types pcT stT)) in
          let vars := constr:(@nil _ : env types) in
            idtac "goign to reflect !" S ;
          SEP_REIFY.reify_sexpr ltac:(fun x => false) S types funcs pcT stT preds vars vars ltac:(fun uvars funcs preds S =>
            idtac uvars funcs preds S))
    end.
*)