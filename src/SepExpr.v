Require Import List.
Require Import SepTheoryX PropX.
Require Import PropXTac.
Require Import RelationClasses EqdepClass.
Require Import Expr.
Require Import Setoid.
Require Import Folds Bool Tactics.

Set Implicit Arguments.
Set Strict Implicit.

Definition BadInj types (e : expr types) := False.
Definition BadPred (f : func) := False.
Definition BadPredApply types (f : func) (es : list (expr types)) (_ : env types) := False.

Module Type SepExpr.
  Declare Module ST : SepTheoryX.SepTheoryX.

  Section env.
    Variable types : list type.
    Variable pcType : tvar.
    Variable stateType : tvar.

    Record predicate := PSig {
      SDomain : list tvar ;
      SDenotation : functionTypeD (map (@tvarD types) SDomain) (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.

    Definition predicates : Type := list predicate.

    Parameter Default_predicate : predicate.

    Inductive sexpr : Type :=
    | Emp : sexpr
    | Inj : expr types -> sexpr
    | Star : sexpr -> sexpr -> sexpr
    | Exists : tvar -> sexpr -> sexpr
    | Func : func -> list (expr types) -> sexpr
    | Const : ST.hprop (tvarD types pcType) (tvarD types stateType) nil -> sexpr
    .

    Definition tpredicate : Type := list tvar.
    Definition tpredicates : Type := list tpredicate.

    Definition Predicate_typeof : predicate -> tpredicate := SDomain.
    Definition Predicates_typeof : predicates -> tpredicates := map Predicate_typeof.

    Section types.
      Variable funcs : tfunctions.
      Variable preds : tpredicates.
      Variable tU : tenv.

      Fixpoint WellTyped_sexpr (tG : tenv) (s : sexpr) : bool :=
        match s with
          | Emp => true
          | Inj e => is_well_typed funcs tU tG e tvProp
          | Star l r => WellTyped_sexpr tG l && WellTyped_sexpr tG r
          | Exists t e => WellTyped_sexpr (t :: tG) e
          | Func f args =>
            match nth_error preds f with
              | None => false
              | Some ts => all2 (is_well_typed funcs tU tG) args ts
            end
          | Const _ => true
        end.

    End types.

    (** sexprD (U ++ U') (G ++ G') e <===>
     ** sexprD (U ++ U'' ++ U') (G ++ G'' ++ G')
     **    (liftSExpr (length U) (length U'') (length G) (length G'') e)
     **)
    Fixpoint liftSExpr ua ub a b s : sexpr :=
      match s with
        | Emp => Emp
        | Const c => Const c
        | Inj p => Inj (liftExpr ua ub a b p)
        | Star l r => Star (liftSExpr ua ub a b l) (liftSExpr ua ub a b r)
        | Exists t s => Exists t (liftSExpr ua ub (S a) b s)
        | Func f args => Func f (map (liftExpr ua ub a b) args)
      end.

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
                  | None => ST.inj (PropX.Inj (BadPredApply f b var_env))
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

    Fixpoint existsEach (ls : list tvar) {struct ls} : sexpr -> sexpr :=
      match ls with
        | nil => fun x => x
        | t :: ts => fun y => Exists t (@existsEach ts y)
      end.

  End env.

  Implicit Arguments Emp [ types pcType stateType ].
  Implicit Arguments Star [ types pcType stateType ].
  Implicit Arguments Exists [ types pcType stateType ].
  Implicit Arguments Func [ types pcType stateType ].
  Implicit Arguments Const [ types pcType stateType ].
  Implicit Arguments Inj [ types pcType stateType ].

End SepExpr.

Require Import Reflection.

Module SepExprFacts (SE : SepExpr).
  Module SEP_FACTS := SepTheoryX_Rewrites SE.ST.

  Section env.
    Variable types : list type.
    Variable pcType : tvar.
    Variable stateType : tvar.
    Variable funcs : functions types.
    Variable preds : SE.predicates types pcType stateType.
    
    Variables U G : env types.
    Variable cs : codeSpec (tvarD types pcType) (tvarD types stateType).

    Global Instance Trans_himp : Transitive (@SE.himp types _ _ funcs preds U G cs).
    Proof.
      red. unfold SE.himp. intros; etransitivity; eauto.
    Qed.

    Global Instance Trans_heq : Transitive (@SE.heq types _ _ funcs preds U G cs).
    Proof.
      red. unfold SE.heq. intros; etransitivity; eauto.
    Qed.

    Global Instance Refl_himp : Reflexive (@SE.himp types _ _ funcs preds U G cs).
    Proof.
      red; unfold SE.himp; intros. reflexivity.
    Qed.

    Global Instance Refl_heq : Reflexive (@SE.heq types _ _ funcs preds U G cs).
    Proof.
      red; unfold SE.heq; intros. reflexivity.
    Qed.

    Global Instance Sym_heq : Symmetric (@SE.heq types _ _ funcs preds U G cs).
    Proof.
      red; unfold SE.heq; intros. symmetry. auto.    
    Qed.

    Global Instance Equiv_heq : Equivalence (SE.heq funcs preds U G cs).
    Proof.
      constructor; eauto with typeclass_instances.
    Qed.

    Lemma heq_defn : forall P Q,
      (@SE.himp types _ _ funcs preds U G cs P Q /\
       @SE.himp types _ _ funcs preds U G cs Q P) <->
      (@SE.heq types _ _ funcs preds U G cs P Q).
    Proof.
      unfold SE.heq, SE.himp. intros; apply SE.ST.heq_defn. 
    Qed.

    Lemma heq_himp : forall P Q,
      @SE.heq types _ _ funcs preds U G cs P Q ->
      @SE.himp types _ _ funcs preds U G cs P Q.
    Proof.
      unfold SE.heq, SE.himp. intros; apply SE.ST.heq_himp; auto.
    Qed.

    Lemma himp_not_WellTyped : forall tfuncs tG tU f P Q l,
      WellTyped_env tU U ->
      WellTyped_env tG G ->
      WellTyped_funcs tfuncs funcs ->
      (forall p, 
        nth_error preds f = Some p ->
        Folds.all2 (@is_well_typed types tfuncs tU tG) l (SE.SDomain p) = true ->
        SE.himp funcs preds U G cs (SE.Star (SE.Func f l) P) Q) ->
      SE.himp funcs preds U G cs (SE.Star (SE.Func f l) P) Q.
    Proof.
      intros. unfold SE.himp in *; simpl in *. consider (nth_error preds f); intros;
        try solve [ eapply SE.ST.himp_star_pure_c; contradiction ].
      match goal with
        | [ |- context [ match ?X with | _ => _ end ] ] =>
          case_eq X
      end; intros; try solve [ eapply SE.ST.himp_star_pure_c; contradiction ].
      specialize (H3 _ refl_equal). rewrite <- H3. rewrite H4. reflexivity.

      clear H2. clear H3. destruct p; simpl in *. generalize dependent l.
      induction SDomain; destruct l; simpl; intros; auto; try congruence.
      revert H4. consider (exprD funcs U G e a); intros.
      erewrite is_well_typed_correct_only by eauto. eapply IHSDomain; eauto. congruence.
    Qed.

    Add Parametric Relation : (@SE.sexpr types pcType stateType) (@SE.himp types _ _ funcs preds U G cs)
      reflexivity proved by  Refl_himp
      transitivity proved by Trans_himp
    as himp_rel.

    Add Parametric Relation : (@SE.sexpr types pcType stateType) (@SE.heq types _ _ funcs preds U G cs)
      reflexivity proved by  Refl_heq
      symmetry proved by Sym_heq
      transitivity proved by Trans_heq
    as heq_rel.

    Global Add Parametric Morphism : (@SE.Star types pcType stateType) with
      signature (SE.himp funcs preds U G cs ==> SE.himp funcs preds U G cs ==> SE.himp funcs preds U G cs)      
      as star_himp_mor.
    Proof.
      unfold SE.himp; simpl; intros; eapply SEP_FACTS.star_himp_mor; eauto.
    Qed.

    Global Add Parametric Morphism : (@SE.Star types pcType stateType) with
      signature (SE.heq funcs preds U G cs ==> SE.heq funcs preds U G cs ==> SE.heq funcs preds U G cs)      
      as star_heq_mor.
    Proof.
      unfold SE.himp; simpl; intros; eapply SEP_FACTS.star_heq_mor; eauto.
    Qed.

    Global Add Parametric Morphism : (SE.himp funcs preds U G cs) with 
      signature (SE.heq funcs preds U G cs ==> SE.heq funcs preds U G cs ==> Basics.impl)
      as himp_heq_mor.
    Proof.
      unfold SE.heq; simpl; intros. eapply SEP_FACTS.himp_heq_mor; eauto.
    Qed.

    Global Add Parametric Morphism : (SE.himp funcs preds U G cs) with 
      signature (SE.himp funcs preds U G cs --> SE.himp funcs preds U G cs ==> Basics.impl)
      as himp_himp_mor.
    Proof.
      unfold SE.himp; simpl; intros. intro. etransitivity. eauto. etransitivity; eauto.
    Qed.

    Global Add Parametric Morphism : (SE.himp funcs preds U G cs) with 
      signature (SE.himp funcs preds U G cs --> SE.himp funcs preds U G cs ++> Basics.impl)
      as himp_himp_mor'.
    Proof.
      unfold SE.himp; simpl; intros. eapply SEP_FACTS.himp_himp_mor; eauto.
    Qed.

    Global Add Parametric Morphism : (SE.sexprD funcs preds U G) with 
      signature (SE.heq funcs preds U G cs ==> SE.ST.heq cs)
      as heq_ST_heq_mor.
    Proof.
      unfold SE.heq; simpl; auto.
    Qed.

    Lemma heq_star_emp_r : forall P, 
      SE.heq funcs preds U G cs (SE.Star P SE.Emp) P.
    Proof.
      unfold SE.heq; simpl; intros; autorewrite with hprop; reflexivity.
    Qed.

    Lemma heq_star_emp_l : forall P, 
      SE.heq funcs preds U G cs (SE.Star SE.Emp P) P.
    Proof.
      unfold SE.heq; simpl; intros; autorewrite with hprop; reflexivity.
    Qed.

    Lemma heq_star_assoc : forall P Q R, 
      SE.heq funcs preds U G cs (SE.Star (SE.Star P Q) R) (SE.Star P (SE.Star Q R)).
    Proof.
      unfold SE.heq; simpl; intros; autorewrite with hprop. rewrite SE.ST.heq_star_assoc. reflexivity.
    Qed.

    Lemma heq_star_comm : forall P Q, 
      SE.heq funcs preds U G cs (SE.Star P Q) (SE.Star Q P).
    Proof.
      unfold SE.heq; simpl; intros; apply SE.ST.heq_star_comm.
    Qed.

    Lemma heq_star_frame : forall P Q R S, 
      SE.heq funcs preds U G cs P R ->
      SE.heq funcs preds U G cs Q S ->
      SE.heq funcs preds U G cs (SE.Star P Q) (SE.Star R S).
    Proof.
      unfold SE.heq; simpl; intros. eapply SE.ST.heq_star_frame; auto.
    Qed.
    
    Lemma himp_star_frame : forall P Q R S,
      SE.himp funcs preds U G cs P R ->
      SE.himp funcs preds U G cs Q S ->
      SE.himp funcs preds U G cs (SE.Star P Q) (SE.Star R S).
    Proof.
      unfold SE.himp; simpl; intros. rewrite H; rewrite H0; reflexivity.
    Qed.
    
    Lemma heq_star_comm_p : forall P Q R,
      SE.heq funcs preds U G cs (SE.Star P Q) R ->
      SE.heq funcs preds U G cs (SE.Star Q P) R.
    Proof.
      intros. rewrite heq_star_comm. auto.
    Qed.

    Lemma heq_star_comm_c : forall P Q R,
      SE.heq funcs preds U G cs R (SE.Star P Q) ->
      SE.heq funcs preds U G cs R (SE.Star Q P).
    Proof.
      intros. rewrite heq_star_comm. auto.
    Qed.

    Lemma heq_star_assoc_p1 : forall P Q R S,
      SE.heq funcs preds U G cs (SE.Star P (SE.Star Q R)) S ->
      SE.heq funcs preds U G cs (SE.Star (SE.Star P Q) R) S.
    Proof.
      intros. rewrite heq_star_assoc; auto.
    Qed.

    Lemma heq_star_assoc_p2 : forall P Q R S,
      SE.heq funcs preds U G cs (SE.Star Q (SE.Star P R)) S ->
      SE.heq funcs preds U G cs (SE.Star (SE.Star P Q) R) S.
    Proof.
      intros. apply heq_star_assoc_p1 in H. rewrite <- H.
      apply heq_star_frame; try reflexivity. rewrite heq_star_comm. reflexivity.
    Qed.

    Lemma heq_star_assoc_c1 : forall P Q R S,
      SE.heq funcs preds U G cs S (SE.Star P (SE.Star Q R)) ->
      SE.heq funcs preds U G cs S (SE.Star (SE.Star P Q) R).
    Proof.
      intros. rewrite heq_star_assoc; auto.
    Qed.

    Lemma heq_star_assoc_c2 : forall P Q R S,
      SE.heq funcs preds U G cs S (SE.Star Q (SE.Star P R)) ->
      SE.heq funcs preds U G cs S (SE.Star (SE.Star P Q) R).
    Proof.
      intros. apply heq_star_assoc_c1 in H. rewrite H.
      apply heq_star_frame; try reflexivity. apply heq_star_comm; reflexivity.
    Qed.

    Lemma heq_star_emp_p : forall P S,
      SE.heq funcs preds U G cs P S ->
      SE.heq funcs preds U G cs (SE.Star SE.Emp P) S.
    Proof.
      intros. rewrite heq_star_emp_l. auto.
    Qed.

    Lemma heq_star_emp_c : forall P S,
      SE.heq funcs preds U G cs S P ->
      SE.heq funcs preds U G cs S (SE.Star SE.Emp P).
    Proof.
      intros. rewrite heq_star_emp_l. auto.
    Qed.

  End env.

  Ltac heq_canceler :=
    let cancel cp ap1 ap2 ep cc ac1 ac2 ec frm P Q :=
      let rec iter_right Q :=
        match Q with 
          | SE.Emp =>
            apply ec
          | SE.Star ?L ?R =>
            (apply ac1 ; iter_right L) || (apply ac2 ; iter_right R)
          | _ => 
            apply frm; [ reflexivity | ]
        end
      in
      let rec iter_left P :=
        match P with
          | SE.Emp =>
            apply ep
          | SE.Star ?L ?R =>
            (apply ap1 ; iter_left L) || (apply ap2 ; iter_left R)
          | _ => 
            match Q with
              | SE.Star ?A ?B =>
                iter_right A || (apply cc; iter_right B)
            end
        end
      in
      match P with 
        | SE.Star ?A ?B =>
          iter_left A || (apply cp; iter_left B)
      end
    in
    repeat (rewrite heq_star_emp_l || rewrite heq_star_emp_r) ;
    repeat match goal with
             | [ |- SE.heq _ _ _ _ _ ?P ?Q ] =>
               cancel heq_star_comm_p heq_star_assoc_p1 heq_star_assoc_p2 heq_star_emp_p 
                      heq_star_comm_c heq_star_assoc_c1 heq_star_assoc_c2 heq_star_emp_c
                      heq_star_frame P Q
(*    | [ |- SE.himp _ _ _ _ _ ?P ?Q ] =>
   cancel himp_star_comm_p himp_star_assoc_p himp_star_comm_c himp_star_assoc_c P Q
   *)
    end; try reflexivity.

  Section other.
    Variable types : list type.
    Variables pcT stT : tvar.
    Variable funcs : functions types.
    Variable preds : SE.predicates types pcT stT.
    Variable cs : codeSpec (tvarD types pcT) (tvarD types stT).

    Theorem sexprD_weaken : forall s U G G' U',
      SE.ST.himp cs (SE.sexprD funcs preds U G s) 
                    (SE.sexprD funcs preds (U ++ U') (G ++ G') s).
    Proof.
      induction s; simpl; intros; try reflexivity.
      { consider (exprD funcs U G e tvProp); intros.
        erewrite exprD_weaken by eauto. reflexivity.
        rewrite <- SE.ST.heq_star_emp_r.
        eapply SE.ST.himp_star_pure_c. contradiction. }
      { rewrite IHs1. rewrite IHs2. reflexivity. }
      { apply SE.ST.himp_ex. intros. rewrite IHs with (U' := U') (G' := G'). reflexivity. }
      { destruct (nth_error preds f); try reflexivity.
        match goal with
          | [ |- SE.ST.himp _ match ?X with _ => _ end _ ] => 
            consider X
        end; intros.
        erewrite Expr.applyD_weaken by eauto. reflexivity.
        rewrite <- SE.ST.heq_star_emp_r.
        eapply SE.ST.himp_star_pure_c. unfold BadPredApply. contradiction. }
    Qed.

    Theorem liftSExpr_sexprD : forall cs s U U' U'' G G' G'', 
      SE.ST.heq cs (SE.sexprD funcs preds (U ++ U') (G ++ G') s)
                   (SE.sexprD funcs preds (U ++ U'' ++ U') (G ++ G'' ++ G') 
                     (SE.liftSExpr (length U) (length U'') (length G) (length G'') s)).
    Proof.
      do 8 intro. revert G. induction s; simpl; intros; think; try reflexivity.
      rewrite <- liftExpr_ext. reflexivity.
      apply SE.ST.heq_ex. intros. etransitivity. 
      change (existT (tvarD types) t v :: G ++ G') with ((existT (tvarD types) t v :: G) ++ G'). eapply IHs. reflexivity.
      destruct (nth_error preds f); try reflexivity.
      match goal with
        | [ |- SE.ST.heq _ match ?X with _ => _ end match ?Y with _ => _ end ] =>
          cutrewrite (X = Y); try reflexivity
      end.
      destruct p; simpl. clear. revert l; induction SDomain; destruct l; simpl; auto.
      rewrite <- liftExpr_ext. destruct (exprD funcs (U ++ U') (G ++ G') e a); eauto.
    Qed.

    Theorem liftSExpr_combine : forall (s : SE.sexpr types pcT stT) ua ub uc a b c,
      SE.liftSExpr ua ub a b (SE.liftSExpr ua uc a c s) = 
      SE.liftSExpr ua (uc + ub) a (c + b) s.
    Proof.
      clear. induction s; intros; simpl; think; try reflexivity.
      rewrite liftExpr_combine. reflexivity.
      f_equal. clear. induction l; simpl; intros; try rewrite liftExpr_combine; think; auto.
    Qed.

    Theorem liftSExpr_0 : forall (s : SE.sexpr types pcT stT) ua a,
      SE.liftSExpr ua 0 a 0 s = s.
    Proof.
      clear; induction s; intros; simpl; think; try reflexivity.
      rewrite liftExpr_0; auto.
      f_equal. clear. induction l; simpl; intros; try rewrite liftExpr_0; think; auto.
    Qed.
  End other.

End SepExprFacts.

Module Make (ST' : SepTheoryX.SepTheoryX) <: SepExpr with Module ST := ST'.
  Module ST := ST'.

  Section env.
    Variable types : list type.
    Variable pcType : tvar.
    Variable stateType : tvar.

    Record predicate := PSig {
      SDomain : list tvar ;
      SDenotation : functionTypeD (map (@tvarD types) SDomain) (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.

    Definition predicates := list predicate.

    Definition Default_predicate : predicate :=
    {| SDomain := nil
     ; SDenotation := @ST.emp _ _ _
     |} .

    Inductive sexpr : Type :=
    | Emp : sexpr
    | Inj : expr types -> sexpr
    | Star : sexpr -> sexpr -> sexpr
    | Exists : tvar -> sexpr -> sexpr
    | Func : func -> list (expr types) -> sexpr
    | Const : ST.hprop (tvarD types pcType) (tvarD types stateType) nil -> sexpr
    .

    Definition tpredicate : Type := list tvar.
    Definition tpredicates : Type := list tpredicate.

    Definition Predicate_typeof : predicate -> tpredicate := SDomain.
    Definition Predicates_typeof : predicates -> tpredicates := map Predicate_typeof.

    Section types.
      Variable funcs : tfunctions.
      Variable preds : tpredicates.
      Variable tU : tenv.

      Fixpoint WellTyped_sexpr (tG : tenv) (s : sexpr) : bool :=
        match s with
          | Emp => true
          | Inj e => is_well_typed funcs tU tG e tvProp
          | Star l r => WellTyped_sexpr tG l && WellTyped_sexpr tG r
          | Exists t e => WellTyped_sexpr (t :: tG) e
          | Func f args =>
            match nth_error preds f with
              | None => false
              | Some ts => all2 (is_well_typed funcs tU tG) args ts
            end
          | Const _ => true
        end.

    End types.

    Variable funcs : functions types.
    Variable sfuncs : predicates.

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
                | None => ST.inj (PropX.Inj (BadPredApply f b var_env))
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

    Fixpoint existsEach (ls : list tvar) {struct ls} : sexpr -> sexpr :=
      match ls with
        | nil => fun x => x
        | t :: ts => fun y => Exists t (@existsEach ts y)
      end.

    Fixpoint liftSExpr ua ub a b s : sexpr :=
      match s with
        | Emp => Emp
        | Const c => Const c
        | Inj p => Inj (liftExpr ua ub a b p)
        | Star l r => Star (liftSExpr ua ub a b l) (liftSExpr ua ub a b r)
        | Exists t s => Exists t (liftSExpr ua ub (S a) b s)
        | Func f args => Func f (map (liftExpr ua ub a b) args)
      end.    

  End env.
End Make.

Module ReifySepExpr (Import SEP : SepExpr).  
  Import ReifyExpr.

  (** Reflection **)
  Require Import Reflect.

  Ltac reflectable shouldReflect P :=
    match P with
      | @PropX.interp _ _ _ _ => false
      | @PropX.valid _ _ _ _ _ => false
      | forall x, _ => false
      | context [ PropX.PropX _ _ ] => false
      | context [ PropX.spec _ _ ] => false
      | _ => match type of P with
               | Prop => shouldReflect P
             end
    end.

  Ltac lift_predicate s nt pc st :=
    let d := eval simpl SDomain in (SDomain s) in
    let f := eval simpl SDenotation in (SDenotation s) in
    let res := constr:(@PSig nt pc st d f) in 
    eval simpl in res.

  Ltac lift_predicates fs nt :=
    match type of fs with
      | list (predicate _ ?pc ?st) =>
        let f sig := 
          lift_predicate sig nt pc st
        in
        map_tac (predicate nt pc st) f fs
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
        constr:(@PSig types pcT stT (@nil tvar) f)
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
                  constr:(@PSig types pcT stT dom f)
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
        | ?F :: ?FS =>
          match F with 
            | @PSig _ _ _ _ ?F =>
              match F with
                | f => k sfuncs acc 
                | _ => 
                  let acc := constr:(S acc) in
                  lookup FS acc
              end
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

  (** reflect sexprs. simultaneously gather the unification variables, funcs and sfuncs
   ** k is called with the unification variables, functions, separation logic predicats and the reflected
   ** sexpr.
   **)
  Ltac reify_sexpr isConst s types funcs pcType stateType sfuncs uvars vars k :=
    let implicits ctor :=
      constr:(ctor types pcType stateType)
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

End ReifySepExpr.
