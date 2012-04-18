Require Import List.
Require Import Heaps SepTheoryX PropX.
Require Import PropXTac.
Require Import RelationClasses EqdepClass.
Require Import Expr ExprUnify.
Require Import DepList.
Require Import Setoid.
Require Import Prover.

Set Implicit Arguments.

Require NatMap.

Module FM := NatMap.IntMap.

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
      
      Fixpoint sexprD (uvs vs : env types) (s : sexpr)
        : ST.hprop (tvarD types pcType) (tvarD types stateType) nil :=
        match s with 
          | Emp => ST.emp _ _
          | Inj p =>
            match exprD funcs uvs vs p tvProp with
              | None => ST.inj (PropX.Inj False)
              | Some p => ST.inj (PropX.Inj p)
            end
          | Star l r =>
            ST.star (sexprD uvs vs l) (sexprD uvs vs r)
          | Exists t b =>
            ST.ex (fun x : tvarD types t => sexprD uvs (@existT _ _ t x :: vs) b)
          | Func f b =>
            match nth_error preds f with
              | None => ST.inj (PropX.Inj False)
              | Some f =>
                match applyD (@exprD types funcs uvs vs) (SDomain f) b _ (SDenotation f) with
                  | None => ST.inj (PropX.Inj False)
                  | Some p => p
                end
            end
          | Const p => p
        end.

    Definition himp (U1 U2 G : env types)
      (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
      (gl gr : sexpr) : Prop :=
      ST.himp cs (sexprD U1 G gl) (sexprD U2 G gr).

    Definition heq (U1 U2 G : env types)
      (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
      (gl gr : sexpr) : Prop :=
      ST.heq cs (sexprD U1 G gl) (sexprD U2 G gr).

    End funcs_preds.

    Record SHeap : Type :=
    { impures : FM.t (list (list (expr types)))
    ; pures   : list (expr types)
    ; other   : list (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.

    Parameter star_SHeap : SHeap -> SHeap -> SHeap.

    Parameter sheapSubstU : nat -> nat -> nat -> SHeap -> SHeap.

    Parameter hash : sexpr -> variables * SHeap.

    Parameter sheapD : SHeap -> sexpr.

(*
    (** result of cancelation **)
    Record SepResult (gl gr : sexpr) : Type :=
    { r_vars   : variables
    ; r_lhs_ex : variables
    ; r_lhs    : SHeap
    ; r_rhs_ex : variables
    ; r_rhs    : SHeap
    ; r_SUBST  : Subst types
    }.
*)

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

    Fixpoint sexprD (uvs vs : env types) (s : sexpr)
      : ST.hprop (tvarD types pcType) (tvarD types stateType) nil :=
      match s with 
        | Emp => ST.emp _ _
        | Inj p =>
          match exprD funcs uvs vs p tvProp with
            | None => ST.inj (PropX.Inj False)
            | Some p => ST.inj (PropX.Inj p)
          end
        | Star l r =>
          ST.star (sexprD uvs vs l) (sexprD uvs vs r)
        | Exists t b =>
          ST.ex (fun x : tvarD types t => sexprD uvs (@existT _ _ t x :: vs) b)
        | Func f b =>
          match nth_error sfuncs f with
            | None => ST.inj (PropX.Inj False)
            | Some f =>
              match applyD (@exprD types funcs uvs vs) (SDomain f) b _ (SDenotation f) with
                | None => ST.inj (PropX.Inj False)
                | Some p => p
              end
          end
        | Const p => p
      end.

    Definition himp (U1 U2 G : env types)
      (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
      (gl gr : sexpr) : Prop :=
      ST.himp cs (sexprD U1 G gl) (sexprD U2 G gr).

    Definition heq (U1 U2 G : env types)
      (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
      (gl gr : sexpr) : Prop :=
      ST.heq cs (sexprD U1 G gl) (sexprD U2 G gr).

    Section Facts.
      Variables U G : env types.
      Variable cs : codeSpec (tvarD types pcType) (tvarD types stateType).

      Global Instance Trans_himp : Transitive (@himp U U G cs).
      Proof.
        red. unfold himp. intros; etransitivity; eauto.
      Qed.

      Global Instance Trans_heq : Transitive (@heq U U G cs).
      Proof.
        red. unfold heq. intros; etransitivity; eauto.
      Qed.

      Global Instance Refl_himp : Reflexive (@himp U U G cs).
      Proof.
        red; unfold himp; intros. reflexivity.
      Qed.

      Global Instance Refl_heq : Reflexive (@heq U U G cs).
      Proof.
        red; unfold heq; intros. reflexivity.
      Qed.

      Global Instance Sym_heq : Symmetric (@heq U U G cs).
      Proof.
        red; unfold heq; intros. symmetry. auto.    
      Qed.

      Add Parametric Relation : sexpr (@himp U U G cs)
        reflexivity proved by  Refl_himp
        transitivity proved by Trans_himp
      as himp_rel.

      Add Parametric Relation : sexpr (@heq U U G cs)
        reflexivity proved by  Refl_heq
        symmetry proved by Sym_heq
        transitivity proved by Trans_heq
      as heq_rel.

      Global Add Parametric Morphism U' : Star with
        signature (himp U U' G cs ==> himp U U' G cs ==> himp U U' G cs)      
        as star_himp_mor.
        unfold himp; simpl; intros; eapply SEP_FACTS.star_himp_mor; eauto.
      Qed.

      Global Add Parametric Morphism U' : Star with
        signature (heq U U' G cs ==> heq U U' G cs ==> heq U U' G cs)      
        as star_heq_mor.
        unfold himp; simpl; intros; eapply SEP_FACTS.star_heq_mor; eauto.
      Qed.

      Global Add Parametric Morphism U' : (himp U U' G cs) with 
        signature (heq U U G cs ==> heq U' U' G cs ==> Basics.impl)
        as himp_heq_mor.
        unfold heq; simpl; intros. eapply SEP_FACTS.himp_heq_mor; eauto.
      Qed.

      Global Add Parametric Morphism U' : (himp U U' G cs) with 
        signature (himp U U G cs --> himp U' U' G cs ++> Basics.impl)
        as himp_himp_mor.
        unfold himp; simpl; intros. eapply SEP_FACTS.himp_himp_mor; eauto.
      Qed.

      Global Add Parametric Morphism : (sexprD U G) with 
        signature (heq U U G cs ==> ST.heq cs)
        as heq_ST_heq_mor.
        unfold heq; simpl; auto.
      Qed.

      Lemma heq_star_emp_r : forall P, 
        heq U U G cs (Star P Emp) P.
      Proof.
        unfold heq; simpl; intros; autorewrite with hprop; reflexivity.
      Qed.

      Lemma heq_star_emp_l : forall P, 
        heq U U G cs (Star Emp P) P.
      Proof.
        unfold heq; simpl; intros; autorewrite with hprop; reflexivity.
      Qed.

      Lemma heq_star_assoc : forall P Q R, 
        heq U U G cs (Star (Star P Q) R) (Star P (Star Q R)).
      Proof.
        unfold heq; simpl; intros; autorewrite with hprop. rewrite ST.heq_star_assoc. reflexivity.
      Qed.

      Lemma heq_star_comm : forall P Q, 
        heq U U G cs (Star P Q) (Star Q P).
      Proof.
        unfold heq; simpl; intros; apply ST.heq_star_comm.
      Qed.

      Lemma heq_star_frame : forall P Q R S, 
        heq U U G cs P R ->
        heq U U G cs Q S ->
        heq U U G cs (Star P Q) (Star R S).
      Proof.
        unfold heq; simpl; intros. eapply ST.heq_star_frame; auto.
      Qed.
      
      Lemma himp_star_frame : forall a b c cs P Q R S,
        himp a b c cs P R ->
        himp a b c cs Q S ->
        himp a b c cs (Star P Q) (Star R S).
      Proof.
        unfold himp; simpl; intros. rewrite H; rewrite H0; reflexivity.
      Qed.
        
    End Facts.

    Existing Instance himp_rel_relation.
    Existing Instance heq_rel_relation.
    Hint Rewrite heq_star_emp_l heq_star_emp_r : hprop.

    Theorem ST_himp_himp : forall (U1 U2 G : env types) cs L R,
      himp U1 U2 G cs L R ->
      ST.himp cs (sexprD U1 G L) (sexprD U2 G R).
    Proof.
      clear. auto.
    Qed.

    Theorem ST_heq_heq : forall (U1 U2 G : env types) cs L R,
      heq U1 U2 G cs L R ->
      ST.heq cs (sexprD U1 G L) (sexprD U2 G R).
    Proof.
      clear. auto.
    Qed.

    

    (** A more efficient representation for sexprs. **)
    Record SHeap : Type :=
    { impures : FM.t (list (list (expr types)))
    ; pures   : list (expr types)
    ; other   : list (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.
  
    Definition SHeap_empty : SHeap := 
      {| impures := @FM.empty _
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

    (** lift all the "real" variables in [a,...) 
     ** to the range [a+b,...)
     **)
    Definition liftSHeap (a b : nat) (s : SHeap) : SHeap :=
      {| impures := FM.map (fun _ => map (map (liftExpr a b))) (impures s)
       ; pures   := map (liftExpr a b) (pures s)
       ; other   := other s
       |}.

    Fixpoint multimap_join T (l r : FM.t (list T)) : FM.t (list T) :=
      FM.fold (fun k v a =>
        match FM.find k a with
          | None => FM.add k v a
          | Some v' => FM.add k (v ++ v') a
        end) l r.

    Fixpoint star_SHeap (l r : SHeap) : SHeap :=
      {| impures := multimap_join (impures l) (impures r)
       ; pures := pures l ++ pures r
       ; other := other l ++ other r
       |}.

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
      end.

    (** convert the sexpr into a SHeap **)
    Fixpoint hash' (nextVar : nat) (vs : list nat) (s : sexpr) : ( variables * SHeap ) :=
      match s with
        | Emp => (nil, SHeap_empty)
        | Inj p => (nil,
          {| impures := FM.empty
            ; pures := substV vs p :: nil
            ; other := nil
          |})
        | Star l r =>
          let (vl, hl) := hash' nextVar vs l in
          let (vr, hr) := hash' (nextVar + length vl) vs r in
          (vl ++ vr,
            star_SHeap hl hr)
        | Exists t b =>
          let (v, b) := hash' (S nextVar) (nextVar :: vs) b in
          (t :: v, b)
        | Func f a =>
          (nil,
           {| impures := FM.add f (map (substV vs) a :: nil) FM.empty
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

    Definition hash := hash' O nil.
 
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
      heq a a c cs base base' ->
      (forall x, heq a a c cs (F x) (F' x)) ->
      heq a a c cs (@starred T F ls base) (@starred' T F' ls base').
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
      heq a a c cs (Star (@starred' T F ls Emp) base) (@starred' T F ls base).
    Proof.
      unfold heq in *; simpl in *.
      induction ls; simpl; intros.
        autorewrite with hprop; reflexivity.
        rewrite <- IHls. rewrite ST.heq_star_assoc. reflexivity.
    Qed.

    Lemma starred_base : forall a c cs T F base ls, 
      heq a a c cs (Star (@starred T F ls Emp) base) (@starred T F ls base).
    Proof.
      unfold heq in *; simpl in *.
      induction ls; simpl; intros.
        autorewrite with hprop; reflexivity.
        Opaque exprD.
        destruct (starred F ls base); destruct (starred F ls Emp);
          simpl in *; autorewrite with hprop in *; try rewrite ST.heq_star_assoc; try rewrite IHls;
            autorewrite with hprop; try reflexivity.
    Qed.

    Lemma fold_starred : forall X a c cs (F : nat -> X -> sexpr) m b,
      heq a a c cs (FM.fold (fun k ls a => Star (F k ls) a) m b)
      (Star (FM.fold (fun k ls a => Star (F k ls) a) m Emp) b).
    Proof.
      induction m; simpl; intros.
      autorewrite with hprop; reflexivity.

      rewrite IHm2. rewrite IHm1. symmetry. rewrite IHm2.
      repeat rewrite heq_star_assoc. reflexivity.
    Qed.

    Lemma impures' : forall a c cs i b, 
      heq a a c cs (FM.fold (fun k => starred (Func k)) i b)
      (Star (FM.fold (fun k ls a => Star (starred' (Func k) ls Emp) a) i Emp) b).
    Proof.
      induction i; simpl; intros.
      autorewrite with hprop. reflexivity.
(*
      rewrite IHi2. rewrite <- starred_base. rewrite IHi1.
      symmetry. 
      rewrite fold_starred. repeat rewrite heq_star_assoc.
      apply heq_star_frame. reflexivity.
      apply heq_star_frame; try reflexivity.
      rewrite starred_starred'; try reflexivity. 
    Qed.
*)
    Admitted.

    Theorem sheapD_sheapD' : forall a c cs h, 
      heq a a c cs (sheapD h) (sheapD' h).
    Proof.
(*
      destruct h; unfold sheapD, sheapD'; simpl.
      rewrite impures'. rewrite <- starred_base. 
      rewrite <- starred_base with (ls := other0).
      eapply heq_star_frame. reflexivity.
      eapply heq_star_frame. eapply starred_starred'; reflexivity.
      autorewrite with hprop.
      eapply starred_starred'; reflexivity.
    Qed.
*)
    Admitted.

    Lemma starred_In : forall T (F : T -> sexpr) a c cs x ls' b ls,
      heq a a c cs (starred F (ls ++ x :: ls') b) (Star (starred F (ls ++ ls') b) (F x)).
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
          change G with (himp uvars uvars vars cs (sheapD h) (sheapD' h))
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
        | [ |- ST.himp ?C (sexprD ?U1 ?V ?L) (sexprD ?U2 ?V ?R) ] =>
          change (ST.himp C (sexprD U1 V L) (sexprD U2 V R)) with
            (himp U1 U2 V C L R)
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

    Lemma insert_at_right_star : forall a c cs i1 i2 b, 
      heq a a c cs (FM.fold
        (fun (k : nat) (ls : list (list (expr types)))
          (acc : sexpr) =>
          Star (starred' (Func k) ls Emp) acc)
        (FM.insert_at_right i1 i2) b)
      (Star (FM.fold
        (fun (k : nat) (ls : list (list (expr types)))
          (acc : sexpr) =>
          Star (starred' (Func k) ls Emp) acc)
        i1 Emp)
      (FM.fold
        (fun (k : nat) (ls : list (list (expr types)))
          (acc : sexpr) =>
          Star (starred' (Func k) ls Emp) acc)
        i2 b)).
    Proof.
      induction i1; simpl; intros.
      autorewrite with hprop. reflexivity.

      clear IHi1_1. rewrite IHi1_2. rewrite fold_starred.
      rewrite heq_star_assoc.
      symmetry. rewrite fold_starred. rewrite heq_star_assoc.
      apply heq_star_frame. reflexivity.
      rewrite heq_star_comm. rewrite fold_starred. 
      symmetry. rewrite fold_starred. autorewrite with hprop.
      repeat rewrite heq_star_assoc. apply heq_star_frame.
      reflexivity. rewrite fold_starred. symmetry; rewrite heq_star_comm.
      rewrite heq_star_assoc. reflexivity.
    Qed.

    Lemma sheapD_pull_impure : forall a c cs h f argss,
      FM.find f (impures h) = Some argss ->
      heq a a c cs (sheapD h)
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
      rewrite heq_star_assoc. apply heq_star_frame. reflexivity.
      rewrite heq_star_comm. reflexivity.

      (** **)
      simpl in *.
      generalize dependent H. clear.
      induction impures0; simpl; try congruence.
      destruct (Compare_dec.lt_eq_lt_dec f n); [ destruct s | ]; simpl.
      intros. specialize (IHimpures0_1 H).
      rewrite fold_starred. symmetry. rewrite fold_starred.
      rewrite heq_star_assoc. apply heq_star_frame; try reflexivity.
      rewrite IHimpures0_1. rewrite heq_star_assoc. reflexivity.
      inversion 1; subst. clear.
      rewrite starred_starred'. 2: reflexivity. 2: reflexivity.

      rewrite insert_at_right_star.
      rewrite fold_starred.
      symmetry. rewrite heq_star_comm. (* rewrite <- heq_star_assoc.
      rewrite heq_star_comm. reflexivity.

      intros.
      rewrite fold_starred. rewrite IHimpures0_2 by assumption.
      symmetry. rewrite fold_starred. 
      rewrite starred_starred'; [ | reflexivity | reflexivity ].
      repeat rewrite heq_star_assoc. apply heq_star_frame; try reflexivity.
      symmetry. rewrite heq_star_comm. rewrite heq_star_assoc.
      reflexivity.
    Qed.
*)
    Admitted.

    Fixpoint existsEach (ls : list tvar) {struct ls} : sexpr -> sexpr :=
      match ls with
        | nil => fun x => x
        | t :: ts => fun y => Exists t (@existsEach ts y)
      end.
    
    Lemma heq_ex : forall X Y cs t P Q,
      (forall v : tvarD types t, heq X X (existT (tvarD types) t v :: Y) cs P Q) ->
      heq X X Y cs (Exists t P) (Exists t Q).
    Proof.
      unfold heq; simpl; intros; apply ST.heq_ex; auto.
    Qed.

    Lemma existsEach_heq : forall cs X v Y (P Q : sexpr),
      (forall Z, heq X X (Z ++ Y) cs P Q) ->
      heq X X Y cs (existsEach v P) (existsEach v Q).
    Proof.
      induction v; simpl; intros.
        apply (H nil).
        eapply heq_ex. intros.
        eapply IHv. intros. specialize (H (Z ++ existT (tvarD types) a v0 :: nil)).
        rewrite app_ass in *. simpl in *. eauto.
    Qed.

    Lemma existsEach_app : forall X cs b a Y (P : sexpr),
      heq X X Y cs (existsEach a (existsEach b P)) (existsEach (a ++ b) P).
    Proof.
      induction a; simpl.
        reflexivity.
        intros. apply heq_ex. intros. eauto.
    Qed.

    Theorem hash_denote : forall cs (s : sexpr) EG G, 
      heq EG EG G cs s 
        (@existsEach (fst (hash s)) (sheapD (snd (hash s)))).
    (*Proof.
      induction s; simpl; try (unfold sheapD; reflexivity).
        intros.
        rewrite IHs1 at 1. rewrite IHs2 at 1. clear IHs1 IHs2.
        destruct (hash s1); destruct (hash s2); simpl. clear. admit.
        
        destruct (hash s); simpl in *. intros. apply heq_ex. intros. eauto.
    Qed.*)
    Admitted.

    (** replace "real" variables [a,b) and replace them with
     ** uvars [c,..]
     **)
    Definition sheapSubstU (a b c : nat) (s : SHeap) : SHeap :=
      {| impures := FM.map (fun _ => map (map (exprSubstU a b c))) (impures s)
       ; pures := map (exprSubstU a b c) (pures s)
       ; other := other s
       |}.

    (** The actual tactic code **)
    Variable Prover : ProverT types.
    Variable Prover_correct : ProverT_correct Prover funcs.

    Definition unifyArgs (summ : Facts Prover) (l r : list (expr types)) (ts : list tvar) (ls rs : Subst types)
      : option (Subst types * Subst types) :=
      ExprUnify.fold_left_3_opt 
        (fun l r t (acc : Subst _ * Subst _) =>
          match exprUnify l r (fst acc) (snd acc) with
            | None => if Prove Prover summ (Expr.Equal t l r) then Some acc else None
            | x => x
          end)
        l r ts (ls, rs).

    Fixpoint unify_remove (summ : Facts Prover) (l : list (expr types)) (ts : list tvar) (r : list (list (expr types)))
      (ls rs : ExprUnify.Subst types)
      : option (list (list (expr types)) * ExprUnify.Subst types * ExprUnify.Subst types) :=
        match r with 
          | nil => None
          | a :: b => 
            match unifyArgs summ l a ts ls rs with
              | None => 
                match unify_remove summ l ts b ls rs with
                  | None => None
                  | Some (x,y,z) => Some (a :: x, y, z)
                end
              | Some (ls,rs) => Some (b, ls, rs)
            end
        end.

    Fixpoint unify_remove_all (summ : Facts Prover) (l r : list (list (expr types))) (ts : list tvar)
      (ls rs : ExprUnify.Subst types)
      : list (list (expr types)) * list (list (expr types)) * 
        ExprUnify.Subst types * ExprUnify.Subst types :=
        match l with
          | nil => (l, r, ls, rs)
          | a :: b => 
            match unify_remove summ a ts r ls rs with
              | None => 
                let '(l,r,ls,rs) := unify_remove_all summ b r ts ls rs in
                (a :: l, r, ls, rs)
              | Some (r, ls, rs) =>
                unify_remove_all summ b r ts ls rs
            end
        end.

    (** TODO: this function signature is going to change **)
    Definition sepCancel (summ : Facts Prover) (l r : SHeap) :
      SHeap * SHeap * ExprUnify.Subst types * ExprUnify.Subst types :=
      let '(lf, rf, ls, rs) := 
        FM.fold (fun k v a => 
          let '(lf, rf, ls, rs) := a in
          match FM.find k rf with
            | None => (FM.add k v lf, rf, ls, rs)
            | Some xs =>
              match nth_error sfuncs k with
                | None => (* should never happen *)
                  (FM.add k v lf, rf, ls, rs)
                | Some sf =>
                  let ts  := SDomain sf in
                  let '(l,r,ls,rs) := unify_remove_all summ v xs ts ls rs in
                  (FM.add k l lf, FM.add k r rf, ls, rs)
              end
          end)
        (impures l)
        (FM.empty , impures r , empty_Subst _ , empty_Subst _)
      in
      ({| impures := lf ; pures := pures l ; other := other l |},
       {| impures := rf ; pures := pures r ; other := other r |},
       ls, rs).

(*
    Record SepResult (gl gr : sexpr) : Type :=
    { r_vars   : variables
    ; r_lhs_ex : variables
    ; r_lhs    : SHeap
    ; r_rhs_ex : variables
    ; r_rhs    : SHeap
    ; r_SUBST  : Subst types
    }.

    (** TODO: I should reconsider this... 
     ** - I think the correct interface here is to spit out two sexprs
     **)
    Definition CancelSep (uvars : env types)
      : list (expr types) -> forall (gl gr : sexpr), SepResult gl gr :=
        fun hyps gl gr =>
        let (ql, lhs) := hash gl in
        let (qr, rhs) := hash gr in
        let summ := Summarize Prover (hyps ++ pures lhs) in
        let rhs' := liftSHeap 0 (length ql) (sheapSubstU 0 (length qr) (length uvars) rhs) in
        let '(lhs',rhs',lhs_subst,rhs_subst) := sepCancel summ lhs rhs' in
        {| r_vars := ql 
         ; r_lhs := lhs' ; r_lhs_ex := nil
         ; r_rhs := rhs' ; r_rhs_ex := map (@projT1 _ _) uvars ++ qr ; r_SUBST := rhs_subst
         |}.

    (** TODO: this isn't true **)
    Theorem ApplyCancelSep : forall cs uvars hyps l r,
      AllProvable funcs uvars nil hyps ->
      match CancelSep uvars hyps l r with
        | {| r_vars := vars 
           ; r_lhs_ex := lhs_ex ; r_lhs := lhs
           ; r_rhs_ex := rhs_ex ; r_rhs := rhs 
           ; r_SUBST := SUBST |} =>
          forallEach vars (fun VS : env types =>
            exists_subst funcs VS uvars (env_of_Subst SUBST rhs_ex 0)
            (fun rhs_ex : env types => 
              himp nil rhs_ex VS cs (sheapD lhs) (sheapD rhs)))
      end ->
      himp nil uvars nil cs l r.
    Proof.
      intros. case_eq (CancelSep uvars hyps l r); intros.
      rewrite H1 in H0. revert Prover_correct.
      admit.
    Qed.
*)

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
    
    (cs : codeSpec (tvarD types pc) (tvarD types st))
    (L R : sexpr types pc st),
    himp funcs sfuncs nil nil nil cs L R ->
    ST.himp cs
      (@sexprD types pc st funcs sfuncs nil nil L)
      (@sexprD types pc st funcs sfuncs nil nil R).
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
        (** TODO : I may need to reflect the pcType and stateType **)
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
   in refl (@nil tvar) T.

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
              let r := constr:(@Star) in
              let r := implicits r in
              let r := constr:(r L R) in
              k uvars funcs sfuncs r))
        | fun x : ?T => @ST.ex _ _ _ ?T' (fun y => @?B x y) =>
          let v := constr:(fun x : VarType (T' * T) => 
            B (@openUp _ T (@snd _ _) x) (@openUp _ T' (@fst _ _) x)) in
          let v := eval simpl in v in
          let nv := reflectType types T' in
          let vars' := constr:(nv :: vars) in
          reflect v funcs sfuncs uvars vars' ltac:(fun uvars funcs sfuncs B =>
            let r := constr:(@Exists) in
            let r := implicits r in
            let r := constr:(@r nv B) in
            k uvars funcs sfuncs r)
        | fun x : ?T => @ST.emp _ _ _ => 
          let r := constr:(@Emp) in
          let r := implicits r in
          k uvars funcs sfuncs r

        | fun x : ?T => @ST.inj _ _ _ (PropX.Inj (@?P x)) =>
          reify_expr isConst P types funcs uvars vars ltac:(fun uvars funcs P =>
            let r := constr:(@Inj) in
            let r := implicits r in
            let r := constr:(r P) in
            k uvars funcs sfuncs r)

        | @ST.emp _ _ _ => 
          let r := constr:(@Emp) in
          let r := implicits r in
          k uvars funcs sfuncs r

        | @ST.inj _ _ _ (PropX.Inj ?P) =>
          reify_expr isConst P types funcs uvars vars ltac:(fun uvars funcs P =>
            let r := constr:(@Inj) in
            let r := implicits r in
            let r := constr:(r P) in
            k uvars funcs sfuncs r)
        | @ST.inj _ _ _ ?PX =>
          let r := constr:(@Const) in
          let r := implicits r in
          let r := constr:(r PX) in
          k uvars funcs sfuncs r
        | @ST.star _ _ _ ?L ?R =>
          reflect L funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs L => 
            reflect R funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs R => 
              let r := constr:(@Star) in
              let r := implicits r in
              let r := constr:(r L R) in
              k uvars funcs sfuncs r))
        | @ST.ex _ _ _ ?T (fun x => @?B x) =>
          let v := constr:(fun x : VarType (T * unit) => B (@openUp _ T (@fst _ _) x)) in
          let v := eval simpl in v in
          let nv := reflectType types T in
          let vars' := constr:(nv :: vars) in
          reflect v funcs sfuncs uvars vars' ltac:(fun uvars funcs sfuncs B =>
            let r := constr:(@Exists) in
            let r := implicits r in
            let r := constr:(@r nv B) in
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
            let r := constr:(@Func) in
            let r := implicits r in
            let r := constr:(@r F args) in
            k uvars funcs sfuncs r))
          in
          refl_app cc X
      end
    in
    reflect s funcs sfuncs uvars vars k.

(*
Ltac reify_exprs isConst ss types funcs pcType stateType sfuncs uvars vars k :=
*)


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