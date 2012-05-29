Require Import List.
Require Import SepTheoryX PropX.
Require Import PropXTac.
Require Import RelationClasses EqdepClass.
Require Import Expr SepExpr.
Require Import DepList.
Require Import Setoid.

Set Implicit Arguments.
Set Strict Implicit.

Require NatMap Multimap.

Module FM := NatMap.IntMap.
Module MM := Multimap.Make FM.
Module MF := NatMap.MoreFMapFacts FM.

Module Type SepHeap.
  Declare Module SE : SepExpr.

  Section env.
    Variable types : list type.
    Variable pcType : tvar.
    Variable stateType : tvar.

    Record SHeap : Type :=
    { impures : MM.mmap (exprs types)
    ; pures   : list (expr types)
    ; other   : list (SE.ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.

    (** TODO: What happens if I denote this directly to hprop?
     ** - fewer lemmas about concrete syntax!
     ** - can't re-hash (probably don't want to do this anyways...)
     ** * I think this is Ok for now
     **)
    Parameter sheapD : SHeap -> SE.sexpr types pcType stateType.

    (** Operations on [SHeap]s **)
    Parameter star_SHeap : SHeap -> SHeap -> SHeap.

    Parameter sheap_liftVars : nat -> nat -> SHeap -> SHeap.

    Parameter sheapSubstU : nat -> nat -> nat -> SHeap -> SHeap.

    (** Convert an [sexpr] to an [SHeap] **)
    Parameter hash : SE.sexpr types pcType stateType -> variables * SHeap.

    Parameter impuresD : MM.mmap (exprs types) -> SE.sexpr types pcType stateType.

    Parameter starred : forall (T : Type) (F : T -> SE.sexpr types pcType stateType), 
      list T -> SE.sexpr types pcType stateType -> SE.sexpr types pcType stateType.
    
    Section facts.
      Variable funcs : functions types.
      Variable preds : SE.predicates types pcType stateType.
      Variables U G : env types.
      Variable cs : codeSpec (tvarD types pcType) (tvarD types stateType).

      (** Theorems **)
      Axiom hash_denote : forall (s : SE.sexpr types pcType stateType), 
        SE.heq funcs preds U G cs s (SE.existsEach (fst (hash s)) (sheapD (snd (hash s)))).

      Axiom star_SHeap_denote : forall s s',
        SE.heq funcs preds U G cs (SE.Star (sheapD s) (sheapD s')) (sheapD (star_SHeap s s')).

      (** Definitions **)
      Axiom starred_def : forall (T : Type) (F : T -> SE.sexpr _ _ _) (ls : list T) (base : SE.sexpr _ _ _),
        SE.heq funcs preds U G cs 
            (starred F ls base)
            (fold_right (fun x a => SE.Star (F x) a) base ls).

      Axiom starred_base : forall (T : Type) (F : T -> SE.sexpr _ _ _) (ls : list T) (base : SE.sexpr _ _ _),
        SE.heq funcs preds U G cs 
            (starred F ls base)
            (SE.Star base (starred F ls SE.Emp)).

      Axiom starred_app : forall (T : Type) (F : T -> SE.sexpr _ _ _) (ls ls' : list T) (base : SE.sexpr _ _ _),
        SE.heq funcs preds U G cs 
            (starred F (ls ++ ls') base)
            (starred F ls (starred F ls' base)).

      Axiom starred_perm : forall T L R,
        Permutation.Permutation L R ->
        forall (F : T -> _) base,
          SE.heq funcs preds U G cs (starred F L base) (starred F R base).

      Axiom impuresD_Add : forall f argss i i',
        MM.PROPS.Add f argss i i' ->
        ~FM.In f i ->
        SE.heq funcs preds U G cs
            (impuresD i')
            (SE.Star (starred (SE.Func f) argss SE.Emp) (impuresD i)).

      Axiom impuresD_Empty : forall i,
        FM.Empty i ->
        SE.heq funcs preds U G cs
            (impuresD i) SE.Emp.

      Axiom impuresD_Equiv : forall a b,
        MM.mmap_Equiv a b ->
        SE.heq funcs preds U G cs (impuresD a) (impuresD b).

      Axiom sheapD_def : forall s,
        SE.heq funcs preds U G cs
            (sheapD s)
            (SE.Star (impuresD (impures s))
                     (SE.Star (starred (@SE.Inj _ _ _) (pures s) SE.Emp)
                              (starred (@SE.Const _ _ _) (other s) SE.Emp))).
    End facts.
  End env.
End SepHeap.

Module Make (SE : SepExpr) <: SepHeap with Module SE := SE.
  Module Import SE := SE.
  Module ST := SE.ST.

  Module Import SE_FACTS := SepExpr.SepExprFacts SE.

  Section env.
    Variable types : list type.
    Variable pcType : tvar.
    Variable stateType : tvar.

    Variable funcs : functions types.
    Variable preds : predicates types pcType stateType.

    (** A more efficient representation for sexprs. **)
    Record SHeap : Type :=
    { impures : MM.mmap (exprs types)
    ; pures   : list (expr types)
    ; other   : list (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.
  
    Definition SHeap_empty : SHeap := 
      {| impures := @MM.empty _
       ; pures   := nil
       ; other   := nil
       |}.

    Existing Instance himp_rel_relation.
    Existing Instance heq_rel_relation.
    Hint Rewrite heq_star_emp_l heq_star_emp_r : hprop.

    Theorem ST_himp_himp : forall (U G : env types) cs L R,
      SE.himp funcs preds U G cs L R ->
      ST.himp cs (sexprD funcs preds U G L) (sexprD funcs preds U G R).
    Proof.
      clear. auto.
    Qed.

    Theorem ST_heq_heq : forall (U G : env types) cs L R,
      heq funcs preds U G cs L R ->
      ST.heq cs (sexprD funcs preds U G L) (sexprD funcs preds U G R).
    Proof.
      clear. auto.
    Qed.


    (** lift all the "real" variables in [a,...) 
     ** to the range [a+b,...)
     **)
    Fixpoint liftSExpr (a b : nat) (s : sexpr types pcType stateType) : sexpr _ _ _ :=
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
      {| impures := MM.mmap_map (map (liftExpr a b)) (impures s)
       ; pures   := map (liftExpr a b) (pures s)
       ; other   := other s
       |}.

    Fixpoint star_SHeap (l r : SHeap) : SHeap :=
      {| impures := MM.mmap_join (impures l) (impures r)
       ; pures := pures l ++ pures r
       ; other := other l ++ other r
       |}.

    Definition sheap_liftVars (from : nat) (delta : nat) (h : SHeap) : SHeap :=
      {| impures := MM.mmap_map (map (liftExpr from delta)) (impures h)
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
        | Less e1 e2 => Less (substV vs e1) (substV vs e2)
        | Not e1 => Not (substV vs e1)
      end.

    Fixpoint hash (s : sexpr types pcType stateType) : ( variables * SHeap ) :=
      match s with
        | Emp => (nil, SHeap_empty)
        | Inj p => (nil,
          {| impures := MM.empty _
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
           {| impures := MM.mmap_add f a (MM.empty _)
            ; pures := nil
            ; other := nil
           |})
        | Const c => 
          (@nil tvar,
           {| impures := MM.empty _
            ; pures := @nil (expr types)
            ; other := c :: nil
            |})
      end.

    Definition starred (T : Type) (F : T -> sexpr types pcType stateType) (ls : list T) (base : sexpr _ _ _)
      : sexpr _ _ _ :=
      fold_right (fun x a => match a with 
                               | Emp => F x
                               | _ => Star (F x) a
                             end) base ls.     

    Definition sheapD (h : SHeap) : sexpr types pcType stateType :=
      let a := starred (@Const _ _ _) (other h) Emp in
      let a := starred (@Inj _ _ _) (pures h) a in
      let a := FM.fold (fun k => starred (Func k)) (impures h) a in
      a.

    Definition sheapD' (h : SHeap) : sexpr types pcType stateType :=
      Star (FM.fold (fun k => starred (Func k)) (impures h) Emp)
           (Star (starred (@Inj _ _ _) (pures h) Emp)
                 (starred (@Const _ _ _) (other h) Emp)).

    Definition impuresD (imp : MM.mmap (exprs types)) : sexpr types pcType stateType :=
      FM.fold (fun k ls acc => 
        Star (starred (Func k) ls Emp) acc) imp Emp.

    Section with_envs.
      Variables U G : env types.
      Variable cs : codeSpec (tvarD types pcType) (tvarD types stateType).

      Local Notation "a '<===>' b" := (heq funcs preds U G cs a b) (at level 60, only parsing).

      Theorem starred_def : forall (T : Type) (F : T -> SE.sexpr _ _ _) (ls : list T) (base : SE.sexpr _ _ _),
        (starred F ls base) <===>
        (fold_right (fun x a => SE.Star (F x) a) base ls).
      Proof.
        induction ls; simpl; intros.
          reflexivity.
          specialize (IHls base). revert IHls.
          case_eq (starred F ls base); intros;
            rewrite <- IHls; heq_canceler.
      Qed.

      Theorem starred_base : forall T F ls base, 
        (@starred T F ls base) <===> (SE.Star base (@starred T F ls Emp)).
      Proof.
        intros. repeat rewrite starred_def.
        revert base. induction ls; simpl in *; intros.
          heq_canceler.
          rewrite IHls. heq_canceler.
      Qed.
      
      Ltac heq_canceler :=
        repeat match goal with
                 | [ H : SE.heq _ _ _ _ _ _ _ |- _ ] => rewrite H
                 | [ |- context [ starred ?F ?L ?B ] ] =>
                   match B with
                     | SE.Emp => fail 1
                     | _ => rewrite (@starred_base _ F L B)
                   end
               end;
        SE_FACTS.heq_canceler.

      Global Add Parametric Morphism : (fun k0 : nat => starred (Func k0)) with
        signature (eq ==> eq ==> heq funcs preds U G cs ==> heq funcs preds U G cs)
        as star_himp_mor'.
      Proof.
        intros. repeat rewrite starred_def.
        revert H. revert x; revert y1.
        induction y0; unfold heq in *; simpl in *; intros; try eauto.
        rewrite IHy0; eauto. heq_canceler.
      Qed.

      Lemma transpose_neqkey_starred : NatMap.IntMapProperties.transpose_neqkey (SE.heq funcs preds U G cs)
        (fun k0 : nat => starred (Func k0)).
      Proof.
        red. intros. rewrite starred_base. symmetry.
        rewrite starred_base. repeat rewrite starred_base with (base := a).
        heq_canceler.
      Qed.
      Lemma transpose_neqkey_Star (X : Type) F : NatMap.IntMapProperties.transpose_neqkey (heq funcs preds U G cs)
        (fun (k0 : nat) (ls : X) (a1 : sexpr types _ _) => Star (F k0 ls) a1).
      Proof.
        red. intros. heq_canceler.
      Qed.

      Hint Resolve transpose_neqkey_starred transpose_neqkey_Star : hprop.
      Hint Extern 1 (Morphisms.Proper _ _) =>
        (unfold Morphisms.Proper, Morphisms.respectful; intros; subst; 
          repeat match goal with
                   | [ H : heq _ _ _ _ _ _ _ |- _ ] => rewrite H
                 end; reflexivity) : hprop.
      Hint Extern 1 (MM.PROPS.transpose_neqkey _ _) => 
        (clear; red; intros; subst; repeat rewrite MM.FACTS.add_o;
          repeat match goal with 
                   | [ |- context [ FM.E.eq_dec ?X ?Y ] ] => 
                     destruct (FM.E.eq_dec X Y)
                   | [ H : FM.E.eq ?X ?Y |- _ ] => rewrite H in *
                 end; solve [ auto | exfalso; auto | heq_canceler ]) : hprop.


      Theorem impuresD_Add : forall f argss i i',
        MM.PROPS.Add f argss i i' ->
        ~FM.In f i ->
        SE.heq funcs preds U G cs
          (impuresD i')
          (SE.Star (starred (SE.Func f) argss SE.Emp) (impuresD i)).
      Proof.
        unfold impuresD; intros.
        rewrite MM.PROPS.fold_Add; eauto with typeclass_instances hprop.
          heq_canceler.
      Qed.
        
      Theorem impuresD_Empty : forall i,
        FM.Empty i ->
        SE.heq funcs preds U G cs (impuresD i) SE.Emp.
      Proof.
        unfold impuresD; intros.
        rewrite MM.PROPS.fold_Empty; eauto with typeclass_instances. heq_canceler.
      Qed.

      Theorem sheapD_def : forall s,
        SE.heq funcs preds U G cs
          (sheapD s)
          (SE.Star (impuresD (impures s))
                   (SE.Star (starred (@SE.Inj _ _ _) (pures s) SE.Emp)
                            (starred (@SE.Const _ _ _) (other s) SE.Emp))).
      Proof.
        intros; unfold sheapD.
        eapply MM.PROPS.fold_rec; intros.
          rewrite impuresD_Empty; eauto. heq_canceler. 
          rewrite impuresD_Add; eauto. heq_canceler. 
      Qed.

      Lemma sheapD_sheapD' : forall h,
        sheapD h <===> sheapD' h.
      Proof.
        destruct h. rewrite sheapD_def; unfold sheapD', impuresD; simpl. 
        repeat eapply heq_star_frame; try reflexivity.
        generalize (@Emp types pcType stateType) at 2 3.
        clear. intros. eapply MM.PROPS.fold_rec with (m := impures0); intros.
          rewrite MM.PROPS.fold_Empty; eauto with typeclass_instances hprop. reflexivity.

          rewrite MM.PROPS.fold_Add; eauto with typeclass_instances hprop.
            rewrite H2. heq_canceler. 
      Qed.

      Lemma starred_In : forall T (F : T -> sexpr _ _ _) x ls' b ls,
        (starred F (ls ++ x :: ls') b) <===> (Star (starred F (ls ++ ls') b) (F x)).
      Proof.
        intros. repeat rewrite starred_def. revert b.
        induction ls; intros; simpl; heq_canceler. 
          rewrite IHls. heq_canceler.
      Qed.

      Lemma sheapD_pures : forall stn sm h,
        ST.satisfies cs (sexprD funcs preds U G (sheapD h)) stn sm ->
        AllProvable funcs U G (pures h).
      Proof.
        intros. eapply ST.satisfies_himp in H.
        Focus 2. rewrite sheapD_def. rewrite starred_def. reflexivity.
        simpl in *.
        
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : ST.satisfies _ (ST.star _ _) _ _ |- _ ] =>
                   apply ST.satisfies_star in H
                 | [ H : _ /\ _ |- _ ] => destruct H
               end.
        revert H2; clear. revert x1.
        induction (pures h); simpl; auto.
        unfold Provable. destruct (exprD funcs U G a tvProp); intros; unfold BadInj in *;
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : ST.satisfies _ (ST.star _ _) _ _ |- _ ] =>
                   apply ST.satisfies_star in H
                 | [ H : ST.satisfies _ (ST.inj _) _ _ |- _ ] =>
                   apply ST.satisfies_pure in H
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ |- _ /\ _ ] => split
                 | [ |- _ ] => propxFo
               end; eauto.
      Qed.

      Lemma sheapD_pull_impure : forall h f argss,
        FM.find f (impures h) = Some argss ->
        (sheapD h) <===>
        (Star (sheapD {| impures := FM.remove f (impures h)
          ; pures   := pures h
          ; other   := other h |})
        (starred (Func f) argss Emp)).
      Proof.
        intros. repeat rewrite sheapD_def. simpl.
        rewrite impuresD_Add with (f := f) (argss := argss) (i := FM.remove f (impures h)). 
        heq_canceler.
        unfold MM.PROPS.Add; intros; repeat rewrite MM.FACTS.add_o; repeat rewrite MM.FACTS.remove_o.
        destruct (FM.E.eq_dec f y); subst; auto.
        apply FM.remove_1; auto.
      Qed.

      Lemma fold_starred : forall X (F : nat -> X -> sexpr _ _ _) m b,
        (FM.fold (fun k ls a => Star (F k ls) a) m b) <===>
        (Star (FM.fold (fun k ls a => Star (F k ls) a) m Emp) b).
      Proof.
        do 2 intro.
        intro. apply NatMap.IntMapProperties.fold_rec with (m := m).
          intros. rewrite NatMap.IntMapProperties.fold_Empty; eauto with typeclass_instances.
          autorewrite with hprop. reflexivity.

          intros. erewrite MM.PROPS.fold_Add; eauto with typeclass_instances hprop.
          rewrite H2. heq_canceler.
      Qed.

      Theorem starred_app : forall T (F : T -> _) a b B,
        (starred F (a ++ b) B) <===> (starred F a (starred F b B)).
      Proof.
        intros; repeat rewrite starred_def.
        induction a; simpl; intros; repeat rewrite starred_def; try reflexivity.     
        rewrite IHa. reflexivity.
      Qed.

      Theorem starred_perm : forall T L R,
        Permutation.Permutation L R ->
        forall (F : T -> _) base,
          (starred F L base) <===> (starred F R base).
      Proof.
        clear. intros.
        repeat rewrite starred_def.
        induction H; simpl; intros;
          repeat match goal with
                   | [ H : _ |- _ ] => rewrite H
                 end; try reflexivity; heq_canceler.
      Qed.

      Theorem impuresD_Equiv : forall a b,
        MM.mmap_Equiv a b ->
        (impuresD a) <===> (impuresD b).
      Proof.
        intro. eapply MM.PROPS.map_induction with (m := a); intros.
        { repeat rewrite impuresD_Empty; auto. reflexivity.
          apply MF.find_empty_iff. intros.
          destruct H0. 
          specialize (H0 k). 
          eapply MF.find_empty_iff with (k := k) in H.
          apply MM.FACTS.not_find_mapsto_iff.
          intro. apply H0 in H2. apply MM.FACTS.not_find_mapsto_iff in H. auto. }
        { admit. }
      Qed.         

      Lemma multimap_join_star : forall 
        (impures0 impures1 : MM.mmap (exprs types)) B,
        (FM.fold
          (fun (k : nat) (ls : list (exprs types)) acc =>
            Star (starred (Func k) ls Emp) acc)
          (MM.mmap_join impures0 impures1) B)
        <===>
        (FM.fold
          (fun (k : nat) (ls : list (exprs types)) acc =>
            Star (starred (Func k) ls Emp) acc) impures0 
          (FM.fold
            (fun (k : nat) (ls : list (exprs types)) acc =>
              Star (starred (Func k) ls Emp) acc) impures1 B)).
      Proof.
        unfold MM.mmap_join.
        intro. apply NatMap.IntMapProperties.map_induction with (m := impures0).
        * intros.
          repeat rewrite NatMap.IntMapProperties.fold_Empty with (m := m); eauto with typeclass_instances.
          reflexivity.

        * intros.
          generalize (@NatMap.IntMapProperties.fold_Add (list (exprs types)) _ (@FM.Equal (list (exprs types)))).
          intro. 
          rewrite NatMap.IntMapProperties.fold_Equal; try solve [ clear; eauto with typeclass_instances ].
          4: eapply H2; eauto with typeclass_instances.
          clear H2. simpl in *.
          unfold exprs, MM.mmap_extend; simpl in *.
          match goal with
            | [ |- context [ FM.find ?x ?y ] ] => remember y
          end.
          case_eq (FM.find x t); intros.
          { subst.
            rewrite NatMap.IntMapProperties.fold_Equal; eauto with typeclass_instances.
            4: eapply MF.add_remove_Equal.
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
            rewrite starred_app. heq_canceler.
          
            generalize (@MM.mmap_join_remove_acc _ x m impures1 H0). unfold MM.mmap_join. intro.
            symmetry. rewrite NatMap.IntMapProperties.fold_Equal.
            5: eapply H3. clear H3.
            rewrite H. rewrite fold_starred with (b := FM.fold _ _ _). heq_canceler. eauto with typeclass_instances.
            
            solve [ clear; eauto with typeclass_instances hprop ].

            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
            apply FM.remove_1; auto.
            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
            apply FM.remove_1; auto.

            { 
              generalize MM.mmap_join_o. 
              unfold MM.mmap_join. intros. unfold MM.mmap_extend in H3. rewrite H3 in H2; auto. 
              apply MM.PROPS.F.not_find_in_iff in H0. unfold exprs in H0. rewrite H0 in H2.
              
              revert H2; clear; intros.
              unfold NatMap.IntMapProperties.Add; intros.
                repeat (rewrite NatMap.IntMapFacts.add_o || rewrite NatMap.IntMapFacts.remove_o).
                destruct (NatMap.Ordered_nat.eq_dec x y); subst; auto.
            }

            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
        }          
        { subst.
          rewrite NatMap.IntMapProperties.fold_add; eauto with typeclass_instances.
          rewrite H. symmetry. rewrite fold_starred. 
          rewrite NatMap.IntMapProperties.fold_Add; eauto with typeclass_instances.
          symmetry. rewrite fold_starred with (b := FM.fold _ _ _). heq_canceler.
          
          repeat (red; intros; subst). rewrite H3. heq_canceler.
          red; intros; heq_canceler.
          repeat (red; intros; subst). rewrite H3; heq_canceler.
          red; intros; heq_canceler.
          intro.
          apply NatMap.IntMapProperties.F.in_find_iff in H3. auto.
        }
        eauto with typeclass_instances.
        solve [ clear; eauto with typeclass_instances hprop ].
        solve [ clear; eauto with typeclass_instances hprop ].
        clear; repeat (red; intros; subst). unfold MM.mmap_extend. rewrite H.
          destruct (FM.find (elt:=list (exprs types)) y y1); try rewrite H; reflexivity.

        eapply MM.transpose_neqkey_mmap_extend.
      Qed.

      Lemma star_SHeap_denote : forall s1 s2,
        (Star (sheapD s1) (sheapD s2)) <===> (sheapD (star_SHeap s1 s2)).
      Proof.
        intros. symmetry. repeat rewrite sheapD_def.
        destruct s1; destruct s2; intros; simpl; unfold star_SHeap; simpl.
        match goal with
          | [ |- heq _ _ _ _ _ _ (Star (Star ?FL (Star ?PL ?OL)) (Star ?FR (Star ?PR ?OR))) ] =>
            transitivity (Star (Star FL FR) (Star (Star PL PR) (Star OL OR)))
        end.
        repeat rewrite starred_app.
        unfold impuresD.
        rewrite multimap_join_star; auto. heq_canceler.
        rewrite <- fold_starred. heq_canceler. 

        heq_canceler.
      Qed.


    End with_envs.

    Ltac heq_canceler :=
        repeat match goal with
                 | [ H : SE.heq _ _ _ _ _ _ _ |- _ ] => rewrite H
                 | [ |- context [ starred ?F ?L ?B ] ] =>
                   match B with
                     | SE.Emp => fail 1
                     | _ => rewrite (@starred_base _ _ _ _ F L B)
                   end
               end;
        SE_FACTS.heq_canceler.

    Hint Resolve transpose_neqkey_starred transpose_neqkey_Star : hprop.
    Hint Extern 1 (Morphisms.Proper _ _) =>
      (unfold Morphisms.Proper, Morphisms.respectful; intros; subst; 
        repeat match goal with
                 | [ H : heq _ _ _ _ _ _ _ |- _ ] => rewrite H
               end; reflexivity) : hprop.
    Hint Extern 1 (MM.PROPS.transpose_neqkey _ _) => 
      (clear; red; intros; subst; repeat rewrite MM.FACTS.add_o;
        repeat match goal with 
                 | [ |- context [ FM.E.eq_dec ?X ?Y ] ] => 
                   destruct (FM.E.eq_dec X Y)
                 | [ H : FM.E.eq ?X ?Y |- _ ] => rewrite H in *
               end; solve [ auto | exfalso; auto | heq_canceler ]) : hprop.

    Lemma heq_ex : forall U G cs t P Q,
      (forall v : tvarD types t, heq funcs preds U (existT (tvarD types) t v :: G) cs P Q) ->
      heq funcs preds U G cs (Exists t P) (Exists t Q).
    Proof.
      unfold heq; simpl; intros; apply ST.heq_ex; auto.
    Qed.
   
    Lemma heq_existsEach : forall cs X v Y (P Q : sexpr types pcType stateType),
      (forall Z, map (@projT1 _ _) Z = rev v -> heq funcs preds X (Z ++ Y) cs P Q) ->
      heq funcs preds X Y cs (existsEach v P) (existsEach v Q).
    Proof.
      induction v; simpl; intros.
        specialize (H nil); simpl in *; auto.

        apply heq_ex. intros. eapply IHv. intros.
        simpl. specialize (H (Z ++ @existT _ _ _ v0 :: nil)). rewrite map_app in *. 
        rewrite H0 in *. simpl in *.
        rewrite app_ass in *. simpl in *. auto.
    Qed.

    Lemma existsEach_app : forall X cs b a Y (P : sexpr _ _ _),
      heq funcs preds X Y cs (existsEach a (existsEach b P)) (existsEach (a ++ b) P).
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
      ST.heq cs (sexprD funcs preds EG (G'' ++ G) s) 
      (sexprD funcs preds EG (G'' ++ G' ++ G) (liftSExpr (length G'') (length G') s)).
    Proof.
      induction s; simpl; intros; 
        repeat match goal with
                 | [ |- _ ] => rewrite <- liftExpr_ext
                 | [ H : forall a, ST.heq _ _ _ |- _ ] => rewrite <- H
               end; try reflexivity.
      eapply ST.heq_ex. intros. specialize (IHs (existT (tvarD types) t v :: G'')).
      simpl in *. auto.
      destruct (nth_error preds f); try reflexivity.
      clear. destruct s; simpl; clear. generalize dependent SDomain0. induction l; simpl; try reflexivity.
      destruct SDomain0; try reflexivity.
      rewrite <- liftExpr_ext. destruct (exprD funcs EG (G'' ++ G) a t); try reflexivity.
      auto.
    Qed.

    Lemma star_pull_exists : forall EG cs a G s s2,
      heq funcs preds EG G cs (Star (Exists a s) s2) (Exists a (Star s (liftSExpr 0 1 s2))).
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
      heq funcs preds EG G cs (Star (existsEach v s) s2)
      (existsEach v (Star s (liftSExpr 0 (length v) s2))).
    Proof.
      induction v; simpl.
      intros; rewrite liftSExpr_0. reflexivity.

      intros.
      rewrite star_pull_exists. apply heq_ex. intros.
      rewrite IHv.
      
      rewrite liftSExpr_combine. reflexivity.
    Qed.

    Lemma starred_liftSExpr : forall F a b (ls : list (expr types)) base,
      (forall a0, liftSExpr a b (F a0) = F (liftExpr a b a0)) ->
      liftSExpr a b (starred F ls base) = starred F (map (liftExpr a b) ls) (liftSExpr a b base).
    Proof.
      induction ls; simpl; intros; try reflexivity.
      case_eq (starred F ls base); intros;
        rewrite <- IHls; repeat rewrite H0; simpl; repeat rewrite H; simpl; eauto.
    Qed.

    Lemma liftSExpr_existsEach : forall EG cs v0 s G n v,
      heq funcs preds EG G cs (liftSExpr n v (existsEach v0 s)) 
                  (existsEach v0 (liftSExpr (n + length v0) v s)).
    Proof.
      induction v0; simpl; intros.
        intros. rewrite Plus.plus_0_r. reflexivity.
      
        apply heq_ex; intros. rewrite IHv0. cutrewrite (S n + length v0 = n + S (length v0)); try reflexivity; omega.
    Qed.

    Lemma skipn_skipn : forall T a (ls : list T) b,
      skipn b (skipn a ls) = skipn (b + a) ls.
    Proof.
      clear; induction a; simpl; intros.
        rewrite Plus.plus_0_r. auto.
        rewrite Plus.plus_comm. simpl. destruct ls; auto. destruct b; auto.
        rewrite IHa. rewrite Plus.plus_comm. auto.
    Qed.

    Lemma heq_liftSExpr : forall cs EG G G' G'' P Q,
      heq funcs preds EG (G ++ G'') cs P Q ->
      heq funcs preds EG (G ++ G' ++ G'') cs (liftSExpr (length G) (length G') P) (liftSExpr (length G) (length G') Q).
    Proof.
      unfold heq; intros.
      repeat rewrite <- sexpr_lift_ext. auto.
    Qed.



    Lemma sheapD_sexprD_liftVars : forall EG cs s G G' G'',
      heq funcs preds EG (G ++ G' ++ G'') cs
        (liftSExpr (length G) (length G') (sheapD' s))
        (sheapD' (sheap_liftVars (length G) (length G') s)).
    Proof.
      destruct s; unfold sheap_liftVars, sheapD'; simpl; intros; repeat apply heq_star_frame; intros.

      clear. change Emp with (liftSExpr (length G) (length G') Emp) at 2. generalize (@Emp types pcType stateType).
        unfold MM.mmap_map. intros. rewrite MF.fold_map_fusion; eauto with typeclass_instances.

        Focus. 
        revert s.
        apply NatMap.IntMapProperties.map_induction with (m := impures0); intros.
        repeat (rewrite MM.PROPS.fold_Empty; eauto with typeclass_instances). reflexivity.

        symmetry. rewrite MM.PROPS.fold_Add. 6: eauto. 5: eauto. 2: eauto with typeclass_instances.
        rewrite starred_base. rewrite <- H. clear H.
        assert (forall base, heq funcs preds EG (G ++ G' ++ G'') cs 
          (starred (Func x) (map (map (liftExpr (length G) (length G'))) e) (liftSExpr (length G) (length G') base))
          (liftSExpr (length G) (length G') (starred (Func x) e base))).
        { clear.
          induction e; intros; try reflexivity. rewrite starred_def. simpl. rewrite <- starred_def.
            rewrite IHe. solve [ destruct (starred (Func x) e base); simpl; heq_canceler ]. 
        }
        rewrite H with (base := Emp).
        change (Star 
        (liftSExpr (length G) (length G')
           (FM.fold
              (fun (k : FM.key) => starred (Func k)) m s))
(liftSExpr (length G) (length G') (starred (Func x) e Emp)))
        with (liftSExpr (length G) (length G')
          (Star 
            (FM.fold
              (fun (k : FM.key) => starred (Func k)) m s)
(starred (Func x) e Emp))).

        eapply heq_liftSExpr.
                
        symmetry.
        rewrite MM.PROPS.fold_Add. 6: eauto. rewrite <- starred_base. reflexivity.
        eauto with typeclass_instances hprop.
        eauto with typeclass_instances hprop.
        clear; red; intros; subst; repeat rewrite MM.FACTS.add_o;
          repeat match goal with 
                   | [ |- context [ FM.E.eq_dec ?X ?Y ] ] => 
                     destruct (FM.E.eq_dec X Y)
                   | [ H : FM.E.eq ?X ?Y |- _ ] => rewrite H in *
                 end; auto.
        heq_canceler.
        eauto with typeclass_instances hprop.
        clear; do 4 (red; intros; subst); heq_canceler.

        clear; red; intros; subst; repeat rewrite MM.FACTS.add_o.
        heq_canceler.
        eapply transpose_neqkey_starred.
        
        Opaque starred.
        symmetry. rewrite starred_def. induction pures0; try reflexivity.
        simpl. rewrite IHpures0.
        match goal with
          | [ |- heq _ _ _ _ _ ?X _ ] =>
            change X with
              (liftSExpr (length G) (length G') (Star (Inj a) (starred (@Inj types pcType stateType) pures0 Emp)))
        end.
        apply heq_liftSExpr. symmetry. repeat rewrite starred_def. simpl. heq_canceler.

        symmetry. etransitivity. rewrite starred_def. reflexivity. induction other0; try reflexivity.
        simpl. rewrite IHother0.
        match goal with
          | [ |- heq _ _ _ _ _ ?X _ ] =>
            change X with
              (liftSExpr (length G) (length G') (Star (Const a) (starred (@Const types pcType stateType) other0 Emp)))
        end.
        apply heq_liftSExpr. symmetry. repeat rewrite starred_def. simpl. reflexivity.
    Qed.

    Lemma hash_denote' : forall EG cs (s : sexpr _ _ _) G, 
      heq funcs preds EG G cs s (existsEach (fst (hash s)) (sheapD' (snd (hash s)))).
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
        generalize star_SHeap_denote.
        symmetry. rewrite <- sheapD_sheapD'.
        rewrite <- star_SHeap_denote. simpl plus.
        cutrewrite (length v0 = length Z0).
        cutrewrite (length v = length Z).
        repeat rewrite sheapD_sheapD'.
        rewrite sheapD_sexprD_liftVars.
        rewrite sheapD_sexprD_liftVars with (G := nil). heq_canceler.
        rewrite <- rev_length; rewrite <- H; apply map_length.
        rewrite <- rev_length; rewrite <- H0; apply map_length.
    Qed.
    
    Theorem hash_denote : forall EG G cs (s : sexpr _ _ _), 
      heq funcs preds EG G cs s (existsEach (fst (hash s)) (sheapD (snd (hash s)))).
    Proof.
      intros. specialize (@hash_denote' EG cs s G). etransitivity.
      eassumption. apply heq_existsEach. intros. rewrite sheapD_sheapD'. reflexivity.
    Qed.

    (** replace "real" variables [a,b) and replace them with
     ** uvars [c,..]
     **)
    Definition sheapSubstU (a b c : nat) (s : SHeap) : SHeap :=
      {| impures := MM.mmap_map (map (exprSubstU a b c)) (impures s)
       ; pures := map (exprSubstU a b c) (pures s)
       ; other := other s
       |}.

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
