Require Import List.
Require Import Heaps SepTheoryX PropX.
Require Import PropXTac.
Require Import RelationClasses EqdepClass.
Require Import Expr ExprUnify.
Require Import DepList.
Require Import Setoid.

Set Implicit Arguments.

Require NatMap.

Module FM := NatMap.IntMap.

Section SepExprTypes.
  Variable types : list type.
  Variable rtype : Type.

  Record ssignature' := SSig {
    SDomain : list tvar ;
    SDenotation : functionTypeD (map (@tvarD types) SDomain) rtype
  }.

  Inductive sexpr' : Type :=
  | Emp : sexpr'
  | Inj : expr types -> sexpr'
  | Star : sexpr' -> sexpr' -> sexpr'
  | Exists : tvar -> sexpr' -> sexpr'
  | Func : func -> list (expr types) -> sexpr'
  | Const : rtype -> sexpr'
  .

  Record SHeap' : Type :=
  { impures : FM.t (list (list (expr types)))
  ; pures   : list (expr types)
  ; other   : list rtype
  }.
End SepExprTypes.

Implicit Arguments Emp [ types rtype ].
Implicit Arguments Star [ types rtype ].
Implicit Arguments Exists [ types rtype ].
Implicit Arguments Func [ types rtype ].
Implicit Arguments Const [ types rtype ].
Implicit Arguments Inj [ types rtype ].

Module SepExpr (B : Heap) (ST : SepTheoryX.SepTheoryXType B).

  Module SEP_FACTS := SepTheoryX_Rewrites B ST.
  Section env.
    Variable types : list type.
    Variable funcs : functions types.

    Variable pcType : tvar.
    Variable stateType : tvar.

    Definition ssignature := ssignature' types (ST.hprop (tvarD types pcType) (tvarD types stateType) nil).
    Definition sfunctions := list ssignature.

    Variable sfuncs : sfunctions.

    Definition sexpr := sexpr' types (ST.hprop (tvarD types pcType) (tvarD types stateType) nil).

    Fixpoint sexprD (uvs vs : list { t : tvar & tvarD types t }) (s : sexpr)
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


    (** TODO : Make these opaque (use the module trick) **)
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

      Global Add Parametric Morphism U' : (@Star _ _) with
        signature (himp U U' G cs ==> himp U U' G cs ==> himp U U' G cs)      
        as star_himp_mor.
        unfold himp; simpl; intros; eapply SEP_FACTS.star_himp_mor; eauto.
      Qed.

      Global Add Parametric Morphism U' : (@Star _ _) with
        signature (heq U U' G cs ==> heq U U' G cs ==> heq U U' G cs)      
        as star_heq_mor.
        unfold himp; simpl; intros; eapply SEP_FACTS.star_heq_mor; eauto.
      Qed.

(* TODO: this needs some pointwise-ness
    Global Add Parametric Morphism T : (@Exists _ _ T) with 
      signature (heq U U G cs ==> heq U U G cs)
    as ex_heq_mor.
      unfold heq; simpl; intros. eapply SEP_FACTS.ex_heq_mor; eauto. intro. 
    Qed.

    Global Add Parametric Morphism T : (@ex p s nil T) with 
      signature (pointwise_relation T (himp cs) ==> himp cs)
    as ex_himp_mor.
      intros. eapply himp_ex. auto.
    Qed.
*)

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

    Section exists_subst.
      Variable U1 : env types.
      
      Fixpoint exists_subst (U : list (tvar * option (expr types))) 
        : (env types -> Prop) -> Prop :=
        match U as U with
          | nil => fun cc => cc nil
          | (t,v) :: r => fun cc =>
            match v with
              | None => 
                exists v : tvarD types t, exists_subst r (fun z => cc (existT _ t v :: z))
              | Some v => 
                match exprD funcs nil U1 v t with
                  | None => False
                  | Some v =>
                    exists_subst r (fun z => cc (existT _ t v :: z))
                end
            end
        end.

    End exists_subst.

    Lemma exists_subst_exists : forall A
      (B : list (tvar * option (expr types))) P,
      exists_subst A B P ->
      exists C, P C.
    Proof.
      clear. induction B; simpl; intros.
      eauto.
      destruct a; simpl in *. destruct o.
      destruct (exprD funcs nil A e t); try tauto.
      eapply IHB in H; destruct H; eauto. 
      destruct H. eapply IHB in H. destruct H; eauto.
    Qed.

    Fixpoint forallEach (ls : variables) : (env types -> Prop) -> Prop :=
      match ls with
        | nil => fun cc => cc nil
        | a :: b => fun cc =>
          forall x : tvarD types a, forallEach b (fun r => cc (existT _ a x :: r))
      end.

    (** A more efficient representation for sexprs. **)
    Definition SHeap := 
      SHeap' types (ST.hprop (tvarD types pcType) (tvarD types stateType) nil).
  
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
      {| impures := FM.map (map (map (liftExpr a b))) (impures s)
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

    (** convert the sexpr into a SHeap **)
    Fixpoint hash (s : sexpr) : ( variables * SHeap ) :=
      match s with
        | Emp => (nil, SHeap_empty)
        | Inj p => (nil,
          {| impures := FM.empty
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
          (t :: v, b)
        | Func f a =>
          (nil,
           {| impures := FM.add f (a :: nil) FM.empty
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

      rewrite IHi2. rewrite <- starred_base. rewrite IHi1.
      symmetry. 
      rewrite fold_starred. repeat rewrite heq_star_assoc.
      apply heq_star_frame. reflexivity.
      apply heq_star_frame; try reflexivity.
      rewrite starred_starred'; try reflexivity. 
    Qed.

    Theorem sheapD_sheapD' : forall a c cs h, 
      heq a a c cs (sheapD h) (sheapD' h).
    Proof.
      destruct h; unfold sheapD, sheapD'; simpl.
      rewrite impures'. rewrite <- starred_base. 
      rewrite <- starred_base with (ls := other0).
      eapply heq_star_frame. reflexivity.
      eapply heq_star_frame. eapply starred_starred'; reflexivity.
      autorewrite with hprop.
      eapply starred_starred'; reflexivity.
    Qed.

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
      Focus 2. instantiate (1 := (sexprD uvars vars (sheapD' h))). 
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
                 (acc : sexpr' types
                          (ST.hprop (tvarD types pcType)
                             (tvarD types stateType) nil)) =>
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
          (acc : sexpr' types
            (ST.hprop (tvarD types pcType) 
              (tvarD types stateType) nil)) =>
          Star (starred' (Func k) ls Emp) acc)
        (FM.insert_at_right i1 i2) b)
      (Star (FM.fold
        (fun (k : nat) (ls : list (list (expr types)))
          (acc : sexpr' types
            (ST.hprop (tvarD types pcType) 
              (tvarD types stateType) nil)) =>
          Star (starred' (Func k) ls Emp) acc)
        i1 Emp)
      (FM.fold
        (fun (k : nat) (ls : list (list (expr types)))
          (acc : sexpr' types
            (ST.hprop (tvarD types pcType) 
              (tvarD types stateType) nil)) =>
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
               (acc : sexpr' types
                        (ST.hprop (tvarD types pcType)
                           (tvarD types stateType) nil)) =>
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
      symmetry. rewrite heq_star_comm. rewrite <- heq_star_assoc.
      rewrite heq_star_comm. reflexivity.

      intros.
      rewrite fold_starred. rewrite IHimpures0_2 by assumption.
      symmetry. rewrite fold_starred. 
      rewrite starred_starred'; [ | reflexivity | reflexivity ].
      repeat rewrite heq_star_assoc. apply heq_star_frame; try reflexivity.
      symmetry. rewrite heq_star_comm. rewrite heq_star_assoc.
      reflexivity.
    Qed.

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
    Proof.
      induction s; simpl; try (unfold sheapD; reflexivity).
        intros.
        rewrite IHs1 at 1. rewrite IHs2 at 1. clear IHs1 IHs2.
        destruct (hash s1); destruct (hash s2); simpl. clear. admit.
        
        destruct (hash s); simpl in *. intros. apply heq_ex. intros. eauto.
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
    Record SepResult (gl gr : sexpr) : Type := Prove
      { vars   : variables
      ; lhs_ex : variables
      ; lhs    : sexpr
      ; rhs_ex : variables
      ; rhs    : sexpr
      ; SUBST  : Subst types
      }.

    Definition SProverT : Type := forall
      (hyps : list (expr types)) (** Pure Premises **)
      (gl gr : sexpr),
      SepResult gl gr.

    Fixpoint unify_remove (l : list (expr types)) (r : list (list (expr types)))
      (ls rs : ExprUnify.Subst types)
      : option (list (list (expr types)) * ExprUnify.Subst types * ExprUnify.Subst types) :=
        match r with 
          | nil => None
          | a :: b => 
            match exprUnifyArgs l a ls rs with
              | None => 
                match unify_remove l b ls rs with
                  | None => None
                  | Some (x,y,z) => Some (a :: x, y, z)
                end
              | Some (ls,rs) => Some (b, ls, rs)
            end
        end.

    Fixpoint unify_remove_all (l r : list (list (expr types)))
      (ls rs : ExprUnify.Subst types)
      : list (list (expr types)) * list (list (expr types)) * 
        ExprUnify.Subst types * ExprUnify.Subst types :=
        match l with
          | nil => (l, r, ls, rs)
          | a :: b => 
            match unify_remove a r ls rs with
              | None => 
                let '(l,r,ls,rs) := unify_remove_all b r ls rs in
                (a :: l, r, ls, rs)
              | Some (r, ls, rs) =>
                unify_remove_all b r ls rs
            end
        end.

    Definition sepCancel (l r : SHeap) :
      SHeap * SHeap * ExprUnify.Subst types * ExprUnify.Subst types :=
     let '(lf, rf, ls, rs) := 
        FM.fold (fun k v a => 
          let '(lf, rf, ls, rs) := a in
          match FM.find k rf with
            | None => (FM.add k v lf, rf, ls, rs)
            | Some xs =>
              let '(l,r,ls,rs) := unify_remove_all v xs ls rs in
              (FM.add k l lf, FM.add k r rf, ls, rs)
          end)
        (impures l)
        (FM.empty , impures r , empty_Subst _ , empty_Subst _)
      in
      ({| impures := lf ; pures := pures l ; other := other l |},
       {| impures := rf ; pures := pures r ; other := other r |},
       ls, rs).

    (** TODO: I should reconsider this... **)
    Definition CancelSep : SProverT :=
      fun _ gl gr =>
        let (ql, lhs) := hash gl in
        let (qr, rhs) := hash gr in
        let rhs' := liftSHeap 0 (length ql) (sheapSubstU 0 (length qr) 0 rhs) in
        let '(lhs',rhs',lhs_subst,rhs_subst) := sepCancel lhs rhs' in
        {| vars := ql ; 
           lhs := sheapD lhs' ; lhs_ex := nil ; 
           rhs := sheapD rhs' ; rhs_ex := qr ; SUBST := rhs_subst
         |}.

    Theorem ApplyCancelSep : forall cs hyps l r,
      AllProvable funcs nil nil hyps ->
      match CancelSep hyps l r with
        | Prove vars lhs_ex lhs rhs_ex rhs SUBST =>
          forallEach vars (fun VS : env types =>
            exists_subst VS (env_of_Subst SUBST rhs_ex 0)
            (fun rhs_ex : env types => 
              himp nil rhs_ex VS cs lhs rhs))
      end ->
      himp nil nil nil cs l r.
    Proof.
      clear. intros. case_eq (CancelSep hyps l r); intros.
      rewrite H1 in H0.
    Admitted.

  End env.

  (** Reflection **)
  Require Import Reflect.

(*
  Definition defaultType (T : Type) : type :=
    {| Impl := T; Expr.Eq := fun _ _ => None |}.
*)

  Ltac build_default_type T := 
    match goal with
      | [ |- _ ] =>
        let D := constr:(@Typ T (@seq_dec T _)) in
        D
      | [ |- _ ] =>
        constr:({| Impl := T ; Expr.Eq := fun _ _ : T => None |})
    end.

  Ltac extend_type T types :=
    match T with
      | Prop => types
      | _ => 
        let rec find types :=
        match types with
          | nil => constr:(false)
          | ?a :: ?b =>
            match unifies (Impl a) T with
              | true => constr:(true)
              | false => find b
            end
        end
        in
        match find types with
          | true => types
          | _ =>
            let D := build_default_type T in
            eval simpl app in (types ++ (D :: @nil type))
        end
    end.

  (* extend a reflected type list with new raw types
   * - Ts is a list of raw types
   * - types is a list of reflected types
   *)
  Ltac extend_all_types Ts types :=
    match Ts with
      | nil => types
      | ?a :: ?b =>
        let types := extend_type a types in
        extend_all_types b types
    end.

  Record VarType (t : Type) : Type :=
    { open : t }.
  Definition openUp T U (f : T -> U) (vt : VarType T) : U :=
    f (open vt).

  Ltac lift_ssignature s nt rtype :=
    let d := eval simpl SDomain in (SDomain s) in
    let f := eval simpl SDenotation in (SDenotation s) in
    let res := constr:(@SSig nt rtype d f) in 
    eval simpl in res.

  Ltac lift_ssignatures fs nt :=
    match type of fs with
      | list (ssignature' _ (ST.hprop (tvarD _ ?pc) (tvarD _ ?st) ?ls)) =>
        let rtype := constr:(ST.hprop (tvarD nt pc) (tvarD nt st) nil) in
        let f sig := 
          lift_ssignature sig nt rtype
        in
        map_tac (ssignature nt pc st) f fs
      | list (ssignature' _ ?rtype) =>
        let f sig := 
          lift_ssignature sig nt rtype
        in
        map_tac (ssignature nt rtype) f fs
      | list (ssignature _ ?pc ?st) =>
        let rtype := constr:(ST.hprop (tvarD nt pc) (tvarD nt st) nil) in
        let f sig := 
          lift_ssignature sig nt rtype
        in
        map_tac (ssignature nt pc st) f fs
    end.

  (** collect the raw types from the given expression.
   ** - e is the expression to collect types from
   ** - types is a value of type [list Type]
   **   (make sure it is NOT [list Set])
   **)
  Ltac collectTypes_expr isConst e Ts :=
    match e with
      | fun x => (@openUp _ ?T _ _) =>
        let v := constr:(T:Type) in
        cons_uniq v Ts
      | fun x => ?e =>
        collectTypes_expr isConst e Ts
      | _ =>
        let rec bt_args args Ts :=
          match args with
            | tt => Ts
            | (?a, ?b) =>
              let Ts := collectTypes_expr isConst a Ts in
              bt_args b Ts
          end
        in
        let cc _ Ts' args := 
          let T := 
            match e with 
              | fun x : VarType _ => _ => 
                match type of e with
                  | _ -> ?T => T
                end
              | _ => type of e
            end
          in
          let Ts' :=
            let v := constr:(T : Type) in
            cons_uniq v Ts'
          in
          let Ts := append_uniq Ts' Ts in
          bt_args args Ts
        in
        refl_app cc e
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

  (** find x inside (map proj xs) and return its position as a natural number.
   ** This tactic fails if x does not occur in the list
   ** - proj is a gallina function.
   **)
  Ltac indexOf_nat proj x xs :=
    let rec search xs :=
      match xs with
        | ?X :: ?XS =>
          match unifies (proj X) x with
            | true => constr:(0)
            | false => 
              let r := search XS in
              constr:(S r)
          end
      end
    in search xs.

  (** specialization of indexOf_nat to project from type **)
  Ltac typesIndex x types :=
    indexOf_nat Impl x types.

  (** given the list of types (of type [list type]) and a raw type
   ** (of type [Type]), return the [tvar] that corresponds to the
   ** given raw type.
   **)
  Ltac reflectType types t :=
    match t with
      | Prop => constr:(tvProp)
      | _ =>
        let i := typesIndex t types in
        let r := constr:(tvType i) in
        r
    end.  
      
  (** essentially this is [map (reflectType types) ts] **)
  Ltac reflectTypes_toList types ts :=
    match ts with 
      | nil => constr:(@nil tvar)
      | ?T :: ?TS =>
        let i := typesIndex T types in
        let rest := reflectTypes_toList types TS in
        constr:(@cons tvar (tvType i) rest)
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

  Ltac collectAllTypes_expr isConst Ts goals :=
    match goals with
      | tt => Ts
      | (?a, ?b) =>
        let ts := collectTypes_expr isConst a Ts in
        collectAllTypes_expr isConst ts b
    end.

  Ltac collectAllTypes_func Ts T :=
    match T with
      | ?t -> ?T =>
        let t := constr:(t : Type) in
        let Ts := cons_uniq t Ts in
        collectAllTypes_func Ts T
      | forall x , _ => 
        (** Can't reflect types for dependent function **)
        fail 100 "can't reflect types for dependent function!"
      | ?t =>
        let t := constr:(t : Type) in
        cons_uniq t Ts
    end.

  Ltac collectAllTypes_funcs Ts Fs :=
    match Fs with
      | tt => Ts
      | (?Fl, ?Fr) =>
        let Ts := collectAllTypes_funcs Ts Fl in
        collectAllTypes_funcs Ts Fr
      | ?F =>
        collectAllTypes_func Ts F
    end.

  Ltac collectAllTypes_sfunc Ts T :=
    match T with
      | ?t -> ?T =>
        let t := constr:(t : Type) in
        let Ts := cons_uniq t Ts in
        collectAllTypes_func Ts T
      | forall x , _ => 
        (** Can't reflect types for dependent function **)
        fail 100 "can't reflect types for dependent function!"
      | ST.hprop _ _ => Ts
    end.

  Ltac collectAllTypes_sfuncs Ts Fs :=
    match Fs with
      | tt => Ts
      | (?Fl, ?Fr) =>
        let Ts := collectAllTypes_sfuncs Ts Fl in
        collectAllTypes_sfuncs Ts Fr
      | ?F =>
        collectAllTypes_sfunc Ts F
    end.

  Ltac getVar' idx :=
    match idx with
      | fun x => x =>
        constr:(0)
      | fun x => @openUp _ _ (@snd _ _) (@?X x) =>
        let r := getVar' X in
          constr:(S r)
      | _ => idtac "couldn't find variable! [1]" idx
    end.

  Ltac getVar idx :=
    match idx with
      | fun x => @openUp _ _ (@fst _ _) (@?X x) =>
        getVar' X
      | fun x => @openUp _ _ (@snd _ _) (@?X x) =>
        let r := getVar X in
          constr:(S r)
      | _ => idtac "couldn't find variable! [2]" idx
    end.

  (** Build a signature for the given function 
   ** - types is a list of reflected types, i.e. type [list type]
   ** the type of f can NOT be dependent, i.e. it must be of the
   ** form, 
   **   _ -> ... -> _
   **)
  Ltac reflect_function types f :=
    let T := type of f in
    let rec refl dom T :=
      match T with
        (* no dependent types *)
        | ?A -> ?B =>
          let A := reflectType types A in
          let dom := constr:(A :: dom) in
          refl dom B 
        | ?R =>
          let R := reflectType types R in
          let dom := eval simpl rev in (rev dom) in
          constr:(@Expr.Sig types dom R f)
      end
   in refl (@nil tvar) T.

  (** lookup a function in a list of reflected functions.
   ** if the function does not exist in the list, the list is extended.
   ** - k is the continutation and is passed the resulting list of functions
   **   and the index of f in the list.
   **   (all elements passed into funcs' are preserved in order)
   **)
  Ltac getFunction types f funcs' k :=
    let rec lookup funcs acc :=
      match funcs with
        | nil =>
          let F := reflect_function types f in
          let funcs := eval simpl app in (funcs' ++ (F :: nil)) in
          k funcs acc
        | ?F :: ?FS =>
          match unifies (Denotation F) f with
            | true => k funcs' acc
            | false =>
              let acc := constr:(S acc) in
              lookup FS acc
          end
      end
    in lookup funcs' 0.

  Ltac getAllFunctions types funcs' fs :=
    match fs with
      | tt => funcs'
      | ?F =>
        getFunction types F funcs' ltac:(fun funcs _ => funcs)
      | ( ?fl , ?fr ) =>
        getAllFunctions types funcs' fl ltac:(fun funcs _ => 
          getAllFunctions types funcs fr ltac:(fun funcs _ => funcs))
    end.

  (** reflect an expression gathering the functions at the same time.
   ** - k is the continuation and is passed the list of reflected
   **   functions and the reflected expression.
   **)
  Ltac reflect_expr isConst e types funcs uvars vars k :=
    let rec reflect funcs e k :=
      match e with
        | fun _ => ?X =>
          is_evar X ; idtac "got EVAR, this case is not implemented" ;
          (** this is a unification variable **)
          let r := constr:(@Expr.UVar) in (** TODO **)
          k funcs r 
        | fun x => (@openUp _ _ _ _) =>
          (** this is a variable **)
          let v := getVar e in
          let r := constr:(@Expr.Var types v) in
          k funcs r
        | fun x => ?e =>
          reflect funcs e k
        | _ =>
          let rec bt_args funcs args k :=
            match args with
              | tt => 
                let v := constr:(@nil (@expr types)) in
                k funcs v
              | (?a, ?b) =>
                reflect funcs a ltac:(fun funcs a =>
                  bt_args funcs b ltac:(fun funcs b =>
                    let r := constr:(@cons (@expr types) a b) in
                    k funcs r))
            end
          in
          let cc f Ts args :=
            getFunction types f funcs ltac:(fun funcs F =>
              bt_args funcs args ltac:(fun funcs args =>
                let r := constr:(@Expr.Func types F args) in 
                k funcs r))
          in
          match e with
            | _ => 
              match isConst e with
                | true => 
                  let ty := type of e in
                  let ty := reflectType types ty in
                  let r := eval simpl in (@Expr.Const types ty e) in
                  k funcs r
                | false => 
                  refl_app cc e
              end
            | _ => refl_app cc e
          end
      end
    in reflect funcs e k.

  (** reflect a separation logic predicate. this is analagous 
   ** to reflect_function except that it works on separation logic functions.
   **)
  Ltac reflect_sfunction pcT stT types f :=
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
          constr:(@SSig types (ST.hprop (@tvarD types pcT) (@tvarD types stT) nil) dom f)
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
          let F := reflect_sfunction pcT stT types f in
          let sfuncs := eval simpl app in (sfuncs ++ (F :: nil)) in
          k sfuncs acc
        | ?F :: ?FS =>
          match unifies (SDenotation F) f with
            | true => k sfuncs acc 
            | false => 
              let acc := constr:(S acc) in
              lookup FS acc
          end
      end
    in lookup sfuncs 0.

  Ltac getAllSFunctions pcT stT types sfuncs' fs :=
    match fs with
      | tt => sfuncs'
      | ?F =>
        getSFunction types F sfuncs' ltac:(fun sfuncs _ => sfuncs)
      | ( ?fl , ?fr ) =>
        getAllSFunctions pcT stT types sfuncs' fl ltac:(fun sfuncs _ => 
          getAllSFunctions pcT stT types sfuncs fr ltac:(fun sfuncs _ => sfuncs))
    end.

  (** reflect sexprs. simultaneously gather the funcs and sfuncs
   ** k is called with the functions, separation logic predicats and the reflected
   ** sexpr.
   **)
  Ltac reflect_sexpr isConst s types funcs pcType stateType sfuncs uvars vars k :=
    let implicits ctor :=
      constr:(ctor types (ST.hprop (@tvarD types pcType) (@tvarD types stateType) nil))
    in
    let rec reflect s funcs sfuncs uvars vars k :=
      match s with
        | fun _ => ?s =>
          reflect s funcs sfuncs uvars vars k
        | fun x : VarType ?T => @ST.star _ _ _ (@?L x) (@?R x) =>
          reflect L funcs sfuncs uvars vars ltac:(fun funcs sfuncs L =>
            reflect R funcs sfuncs uvars vars ltac:(fun funcs sfuncs R => 
              let r := constr:(@Star) in
              let r := implicits r in
              let r := constr:(r L R) in
              k funcs sfuncs r))
        | fun x : ?T => @ST.ex _ _ _ ?T' (fun y : ?T' => @?B y x) =>
          let v := constr:(fun x : VarType (T' * T) => 
            B (@openUp _ T (@fst _ _) x) (@openUp _ T' (@snd _ _) x)) in
          let v := eval simpl in v in
          let nv := reflectType types T' in
          let vars' := constr:(nv :: vars) in
          reflect v funcs sfuncs uvars vars' ltac:(fun funcs sfuncs B =>
            let r := constr:(@Exists) in
            let r := implicits r in
            let r := constr:(@r nv B) in
            k funcs sfuncs r)
        | @ST.emp _ _ _ => 
          let r := constr:(@Emp) in
          let r := implicits r in
          k funcs sfuncs r

        | @ST.inj _ _ _ (PropX.Inj ?P) =>
          reflect_expr isConst P types funcs uvars vars ltac:(fun funcs P =>
            let r := constr:(@Inj) in
            let r := implicits r in
            let r := constr:(r P) in
            k funcs sfuncs r)
        | @ST.inj _ _ _ ?PX =>
          let r := constr:(@Const) in
          let r := implicits r in
          let r := constr:(r PX) in
          k funcs sfuncs r
        | @ST.star _ _ _ ?L ?R =>
          reflect L funcs sfuncs uvars vars ltac:(fun funcs sfuncs L => 
            reflect R funcs sfuncs uvars vars ltac:(fun funcs sfuncs R => 
              let r := constr:(@Star) in
              let r := implicits r in
              let r := constr:(r L R) in
              k funcs sfuncs r))
        | @ST.ex _ _ _ ?T (fun x : ?T => @?B x) =>
          let v := constr:(fun x : VarType (T * unit) => B (@openUp _ T (@fst _ _) x)) in
          let v := eval simpl in v in
          let nv := reflectType types T in
          let vars' := constr:(nv :: vars) in
          reflect v funcs sfuncs uvars vars' ltac:(fun funcs sfuncs B =>
            let r := constr:(@Exists) in
            let r := implicits r in
            let r := constr:(@r nv B) in
            k funcs sfuncs r)
        | ?X =>
          let rec bt_args args funcs k :=
            match args with
              | tt => 
                let v := constr:(@nil (@expr types)) in
                k funcs v
              | (?a,?b) =>
                reflect_expr isConst a types funcs uvars vars ltac:(fun funcs a =>
                  bt_args b funcs ltac:(fun funcs b => 
                  let v := constr:(@cons (@expr types) a b) in
                  k funcs v))
            end
          in
          let cc f Ts As :=
            getSFunction pcType stateType types f sfuncs ltac:(fun sfuncs F =>
            bt_args As funcs ltac:(fun funcs args =>
            let r := constr:(@Func) in
            let r := implicits r in
            let r := constr:(@r F args) in
            k funcs sfuncs r))
          in
          refl_app cc X
      end
    in
    reflect s funcs sfuncs uvars vars k.

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
   ** - the list of reflected functions
   ** - the list of reflected separation logic predicates
   ** - the list of reflected sexpr.
   **)
  Ltac reflect_sexprs pcT stT isConst types' funcs sfuncs goals :=
    let rt := 
      collectAllTypes_sexpr isConst ((pcT : Type) :: (stT : Type) :: @nil Type) goals
    in
    let types := extend_all_types rt types' in
    let types := eval simpl in types in
    let pcTyp := typesIndex pcT types in
    let stTyp := typesIndex stT types in
    let pcTyp := constr:(tvType pcTyp) in
    let stTyp := constr:(tvType stTyp) in
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
    let rec reflect_all ls funcs sfuncs k :=
      match ls with
        | nil => 
          let r := constr:(@nil (@sexpr types pcTyp stTyp)) in
          k funcs sfuncs r
        | ?e :: ?es =>
          let vs := constr:(@nil tvar) in
          let us := constr:(@nil tvar) in
          reflect_sexpr isConst e types funcs pcTyp stTyp sfuncs us vs ltac:(fun funcs sfuncs e =>
            reflect_all es funcs sfuncs ltac:(fun funcs sfuncs es =>
              let es := constr:(e :: es) in
              k funcs sfuncs es)) 
      end
    in
    match type of funcs with
      | list (signature types) =>
        reflect_all goals funcs sfuncs ltac:(fun funcs sfuncs es =>
          constr:((types, pcTyp, stTyp, funcs, sfuncs, es)))
      | ?X =>
        let funcs := lift_signatures funcs types in
        let sfuncs := lift_ssignatures sfuncs types in
        reflect_all goals funcs sfuncs ltac:(fun funcs sfuncs es =>
          constr:((types, pcTyp, stTyp, funcs, sfuncs, es)))
    end.

  (** NOTE: if types is extended at all then funcs needs to be lifted **)
  Ltac reflect_exprs isConst types funcs exprs :=
    let rt := 
      collectAllTypes_expr isConst (@nil Type) exprs
    in
    let types := extend_all_types rt types in
    let types := eval simpl in types in
    let funcs := 
      match funcs with
        | tt => constr:(@nil (@signature types))
        | _ => funcs 
      end
    in
    let rec reflect_all ls funcs k :=
      match ls with
        | tt => 
          let r := constr:(@nil (@expr types)) in
          k funcs r
        | (?e, ?es) =>
          let vs := constr:(@nil tvar) in
          let us := constr:(@nil tvar) in
          reflect_expr isConst e types funcs us vs ltac:(fun funcs e =>
            reflect_all es funcs ltac:(fun funcs es =>
              let es := constr:(e :: es) in
              k funcs es))
      end
    in
    match type of funcs with
      | list (signature types) =>
        reflect_all exprs funcs ltac:(fun funcs es =>
          constr:((types, funcs, es)))
      | list (signature ?X) =>
        let funcs := lift_signatures funcs types in
        reflect_all exprs funcs ltac:(fun funcs es =>
          constr:((types, funcs, es)))
    end.

  Lemma change_ST_himp_himp : forall (types : list type)
    (funcs : functions types) (pc st : tvar)
    (sfuncs : list (ssignature types pc st))
    
    (cs : codeSpec (tvarD types pc) (tvarD types st))
    (L R : sexpr types pc st),
    himp funcs sfuncs nil nil nil cs L R ->
    ST.himp cs
      (@sexprD types funcs pc st sfuncs nil nil L)
      (@sexprD types funcs pc st sfuncs nil nil R).
  Proof.
    unfold himp. intros. auto.
  Qed.

  Ltac reflect_goal isConst types :=
    let types :=
      match types with
        | tt => constr:(@nil type)
        | _ => types
      end
    in
    match goal with
      | [ |- @ST.himp ?pcT ?stT ?cs ?L ?R ] =>
        let v := reflect_sexprs pcT stT isConst types tt tt (L :: R :: nil) in
        match v with
          | (?types, ?pcTyp, ?stTyp, ?funcs, ?sfuncs, ?L :: ?R :: nil) =>
            apply (@change_ST_himp_himp types funcs pcTyp stTyp sfuncs cs L R)
        end
    end.

  (** This should perform all the reductions necessary to remove all of reflection calls.
   **)
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
    ].

  Ltac canceler hyps' :=
    match hyps' with
      | tt => 
        apply ApplyCancelSep with (hyps := nil)
      | _ =>
        apply ApplyCancelSep with (hyps := hyps')
    end; [ simpl AllProvable; tauto | simplifier ].

  Ltac sep isConst types hyps := 
    reflect_goal isConst types;
    let rec unfold_all ls :=
      match ls with
        | ?a :: ?b => unfold a ; unfold_all b
        | _ => canceler hyps; intros; hnf; simpl in *
      end
    in unfold_all types.

End SepExpr.
