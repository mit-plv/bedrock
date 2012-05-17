Require Import Expr.
Require Import NatMap.
Require Import EquivDec.
Require Import List Bool.
Require Import GenRec.

Set Implicit Arguments.
Set Strict Implicit.

Module Type SynUnifier.
  (** An environment that maintains a mapping from variables to their meaning **)
  Parameter Subst : list type -> Type.

  Section typed.
    Variable types : list type.
    
    Parameter Subst_empty : Subst types.

    (** Relations **)
    Parameter Subst_Equal : Subst types -> Subst types -> Prop.
    Parameter Equiv_Subst_Equal : RelationClasses.Equivalence Subst_Equal.

    Parameter Subst_Le : Subst types -> Subst types -> Prop.

    Parameter Refl_Subst_Le : RelationClasses.Reflexive Subst_Le.
    Parameter Antisym_Subst_Le : @RelationClasses.Antisymmetric _ _ Equiv_Subst_Equal Subst_Le.
    Parameter Trans_Subst_Le : RelationClasses.Transitive Subst_Le.

    (** The actual unification algorithm **)
    Parameter exprUnify : nat -> expr types -> expr types -> Subst types -> option (Subst types).
    
    (** Substitute meta variables **)
    Parameter exprInstantiate : Subst types -> expr types -> expr types.

    (** This is the soundness statement.
     **)
    Axiom exprUnify_sound : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      exprInstantiate sub' l = exprInstantiate sub' r.

    Axiom exprUnify_extends : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      Subst_Le sub' sub.

  End typed.
End SynUnifier.

Inductive R_expr (ts : list type) : expr ts -> expr ts -> Prop :=
| R_EqualL : forall t l r, R_expr l (Equal t l r)
| R_EqualR : forall t l r, R_expr r (Equal t l r)
| R_Not    : forall e, R_expr e (Not e)
| R_Func   : forall f args arg,
  In arg args -> R_expr arg (Func f args).
  
Lemma wf_R_expr' ts : well_founded (@R_expr ts).
Proof.  
  red; induction a; constructor; inversion 1; try assumption.

  subst. clear H0. generalize dependent y. generalize dependent l. clear.
  induction l; intros; simpl. inversion H3.
  inversion H3. inversion H. rewrite H0 in H4; assumption.
  inversion H; apply IHl; auto.
Defined.

Lemma wf_R_expr ts : well_founded (@R_expr ts).
Proof.
  let v := eval cbv beta iota zeta delta [ wf_R_expr' list_ind list_rec list_rect eq_ind eq_ind_r eq_rect eq_sym expr_ind ] in (@wf_R_expr' ts) in
  exact  v.
Defined.

Module Unifier (E : OrderedType.OrderedType with Definition t := nat) : SynUnifier.
  Module FM := HintlessFMapAVL.Make E.
  Module FACTS := HintlessFMapFacts.Facts FM.
  Module MFACTS := NatMap.MoreFMapFacts FM.
  Module PROPS := HintlessFMapFacts.Properties FM.

  Section typed.
    Variable types : list type.

    Section Mentions.
      Variable uv : nat.

      Fixpoint mentionsU (e : expr types) : bool :=
        match e with
          | Const _ _ 
          | Var _ => false
          | UVar n => if equiv_dec uv n then true else false
          | Func _ args =>
            (fix anyb ls : bool := 
              match ls with
                | nil => false
                | l :: ls => mentionsU l || anyb ls
              end) args
          | Equal _ l r => mentionsU l || mentionsU r
          | Not e => mentionsU e
        end.
    End Mentions.

    Section Normalization.
      Variable ctx : FM.t (expr types).
            
      Fixpoint normalized (e : expr types) : bool :=
        match e with
          | Var _ 
          | Const _ _ => true
          | UVar x => match FM.find x ctx with
                        | None => true
                        | Some _ => false
                      end
          | Not e => normalized e
          | Equal _ e1 e2 => (normalized e1) && (normalized e2)
          | Func _ l =>
            fold_right (fun x acc => acc && (normalized x)) true l
        end.
    End Normalization.

    Definition WellFormed (this : FM.t (expr types)) : Prop :=
      forall k v,
        FM.MapsTo k v this -> normalized this v = true.

    Definition Subst : Type :=
      { this : FM.t (expr types) & WellFormed this }.

    Definition subst_empty : FM.t (expr types) := FM.empty _. 

    Theorem WF_subst_empty : WellFormed subst_empty.
      red; unfold subst_empty; intros. apply FACTS.empty_mapsto_iff in H. exfalso; auto.
    Defined.

    Definition Subst_empty : Subst :=
      @existT _ _ subst_empty WF_subst_empty.

    Definition subst_lookup (k : nat) (s : FM.t (expr types)) : option (expr types) :=
      FM.find k s.
    
    Definition Subst_lookup k (s : Subst) : option (expr types) :=
      subst_lookup k (projT1 s).

    Section Instantiate.
      Variable sub : FM.t (expr types).

      Fixpoint subst_exprInstantiate (e : expr types) : expr types :=
        match e with 
          | Const _ _ 
          | Var _ => e
          | UVar n => match subst_lookup n sub with
                        | None => e 
                        | Some v => v
                      end
          | Func f args => Func f (map subst_exprInstantiate args)
          | Equal t l r => Equal t (subst_exprInstantiate l) (subst_exprInstantiate r)
          | Not e => Not (subst_exprInstantiate e)
        end.
    End Instantiate.
    
    Definition exprInstantiate (sub : Subst) := subst_exprInstantiate (projT1 sub).

    Definition Subst_Equal (l r : Subst) : Prop := 
      forall e, exprInstantiate l e = exprInstantiate r e.

    Definition Subst_Le (l r : Subst) : Prop :=
      forall k v, FM.MapsTo k v (projT1 r) -> 
        FM.MapsTo k (exprInstantiate l v) (projT1 l).

    Theorem Equiv_Subst_Equal : RelationClasses.Equivalence Subst_Equal.
    Proof.
      constructor; unfold Subst_Equal, FM.Equiv; red; intros; subst; eauto.
      rewrite H; eauto.
    Qed.    

    Lemma WellFormed_Canonical : forall s v,
      normalized s v = true ->
        subst_exprInstantiate s v = v.
    Proof.
      induction v; simpl; auto.
        { unfold subst_lookup. destruct (FM.find x s); auto; congruence. }          
        { generalize true at 1. intros. f_equal. generalize dependent l.
          induction 1; simpl; intros; auto.
          apply andb_true_iff in H1. intuition. f_equal; eauto. }            
        { intros. apply andb_true_iff in H; f_equal; firstorder. }
        { intros; f_equal; auto. }
    Qed.

    Lemma normalized_Lt' : forall s s' v,
      normalized (projT1 s) v = true -> 
      Subst_Le s s' ->
      normalized (projT1 s') v = true.
    Proof.
      induction v; simpl; intros; auto.
      { revert H. case_eq (FM.find x (projT1 s)); intros; try congruence.
        apply FACTS.not_find_in_iff in H.
        cutrewrite (FM.find x (projT1 s') = None); auto.
        apply FACTS.not_find_in_iff. intro. apply H.
        destruct H2. eapply H0 in H2. eexists; eauto. }
      { revert H0; revert H1; generalize true at 1 3; induction H; auto; simpl; intros.
        apply andb_true_iff in H2. apply andb_true_iff. intuition. }
      { apply andb_true_iff. apply andb_true_iff in H. intuition. }
    Qed.
    
    Lemma WellFormed_subst : forall x y,
      Subst_Le x y ->
      forall t, exprInstantiate x (exprInstantiate y t) = exprInstantiate x t.
    Proof.
      induction t; simpl; intros; try solve [ auto | f_equal; intuition ].
      { unfold subst_lookup.
        case_eq (FM.find x0 (projT1 y)); intros.
          cutrewrite (FM.find x0 (projT1 x) = Some (exprInstantiate x e)); auto.
          eapply FACTS.find_mapsto_iff. unfold Subst_Le in *. eapply H.
          eapply FACTS.find_mapsto_iff. auto.

          case_eq (FM.find x0 (projT1 x)); intros; simpl; unfold subst_lookup; rewrite H1; auto. }
      { f_equal. induction H0; simpl; auto.
        f_equal; auto. }
    Qed.        

    Lemma normalized_Lt : forall s s' w w' v,
      normalized s' v = true -> 
      Subst_Le (@existT _ _ s' w') (@existT _ _ s w) ->
      normalized s v = true.
    Proof.
      intros. change s with (projT1 (@existT _ _ s w)). eapply normalized_Lt'; eauto.
      simpl. auto.
    Qed.

    Theorem Refl_Subst_Le : RelationClasses.Reflexive Subst_Le.
    Proof.
      red; unfold Subst_Le; intros. destruct x; simpl in *.
      unfold exprInstantiate in *; simpl in *.
      rewrite WellFormed_Canonical; auto. eapply w; eauto.
    Qed.

    Theorem Antisym_Subst_Le : @RelationClasses.Antisymmetric _ _ Equiv_Subst_Equal Subst_Le.
    Proof.
      red; unfold Subst_Le, Subst_Equal, FM.Equal; intros; eauto.
      destruct x; destruct y; unfold exprInstantiate in *; simpl in *.
      induction e; simpl;
        repeat match goal with
                 | [ H : _ |- _ ] => rewrite H
               end; auto.
      { unfold subst_lookup.
        case_eq (FM.find x1 x0); intros.
          eapply FACTS.find_mapsto_iff in H1. generalize H1. eapply w0 in H1. eapply normalized_Lt in H1.
            2: instantiate (1 := w). 2: instantiate (1 := w0). 2: unfold Subst_Le; simpl; auto.
            intros.
            apply H in H2. rewrite WellFormed_Canonical in H2; eauto.
            eapply FACTS.find_mapsto_iff in H2. rewrite H2; reflexivity.

          eapply FACTS.not_find_in_iff in H1.
          assert (~FM.In x1 x).
          intro. apply H1. apply MFACTS.MapsTo_def.
          destruct H2. eapply H0 in H2. eauto.
          apply FACTS.not_find_in_iff in H2. rewrite H2. auto. }
      { f_equal. induction H1; simpl; f_equal; auto. }
    Qed.

    Theorem Trans_Subst_Le : RelationClasses.Transitive Subst_Le.
    Proof.
      red; unfold Subst_Le; intros.
        eapply H0 in H1. eapply H in H1.
        erewrite WellFormed_subst in H1; auto.
    Qed.

    (** Unification **) 
    Definition subst_set (k : nat) (v : expr types) (s : FM.t (expr types)) 
      : option (FM.t (expr types)) :=
      let v' := subst_exprInstantiate s v in
      if mentionsU k v'
      then None
      else let s := FM.add k v' s in
           let s := FM.map (subst_exprInstantiate s) s in
           if FM.fold (fun k e (acc : bool) => if acc then true else mentionsU k e) s false
           then None
           else Some s.
    
    Lemma subst_set_wf : forall k v s s',
      WellFormed s ->
      subst_set k v s = Some s' ->
      WellFormed s'.
    Proof.
      unfold subst_set; intros.
    Admitted.

    Definition Subst_set (k : nat) (v : expr types) (s : Subst) : option Subst :=
      match subst_set k v (projT1 s) as t return subst_set k v (projT1 s) = t -> _ with
        | None => fun _ => None
        | Some s' => fun pf => Some (@existT _ _ s' (@subst_set_wf _ _ _ _ (projT2 s) pf))
      end refl_equal.
    
    Definition get_Eq (t : tvar) : forall x y : tvarD types t, option (x = y) :=
      match t as t return forall x y : tvarD types t, option (x = y) with
        | tvProp => fun _ _ => None
        | tvType t => 
          match nth_error types t as k 
            return forall x y : match k with
                                  | Some t => Impl t
                                  | None => Empty_set
                                end, option (x = y)
            with
            | None =>
              fun x _ => 
                match x with
                end
            | Some t => Expr.Eq t
          end 
      end.

    Section fold_in.
      Variable LS : list (expr types).
      Variable F : forall (l r : expr types), Subst -> In l LS -> option Subst.

      Fixpoint dep_in (ls rs : list (expr types)) (sub : Subst) : (forall l, In l ls -> In l LS) -> option Subst.
      refine (
        match ls as ls , rs as rs return (forall l, In l ls -> In l LS) -> option Subst with
          | nil , nil => fun _ => Some sub
          | l :: ls , r :: rs => fun pf_trans =>
            match F l r sub _ with
              | None => None
              | Some sub => dep_in ls rs sub (fun ls pf => pf_trans _ _)
            end
          | _ , _ => fun _ => None
        end).
        Focus 2.
        refine (or_intror _ pf).
        refine (pf_trans _ (or_introl _ (refl_equal _))).
      Defined.
 
      Variable F' : forall (l r : expr types), Subst -> option Subst.

      Fixpoint fold2_option (ls rs : list (expr types)) (sub : Subst) : option Subst :=
        match ls , rs with
          | nil , nil => Some sub
          | l :: ls , r :: rs =>
            match F' l r sub with
              | None => None
              | Some sub => fold2_option ls rs sub
            end
          | _ , _ => None
        end.

    End fold_in.

    Definition exprUnify_recursor bound_l 
      (recur : forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b bound_l -> expr types -> Subst -> option Subst)
      (r : expr types) (sub : Subst) : option Subst.
    refine (
      match bound_l as bound_l
        return (forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b bound_l -> expr types -> Subst -> option Subst)
        -> option Subst
        with
        | (bound,l) =>
          match l as l , r as r 
            return (forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b (bound, l) -> expr types -> Subst -> option Subst)
            -> option Subst
            with
            | Const t v , Const t' v' => fun _ =>
              match equiv_dec t t' with
                | left pf => match pf in _ = k return tvarD _ k -> _ with
                               | refl_equal => fun v' =>
                                 if get_Eq t v v'
                                   then Some sub
                                   else None
                             end v'
                | right _ => None
              end
            | Var v , Var v' => fun _ => 
              if Peano_dec.eq_nat_dec v v' 
                then Some sub
                else None
            | Func f1 args1 , Func f2 args2 => fun recur =>
              match equiv_dec f1 f2 with
                | left _ => 
                  @dep_in args1 (fun l r s pf => recur (bound, l) _ r s) args1 args2 sub (fun _ pf => pf)
                | right _ => None
              end
            | Equal t1 e1 f1 , Equal t2 e2 f2 => fun recur =>
              if equiv_dec t1 t2 then
                match recur (bound, e1) _ e2 sub with
                  | None => None
                  | Some sub => recur (bound, f1) _ f2 sub
                end
                else
                  None
            | Not e1 , Not e2 => fun recur =>
              recur (bound,e1) _ e2 sub
            | UVar u , _ =>
              match Subst_lookup u sub with
                | None => fun recur =>
                  Subst_set u r sub
                | Some l' =>
                  match bound as bound return 
                    (forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b (bound,UVar u) -> expr types -> Subst -> option Subst)
                    -> option Subst with
                    | 0 => fun _ => None
                    | S bound => fun recur => recur (bound, l') _ r sub
                  end
              end
            | l , UVar u =>
              match Subst_lookup u sub with
                | None => fun recur =>
                  Subst_set u l sub
                | Some r' =>
                  match bound as bound return 
                    (forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b (bound,l) -> expr types -> Subst -> option Subst)
                    -> option Subst with
                    | 0 => fun _ => None
                    | S bound => fun recur => recur (bound, l) _ r' sub
                  end
              end
            | _ , _ => fun _ => None
          end 
      end recur
    ); try solve [ apply GenRec.L ; constructor | apply GenRec.R ; constructor; assumption ].
    Defined.

    (** index by a bound, since the termination argument is not trivial
     ** it is guaranteed to not make more recursions than the number of
     ** uvars.
     **)
    Definition exprUnify (bound : nat) (l : expr types) : expr types -> Subst -> option Subst :=
      (@Fix _ _ (guard 4 (GenRec.wf_R_pair GenRec.wf_R_nat (@wf_R_expr types)))
        (fun _ => expr types -> Subst -> option Subst) exprUnify_recursor) (bound,l).

    (** Proofs **)
    Section equiv.
      Variable A : Type.
      Variable R : A -> A -> Prop.
      Hypothesis Rwf : well_founded R.
      Variable P : A -> Type.
      
      Variable equ : forall x, P x -> P x -> Prop.
      Hypothesis equ_Equiv : forall x, RelationClasses.Equivalence (@equ x).
      
      Variable F : forall x : A, (forall y : A, R y x -> P y) -> P x.

      Lemma Fix_F_equ : forall (x : A) (r : Acc R x),
        equ (@F x (fun (y : A) (p : R y x) => Fix_F P F (Acc_inv r p)))
        (Fix_F P F r).
      Proof.
        eapply Acc_inv_dep; intros.
        simpl in *. reflexivity.
      Qed.

      Lemma Fix_F_inv_equ : 
        (forall (x : A) (f g : forall y : A, R y x -> P y),
          (forall (y : A) (p : R y x), equ (@f y p) (g y p)) -> equ (@F x f) (@F x g)) ->
        forall (x : A) (r s : Acc R x), equ (Fix_F P F r) (Fix_F P F s).
      Proof.
        intro. intro. induction (Rwf x). intros.
        erewrite <- Fix_F_equ. symmetry. erewrite <- Fix_F_equ. symmetry.
        eapply H. intros. eauto.
      Qed.

    End equiv.

    Lemma Equiv_equiv : Equivalence
      (fun f g : expr types -> Subst -> option Subst =>
        forall (a : expr types) (b : Subst), f a b = g a b).
    Proof.
      constructor; eauto.
      red. intros. rewrite H; eauto.
    Qed.

    Lemma exprUnify_recursor_inv : forall (bound : nat)
      e1 e2 (sub : Subst) (A B : Acc _ (bound,e1))
      (w : well_founded (R_pair R_nat (R_expr (ts:=types)))),
      Fix_F (fun _ : nat * expr types => expr types -> Subst -> option Subst)
      exprUnify_recursor A e2 sub =
      Fix_F (fun _ : nat * expr types => expr types -> Subst -> option Subst)
      exprUnify_recursor B e2 sub.
    Proof.
      intros.
      eapply (@Fix_F_inv_equ (nat * expr types) (R_pair R_nat (R_expr (ts:=types)))
        w
        (fun _ : nat * expr types => expr types -> Subst -> option Subst)
        (fun x f g => forall a b, f a b = g a b)
        (fun _ => Equiv_equiv)
        exprUnify_recursor).
      clear. intros.
      unfold exprUnify_recursor. destruct x. destruct e; destruct a; auto;
      repeat match goal with 
               | _ => reflexivity
               | [ H : _ |- _ ] => rewrite H
               | [ |- context [ match ?X with 
                                  | _ => _
                                end ] ] => destruct X
             end.
      generalize (fun (l1 : expr types) (pf : In l1 l) => pf).
      assert (
        forall l' l0 b, forall i : forall l1 : expr types, In l1 l' -> In l1 l,
          dep_in l
          (fun (l1 r0 : expr types) (s : Subst) (pf : In l1 l) =>
            f (n, l1)
            (R R_nat (R_expr (ts:=types)) n l1 (Func f0 l) (R_Func f0 l l1 pf))
            r0 s) l' l0 b i =
          dep_in l
          (fun (l1 r0 : expr types) (s : Subst) (pf : In l1 l) =>
            g (n, l1)
            (R R_nat (R_expr (ts:=types)) n l1 (Func f0 l) (R_Func f0 l l1 pf))
            r0 s) l' l0 b i).
      induction l'; simpl in *; intros; auto.
      destruct l1; auto. 
      rewrite H. destruct (g (n, a)); auto.
      eapply H0.
    Qed.

    Theorem exprUnify_unroll : forall bound l r sub,
      exprUnify bound l r sub = 
      match l , r with
        | Const t v , Const t' v' =>
          match equiv_dec t t' with
            | left pf => match pf in _ = k return tvarD _ k -> _ with
                           | refl_equal => fun v' =>
                             if get_Eq t v v'
                               then Some sub
                               else None
                         end v'
            | right _ => None
          end
        | Var v , Var v' => 
          if Peano_dec.eq_nat_dec v v' 
            then Some sub
            else None
        | Func f1 args1 , Func f2 args2 =>
          match equiv_dec f1 f2 with
            | left _ =>
              fold2_option (@exprUnify bound) args1 args2 sub
            | right _ => None
          end
        | Equal t1 e1 f1 , Equal t2 e2 f2 =>
          if equiv_dec t1 t2 then
            match exprUnify bound e1 e2 sub with
              | None => None
              | Some sub => exprUnify bound f1 f2 sub
            end
            else
              None
        | Not e1, Not e2 =>
          exprUnify bound e1 e2 sub
        | UVar u , _ =>
          match Subst_lookup u sub with
            | None => Subst_set u r sub
            | Some l' =>
              match bound with
                | 0 => None
                | S bound => exprUnify bound l' r sub
              end
          end
        | l , UVar u =>
          match Subst_lookup u sub with
            | None => Subst_set u l sub
            | Some r' =>
              match bound with
                | 0 => None
                | S bound => exprUnify bound l r' sub
              end
          end
        | _ , _ => None
      end.
    Proof.
      intros. unfold exprUnify at 1.
      match goal with
        | [ |- context [ guard ?X ?Y ] ] =>
          generalize (guard X Y)
      end.
      intros. unfold Fix.
      rewrite <- (@Fix_F_equ (nat * expr types) (R_pair R_nat (R_expr (ts:=types)))
        (fun _ : nat * expr types => expr types -> Subst -> option Subst)
        (fun x f g => forall a b, f a b = g a b)
        (fun _ => Equiv_equiv)
        exprUnify_recursor
        (bound,l)
        (w (bound,l))
        r sub).
      destruct l; destruct r; simpl; intros; auto;
        try solve [
          repeat match goal with
                   | [ |- context [ match ?X with 
                                      | _ => _ 
                                    end ] ] => destruct X
                 end; try solve [ auto | 
                   unfold exprUnify, Fix ;
                     eapply exprUnify_recursor_inv; eauto ] ].
      Focus 2.
      destruct (equiv_dec t t0); auto.
      unfold exprUnify, Fix.
      erewrite exprUnify_recursor_inv; eauto.
      instantiate (1 := (guard 4 (wf_R_pair wf_R_nat (wf_R_expr (ts:=types))) (bound, l1))).
      match goal with 
        | [ |- match ?X with 
                 | _ => _ 
               end = _ ] => destruct X
      end; auto.
      erewrite exprUnify_recursor_inv; eauto.

      match goal with
        | [ |- match ?X with
                 | _ => _
               end = _ ] => destruct X; auto
      end.
      generalize (fun (l1 : expr types) (pf : In l1 l) => pf).
      assert (forall l' l0 sub,
        forall i : (forall l1 : expr types, In l1 l' -> In l1 l),
          dep_in l
          (fun (l1 r0 : expr types) (s : Subst) (pf : In l1 l) =>
            @Fix_F _ _ (fun _ : nat * expr types => expr types -> Subst -> option Subst)
            exprUnify_recursor (bound, l1) (@Acc_inv (nat * expr types)
              (@R_pair nat (expr types) R_nat (@R_expr types))
              (bound, @Func types f l) (w (bound, @Func types f l)) 
              (bound, l1)
              (@R nat (expr types) R_nat (@R_expr types) bound l1
                (@Func types f l) (@R_Func types f l l1 pf))) r0 s) l' l0 sub i =
          fold2_option (exprUnify bound) l' l0 sub).
      induction l'; simpl; intros; destruct l1; auto.
      erewrite exprUnify_recursor_inv; eauto.
      instantiate (1 := (guard 4 (wf_R_pair wf_R_nat (wf_R_expr (ts:=types))) (bound, a))).
      unfold exprUnify, Fix.
      match goal with
        | [ |- match ?X with
                 | _ => _
               end = _ ] => destruct X; auto
      end.
      eapply H.
    Qed.

    Lemma Subst_set_Extends : forall k v sub sub',
      Subst_set k v sub = Some sub' ->
      Subst_Le sub' sub.
    Proof.
      unfold Subst_set; simpl; intros.
      revert H.
      match goal with
        | [ |- context [ eq_refl ?X ] ] => generalize (eq_refl X)
      end.
      generalize (subst_set k v (projT1 sub)) at 2 3. intro. 
      destruct o; intros; try congruence.
        inversion H; clear H; subst.
        destruct sub. unfold Subst_Le, exprInstantiate; simpl in *.
      admit.
    Qed.

    Lemma fold2_option_exprUnify_Le' : forall b l l0 sub sub',
      fold2_option (exprUnify b) l l0 sub = Some sub' ->
      Forall
      (fun l : expr types =>
        forall (r : expr types) (sub sub' : Subst),
          exprUnify b l r sub = Some sub' -> Subst_Le sub' sub) l ->
      Subst_Le sub' sub.
    Proof.
      intros.
      generalize dependent l0. generalize dependent sub.
      induction H0; destruct l0; simpl in *; try congruence; intros.
        inversion H; eapply Refl_Subst_Le.

      revert H1; case_eq (exprUnify b x e sub); try congruence; intros.
      eapply Trans_Subst_Le; eauto. 
    Qed.

    Theorem exprUnify_extends : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      Subst_Le sub' sub.
    Proof.
      induction n; induction l; intros; rewrite exprUnify_unroll in *; destruct r; simpl in *;
        try solve [ 
          repeat (congruence || eauto ||
              solve [ eapply Subst_set_Extends; eauto |
                      eapply Trans_Subst_Le; eauto |
                      apply Refl_Subst_Le |
                  eapply fold2_option_exprUnify_Le'; eauto ] ||
              match goal with
                | [ H : Equivalence.equiv _ _ |- _ ] => 
                  unfold Equivalence.equiv in H; subst
                | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                | [ H : match exprUnify ?A ?B ?C ?D with _ => _ end = _ |- _ ] => 
                  revert H; case_eq (exprUnify A B C D); intros
                | [ H : match ?X with _ => _ end = _ |- _ ] => destruct X
              end) ].
    Qed.

    Lemma fold2_option_exprUnify_Extends : forall b l l0 sub sub',
      fold2_option (exprUnify b) l l0 sub = Some sub' ->
      Subst_Le sub' sub.
    Proof.
      induction l; destruct l0; simpl in *; try congruence; intros.
        inversion H; subst; apply Refl_Subst_Le.
      revert H; case_eq (exprUnify b a e sub); try congruence; intros.
      eapply Trans_Subst_Le; eauto using exprUnify_extends.
    Qed.

    Lemma Subst_lookup_Subst_set : forall k v s s',
      Subst_set k v s = Some s' ->
      Subst_lookup k s' = Some (exprInstantiate s v).
    Proof.
      unfold Subst_set, Subst_lookup; do 4 intro.
(*
      case_eq (mentionsU k (exprInstantiate s v)); try congruence.
      match goal with
        | [ |- context [ if ?X then _ else _ ] ] => case_eq X; try congruence
      end; intros.
      inversion H1; clear H1; subst.
      rewrite FACTS.map_o. unfold FACTS.option_map. rewrite FACTS.add_o.
      destruct (FM.E.eq_dec k k); intros. 2: exfalso; auto.
      f_equal.

      clear. (** TODO: probably not legit **)
      induction v; simpl; auto.
        destruct (Subst_lookup x s); auto.
*)
    Admitted.

    Lemma Subst_lookup_Extends : forall sub sub' k v,
      Subst_lookup k sub = Some v ->
      Subst_Le sub' sub ->
      Subst_lookup k sub' = Some (exprInstantiate sub' v).
    Proof.

(*
      intro. unfold Subst_lookup, Subst_Le. eapply PROPS.map_induction with (m := sub); simpl; intros.
        eapply FACTS.find_mapsto_iff in H0. exfalso. eapply H. eauto.

        rewrite H1 in H2. rewrite FACTS.add_o in H2.
        destruct (FM.E.eq_dec x k). inversion H2; clear H2; subst.

*)
    Admitted.


    Lemma Subst_set_Subst_lookup : forall k v sub sub',
      Subst_set k v sub = Some sub' ->
      Subst_lookup k sub' = Some (exprInstantiate sub' v).
    Proof.
(*
      unfold Subst_set, Subst_lookup; intros.
      destruct (mentionsU k (exprInstantiate sub v)); try congruence.
      match goal with
        | [ H : (if ?X then _ else _) = _ |- _ ] => destruct X; try congruence
      end.
      inversion H; clear H; subst.
      rewrite FACTS.map_o. unfold FACTS.option_map.
      repeat rewrite FACTS.add_o. destruct (FM.E.eq_dec k k); try solve [ exfalso; eauto ].
      f_equal.
      clear. revert k; revert sub. induction v; simpl; intros; auto.
      



      SearchAbout FM.find.


      assert (sub' = FM.map (exprInstantiate (FM.add k (exprInstantiate sub v) sub))
        (FM.add k (exprInstantiate sub v) sub)).
      generalize dependent sub'.
      generalize dependent ((FM.map (exprInstantiate (FM.add k (exprInstantiate sub v) sub))
           (FM.add k (exprInstantiate sub v) sub))). clear.
      intro. eapply PROPS.fold_rec with (m := t); intros.
        inversion H0; clear H0; subst.
*)
    Admitted.


    Lemma exprInstantiate_extends : forall l r sub sub',
      exprInstantiate sub l = exprInstantiate sub r ->
      Subst_Le sub' sub -> 
      exprInstantiate sub' l = exprInstantiate sub' r.
    Proof.
    Admitted.

    Lemma fold2_option_map_sound' : forall (n : nat) (l l0 : list (expr types)) (sub sub' : Subst),
      fold2_option (exprUnify n) l l0 sub = Some sub' ->
      Forall
      (fun l1 : expr types =>
        forall (r : expr types) (sub0 sub'0 : Subst),
          exprUnify n l1 r sub0 = Some sub'0 ->
          exprInstantiate sub'0 l1 = exprInstantiate sub'0 r) l ->
      map (exprInstantiate sub') l = map (exprInstantiate sub') l0.
    Proof.
      intros.
      generalize dependent l0. revert sub; revert sub'. 
      induction H0; simpl in *; intros; destruct l0; simpl in *; try congruence; auto.
      revert H1. case_eq (exprUnify n x e sub); intros; try congruence.
      f_equal; eauto using exprInstantiate_extends, exprUnify_extends, fold2_option_exprUnify_Extends.
    Qed.

    Theorem exprUnify_sound : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      exprInstantiate sub' l = exprInstantiate sub' r.
    Proof.
      induction n; induction l; intros; rewrite exprUnify_unroll in *; destruct r; simpl in *;
        try solve [ 
          repeat (congruence || 
                  solve [ eauto |
                          eapply exprInstantiate_extends; eauto using exprUnify_extends |
                          eapply fold2_option_map_sound'; eauto ] ||
              match goal with
                | [ H : Equivalence.equiv _ _ |- _ ] => 
                  unfold Equivalence.equiv in H; subst
                | [ H : _ |- _ ] => erewrite H by eauto
                | [ |- _ ] => erewrite Subst_set_Subst_lookup by eauto
                | [ H : forall (l r : expr types) (sub sub' : Subst), exprUnify _ l r sub = Some sub' -> _ , H' : _ |- _ ] =>
                  specialize (@H _ _ _ _ H')
                | [ H : Subst_lookup _ _ = _ |- _ ] =>
                  eapply Subst_lookup_Extends in H; [ | solve [ eauto using exprUnify_extends ] ]
                | [ H : match exprUnify ?A ?B ?C ?D with _ => _ end = _ |- _ ] => 
                  revert H; case_eq (exprUnify A B C D); intros
                | [ H : match Subst_lookup ?X ?Y with _ => _ end = _ |- _ ] =>
                  revert H; case_eq (Subst_lookup X Y); intros
                | [ H : match ?X with _ => _ end = _ |- _ ] => destruct X
                | [ |- Equal _ _ _ = Equal _ _ _ ] => f_equal
                | [ |- Func _ _ = Func _ _ ] => f_equal
              end) ].

repeat (congruence || 
                  solve [ eauto |
                          eapply exprInstantiate_extends; eauto using exprUnify_extends |
                          eapply fold2_option_map_sound'; eauto ] ||
              match goal with
                | [ H : Equivalence.equiv _ _ |- _ ] => 
                  unfold Equivalence.equiv in H; subst
                | [ H : _ |- _ ] => erewrite H by eauto
                | [ |- _ ] => erewrite Subst_set_Subst_lookup by eauto
                | [ H : forall (l r : expr types) (sub sub' : Subst), exprUnify _ l r sub = Some sub' -> _ , H' : _ |- _ ] =>
                  specialize (@H _ _ _ _ H')
                | [ H : Subst_lookup _ _ = _ |- _ ] =>
                  eapply Subst_lookup_Le in H; [ | solve [ eauto using exprUnify_extends ] ]
                | [ H : match exprUnify ?A ?B ?C ?D with _ => _ end = _ |- _ ] => 
                  revert H; case_eq (exprUnify A B C D); intros
                | [ H : match Subst_lookup ?X ?Y with _ => _ end = _ |- _ ] =>
                  revert H; case_eq (Subst_lookup X Y); intros
                | [ H : match ?X with _ => _ end = _ |- _ ] => destruct X
                | [ |- Equal _ _ _ = Equal _ _ _ ] => f_equal
                | [ |- Func _ _ = Func _ _ ] => f_equal
              end).
    Admitted.
  
  End typed.
End Unifier.

(*

Module SUBST := NatMap.IntMap.

Section typed.
  Variable types : list type.

  Definition Subst : Type :=
    SUBST.t (expr types).


  Definition Subst_lookup (k : nat) (s : Subst) : option (expr types) :=
    SUBST.find k s.

  

  Section SubstDenote.
    Variable funcs : functions types.
    Variable vars : env types.
    Variable sub : Subst.


    Fixpoint Subst_equations (ls : env types) (cur : nat) : env types -> Prop :=
      match ls with
        | nil => fun _ => True
        | l :: ls =>
          let P := Subst_equations ls (S cur) in
          match Subst_lookup cur sub with
            | None => P
            | Some v => fun g => 
              match exprD funcs g vars v (projT1 l) with 
                | Some v => v = projT2 l
                | None => False
              end /\ P g
          end
      end.
  End SubstDenote.

  Definition empty_Subst : Subst :=
    SUBST.empty _.

(*
  Fixpoint anyb T (F : T -> bool) (ls : list T) : bool :=
    match ls with
      | nil => false
      | l :: ls => F l || anyb F ls 
    end.
*)



  (** Syntactic Unification **)
  Section Unifies.
    Variable funcs : functions types.
    Variable vars : env types.
    
    (** NOTE: the meaning of Prop isn't quite perfect. We currently reflect Props
     ** but we actually mean proofs, i.e. using the Provable predicate.
     **)
    Definition unifies uenv env (t : tvar) (l r : expr types) : Prop :=
      match exprD funcs uenv env l t , exprD funcs uenv env r t with
        | Some l , Some r => match t as t return tvarD types t -> tvarD types t -> Prop with
                               | tvProp => fun l r => l <-> r (** we'll weaken things a bit more **)
                               | tvType _ => fun l r => l = r
                             end l r
        | _ , _ => False
      end.
  End Unifies.


  Section Correctness.
    Variable funcs : functions types.
    Variable vars : env types.

    Theorem exprUnify_correct : forall env uvars l r t sub sub' n,
      exprUnify n l r sub = Some sub' ->
      existsEach uvars (fun uenv =>
        Subst_equations funcs env sub uenv 0 uenv /\  
        is_well_typed funcs uenv env l t = true /\ 
        is_well_typed funcs uenv env r t = true) ->
      existsEach uvars (fun uenv =>
        Subst_equations funcs env sub' uenv 0 uenv /\  
        unifies funcs uenv env t l r).
    Proof.
(*
      induction l; destruct r; intuition; simpl in *; try congruence;
        repeat (match goal with 
                  | [ H : existsEach _ _ |- _ ] => 
                    apply existsEach_sem in H
                  | [ H : exists x, _ |- _ ] => destruct H
                  | [ H : match ?X with 
                            | left _ => _
                            | right _ => _ 
                          end = _ |- _ ] => destruct X; try congruence
                  | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                  | [ H : match ?X with 
                            | None => _
                            | Some _ => _ 
                          end = _ |- _ ] => revert H; case_eq X; intros; try congruence
                end; intuition; unfold equiv in *; subst); 
        eapply existsEach_sem.
      Focus. (** const **)
        exists x; intuition. unfold unifies; simpl. repeat rewrite EquivDec_refl_left.
        destruct t3; intuition auto.
      
      Focus. (** var **)
        exists x1; intuition eauto.
        unfold unifies; simpl. rewrite H. destruct t; intuition eauto.

      Focus. (** equal **)
        destruct t1; try congruence.
        apply andb_true_iff in H4. apply andb_true_iff in H2.
        intuition.
        eapply IHl1 with (t := t0) in H; [ | apply existsEach_sem; exists x; intuition ].
        apply existsEach_sem in H. destruct H; intuition.
        eapply IHl2 with (t := t0) in H1; [ | apply existsEach_sem; exists x0; intuition ].

        Focus.
        apply existsEach_sem in H1. destruct H1; intuition.
        exists x1; intuition eauto. unfold unifies; simpl.
*)
    Admitted.
  End Correctness.

End typed.

Module TEST.
  Definition types := ({| Impl := nat ; Eq := fun _ _ => None |} :: nil).
  
  Definition vars_env : env types := nil.
  Definition uvars := tvType 0 :: tvType 0 :: tvType 0 :: nil.
  Definition subst := 
    let s := empty_Subst types in
    Subst_set 1 (UVar 0) s.
  Definition funcs : functions types := nil.

  Goal 
    existsEach uvars (fun uenv =>
      match subst with 
        | None => False
        | Some subst => 
          Subst_equations funcs vars_env subst uenv 0 uenv 
      end /\  
      AllProvable funcs uenv vars_env 
        ((Equal (tvType 0) (UVar 0) (UVar 2)) :: 
         (Equal (tvType 0) (UVar 0) (@Const types (tvType 0) 3)) :: nil)).
    compute.
  Abort.
End TEST.
*)


(**
(** TODO:
 ** this seems like a more difficult interface, but it seems realistic given 
 ** that you can't actually conclude more information after a substitution occurs
 ** you can only ensure that the substitution is consistent with the equation
 **)
Module Type SemUnifier.
  (** An environment that maintains a mapping from variables to their meaning **)
  Parameter Subst : list type -> Type.

  Section typed.
    Variable types : list type.
    
    Parameter Subst_empty : Subst types.

    (** The invariant that the substitution implies.
     **)
    Parameter SubstInv : forall (funcs : functions types) (meta_env var_env : env types), Subst types -> list (tvar * expr types * expr types) -> Prop.

    (** The actual unification algorithm **)
    Parameter exprUnify : nat -> expr types -> expr types -> Subst types -> option (Subst types).
    
    (** Substitute meta variables **)
    Parameter exprInstantiate : Subst types -> expr types -> expr types.

    Variable funcs : functions types.
    Variable vars : env types.
    
    (** NOTE: the meaning of Prop isn't quite perfect. We currently reflect Props
     ** but we actually mean proofs, i.e. using the Provable predicate.
     **)
    Definition unifies uenv env (t : tvar) (l r : expr types) : Prop :=
      match exprD funcs uenv env l t , exprD funcs uenv env r t with
        | Some l , Some r => match t as t return tvarD types t -> tvarD types t -> Prop with
                               | tvProp => fun l r => l <-> r (** we'll weaken things a bit more **)
                               | tvType _ => fun l r => l = r
                             end l r
        | _ , _ => False
      end.

    Axiom SubstInv_empty : forall uenv env sub,
      SubstInv funcs uenv env sub nil.

    Axiom SubstInvD : forall uenv env sub ctx,
      SubstInv funcs uenv env sub ctx ->
      Forall (fun t_l_r => 
        let '(t,l,r) := t_l_r in
        unifies uenv env t l r) ctx.

    (** This is the soundness statement.
     ** TODO: Is this correct?
     **)
    Axiom exprUnify_sound : forall env uenv l r t sub sub' n ctx,
      exprUnify n l r sub = Some sub' ->
      SubstInv funcs uenv env sub ctx ->
      is_well_typed funcs uenv env l t = true ->
      is_well_typed funcs uenv env r t = true ->
      SubstInv funcs uenv env sub' ((t,l,r) :: ctx).

  End typed.

End Unifier.
**)