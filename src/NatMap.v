Require Import HintlessOrderedType HintlessFMapAVL.
Require Import List.

Set Implict Arguments.
Set Strict Implicit.

Module Ordered_nat <: OrderedType with Definition t := nat.
  Definition t := nat.
  Definition eq := @eq nat. 
  Definition lt := @lt.

  Theorem eq_refl : forall x, eq x x.
    reflexivity.
  Qed.

  Theorem eq_sym : forall a b, eq a b -> eq b a.
    intros; symmetry; auto.
  Qed.    

  Theorem eq_trans : forall a b c, eq a b -> eq b c -> eq a c.
    intros; etransitivity; eauto.
  Qed.

  Require Import Omega.
  Theorem lt_trans : forall a b c, lt a b -> lt b c -> lt a c.
    intros. unfold lt in *. omega.
  Qed.
     
  Theorem lt_not_eq : forall a b, lt a b -> ~(eq a b).
    unfold eq, lt. intros; omega.
  Qed.

  Definition compare (x y : t) : OrderedType.Compare lt eq x y :=
    match Compare_dec.nat_compare x y as r return
      Compare_dec.nat_compare x y = r -> OrderedType.Compare lt eq x y
      with 
      | Lt => fun pf => OrderedType.LT (lt:=lt) (nat_compare_Lt_lt _ _ pf)
      | Eq => fun pf => OrderedType.EQ (lt:=lt) (Compare_dec.nat_compare_eq _ _ pf)
      | Gt => fun pf => OrderedType.GT (lt:=lt) (nat_compare_Gt_gt _ _ pf)
    end (refl_equal _).

  Definition eq_dec : forall x y : nat, {x = y} + {x <> y} := 
    Peano_dec.eq_nat_dec.

End Ordered_nat.

Module IntMap := HintlessFMapAVL.Make Ordered_nat.

Require HintlessFMapFacts.
Module IntMapFacts := HintlessFMapFacts.WFacts_fun(Ordered_nat)(IntMap).

Module IntMapProperties := HintlessFMapFacts.WProperties_fun(Ordered_nat)(IntMap).

Definition singleton {T} (k : nat) (v : T) : IntMap.t T :=
  IntMap.add k v (IntMap.empty _).

(** Neither Properties nor Facts contains anything useful about 'map' **)
Module MoreFMapFacts (FM : HintlessFMapInterface.WS).
  
  Module PROPS := HintlessFMapFacts.WProperties_fun(FM.E) FM.
  Module FACTS := HintlessFMapFacts.WFacts_fun FM.E FM.    

  Definition union T :=
    FM.fold (fun k (v : T) a => FM.add k v a).

  Lemma add_remove_Equal : forall (elt : Type) k (v : elt) m,
    FM.Equal (FM.add k v m) (FM.add k v (FM.remove k m)).
  Proof.
    clear. unfold FM.Equal. intros.
    repeat (rewrite FACTS.add_o || rewrite FACTS.remove_o).
    destruct (FM.E.eq_dec k y); auto.
  Qed.

  Lemma map_Empty : forall T U (F : T -> U) m,
    FM.Empty m ->
    FM.Empty (FM.map F m).
  Proof.
    intros.
    unfold FM.Empty in *.
    intros. intro.
    eapply FACTS.map_mapsto_iff in H0. destruct H0; intuition. eauto.
  Qed.

  Lemma union_empty : forall T m,
    FM.Equal (union T m (FM.empty _)) m.
  Proof.
    intros. unfold union.
    remember (FM.empty T).
    apply PROPS.map_induction with (m := m); intros.
      rewrite PROPS.fold_Empty; eauto with typeclass_instances. subst; auto.
      unfold FM.Equal, FM.Empty in *. intros.
      rewrite FACTS.empty_o. case_eq (FM.find y m0); intros; auto.
      exfalso. eapply H. eapply FM.find_2; eauto.
      
    erewrite PROPS.fold_Add; eauto with typeclass_instances.
    rewrite H. unfold PROPS.Add, FM.Equal in *. eauto.
    
    repeat (red; intros; subst).
    repeat (rewrite FACTS.add_o).
      destruct (FM.E.eq_dec k y); auto.
      destruct (FM.E.eq_dec k' y); auto. rewrite <- e1 in e2. exfalso; auto.
  Qed.

  Lemma map_fold' : forall T U (F : T -> U) (m : FM.t T) (m' : FM.t U),
    FM.Equal (union _ (FM.map F m) m')
             (FM.fold (fun k v a => FM.add k (F v) a) m m').              
  Proof.
    do 4 intro. unfold union.
    eapply PROPS.map_induction with (m := m); intros.
    symmetry.
    rewrite PROPS.fold_Empty; eauto with typeclass_instances.
    rewrite PROPS.fold_Empty; eauto with typeclass_instances. reflexivity.
    eapply map_Empty; auto.

    symmetry; rewrite PROPS.fold_Add; eauto with typeclass_instances.
      specialize (H m'0).
      cut (PROPS.Add x (F e) (FM.map F m0) (FM.map F m')); intros.
      symmetry. rewrite PROPS.fold_Add. 6: eapply H2. 2: eauto with typeclass_instances.
      rewrite H. reflexivity.
      
      repeat (red; intros; subst). rewrite H3. rewrite H4. reflexivity.
      repeat (red; intros; subst). repeat rewrite FACTS.add_o.
      destruct (FM.E.eq_dec k y); destruct (FM.E.eq_dec k' y); eauto.
      rewrite <- e1 in e2; exfalso; auto.
      intro. apply FACTS.map_in_iff in H3. auto.
      
      unfold PROPS.Add in *; intros.
      specialize (H1 y). repeat (rewrite FACTS.add_o || rewrite FACTS.map_o || rewrite H1).
      unfold FACTS.option_map.
      destruct (FM.E.eq_dec x y); auto.

      repeat (red; intros; subst). rewrite H3. rewrite H2. reflexivity.
      repeat (red; intros; subst). repeat rewrite FACTS.add_o.
      repeat match goal with 
               | [ |- context [ FM.E.eq_dec ?X ?Y ] ] => destruct (FM.E.eq_dec X Y); auto
             end.
      rewrite <- e1 in e2; exfalso; auto.
  Qed.

  Lemma map_fold : forall T U (F : T -> U) m,
    FM.Equal (FM.map F m)
             (FM.fold (fun k v a => FM.add k (F v) a) m (FM.empty _)).
  Proof.
    intros. etransitivity. symmetry; apply union_empty. apply map_fold'. 
  Qed.

  Section fusion.
    Variable T U V : Type.
    Variable F : T -> U.
    Variable G : FM.key -> U -> V -> V.
    Hypothesis equ : V -> V -> Prop.
    Hypothesis equ_Equiv : RelationClasses.Equivalence equ.
    Hypothesis G_trans: PROPS.transpose_neqkey equ G.
    Hypothesis G_respect: Morphisms.Proper
      (Morphisms.respectful FM.E.eq
        (Morphisms.respectful eq (Morphisms.respectful equ equ))) G.
    
    Local Hint Resolve G_trans G_respect equ_Equiv.
    Local Hint Extern 1 (Morphisms.Proper _ _) => 
      clear; repeat (red; intros; subst); repeat rewrite FACTS.add_o;
        repeat match goal with 
                 | [ |- context [ FM.E.eq_dec ?X ?Y ] ] => 
                   destruct (FM.E.eq_dec X Y)
                 | [ H : FM.E.eq ?X ?Y |- _ ] => rewrite H in *
               end; auto; exfalso; auto.
    Local Hint Extern 1 (PROPS.transpose_neqkey _ _) => 
      clear; repeat (red; intros; subst); repeat rewrite FACTS.add_o;
        repeat match goal with 
                 | [ |- context [ FM.E.eq_dec ?X ?Y ] ] => 
                   destruct (FM.E.eq_dec X Y)
                 | [ H : FM.E.eq ?X ?Y |- _ ] => rewrite H in *
               end; auto; exfalso; auto.
    Local Hint Resolve FACTS.EqualSetoid.

    Lemma fold_map_fusion : forall m a,
      equ (FM.fold G (FM.map F m) a)
      (FM.fold (fun k x acc => G k (F x) acc) m a).
    Proof.
      intro. eapply PROPS.map_induction with (m := m); intros.
        rewrite PROPS.fold_Empty; eauto with typeclass_instances.
        rewrite PROPS.fold_Empty; eauto with typeclass_instances. eapply equ_Equiv.
        apply map_Empty. auto.

        symmetry. rewrite PROPS.fold_Add; eauto with typeclass_instances.
        2: repeat (red; intros; subst); eapply G_respect; auto.
        2: repeat (red; intros; subst); eapply G_trans; auto.

        symmetry. rewrite PROPS.fold_Equal. 5: eapply map_fold. 2: eapply equ_Equiv. 3: eapply G_trans.
        2: eapply G_respect.
        rewrite PROPS.fold_Equal. 5: rewrite PROPS.fold_Add; eauto. 
        5: reflexivity. rewrite PROPS.fold_add; eauto.
        eapply G_respect; eauto. erewrite <- H. 
        symmetry. rewrite PROPS.fold_Equal. 5: apply map_fold. reflexivity. eauto. eauto. eauto.
        
        { revert H0. clear. revert x. eapply PROPS.map_induction with (m := m0); intros.
          rewrite PROPS.fold_Empty; eauto. intro. eapply FACTS.empty_in_iff; eauto with typeclass_instances.

          rewrite PROPS.fold_Add. 6: eauto. 5: eauto. 2: eauto. 2: eauto. 2: eauto.
          intro. apply FACTS.add_in_iff in H3. destruct H3. 
            rewrite <- H3 in *. apply H2. specialize (H1 x). rewrite FACTS.add_o in *.
            destruct (FM.E.eq_dec x x); try solve [ exfalso; auto ]. apply FACTS.in_find_iff. congruence.

            eapply H. 2: eauto. intro. clear H3. specialize (H1 x0).
            rewrite FACTS.add_o in H1.
            repeat match goal with
                     | [ H : ~ FM.In _ _ |- _ ] => apply FACTS.not_find_in_iff in H
                     | [ H : FM.In _ _ |- _ ] => apply FACTS.in_find_iff in H
                   end.
            destruct (FM.E.eq_dec x x0); congruence. 
        }

        eauto.
        eauto.
        eauto.
    Qed.
  End fusion.

  Lemma MapsTo_def : forall T k m,
    FM.In k m <-> exists (v : T), FM.MapsTo k v m.
  Proof.
    unfold FM.In; split; auto.
  Qed.

End MoreFMapFacts.
