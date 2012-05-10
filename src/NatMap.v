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
Module MoreFMapFacts (FM : HintlessFMapInterface.S).
  
  Module PROPS := HintlessFMapFacts.WProperties_fun(FM.E) FM.
  Module FACTS := HintlessFMapFacts.WFacts_fun FM.E FM.    

  Definition union T :=
    FM.fold (fun k (v : T) a => FM.add k v a).

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
End MoreFMapFacts.
