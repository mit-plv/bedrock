Require Import HintlessOrderedType.
Require Import HintlessFMapAVL.
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

Module IntMap := HintlessFMapAVL.Raw ZArith.Int.Z_as_Int Ordered_nat.

Definition singleton {T} (k : nat) (v : T) : IntMap.t T :=
  IntMap.add k v (IntMap.empty _).

(** Other Lemmas **)
(* these currently break the FMap abstraction, but they could be proved
 * using only the FMap abstraction
 *)


Theorem elements_map : forall T U (F : T -> U) m,
  IntMap.bst m ->
  IntMap.elements (IntMap.map F m) = List.map (fun x => (fst x, F (snd x))) (IntMap.elements m).
Proof.
  clear. unfold IntMap.elements. do 4 intro. 
  change (@nil (IntMap.key * U)) with (List.map (fun x => (fst x, F (snd x))) (@nil (IntMap.key * T))).
  generalize (@nil (IntMap.key * T)).
  induction m; simpl; intros; try reflexivity.
  inversion H; subst; auto.
  rewrite IHm2; eauto.
  change (((k, F e) :: map (fun x : IntMap.key * T => (fst x, F (snd x))) (IntMap.elements_aux l m2)))
    with (map (fun x : IntMap.key * T => (fst x, F (snd x))) ((k,e) :: (IntMap.elements_aux l m2))).
  rewrite IHm1; eauto.
Qed.

Lemma elements_singleton : forall T k (v : T), 
  IntMap.elements (singleton k v) = (k,v) :: nil.
Proof.
  unfold IntMap.empty. intros. reflexivity.
Qed.


Lemma find_elements_split : forall T k (v : T) m,
  IntMap.find k m = Some v ->
  exists ls, exists rs, IntMap.elements m = ls ++ (k,v) :: rs.
Proof.
  intros. apply IntMap.Proofs.find_2 in H.
  eapply IntMap.Proofs.elements_mapsto in H.
  eapply SetoidList.InA_split in H.
  do 3 destruct H. destruct x0. intuition. 
  destruct H0; simpl in *; subst. eauto.
Qed.

(*
SearchAbout IntMap.elements.

Lemma prove_elements : forall T (m : IntMap.t T) ls,
  IntMap.bst m ->
  (Sorted.Sorted (IntMap.Proofs.PX.ltk (elt:=T)) ls /\
    (forall k v, IntMap.MapsTo k v m <-> SetoidList.InA  (IntMap.Proofs.PX.eqke (elt:=T))  (k, v) ls)) <->
  IntMap.elements m = ls.
Admitted.
*)

Lemma find_elements_remove : forall T k (v : T) m ls rs,
  IntMap.bst m ->
  IntMap.elements m = ls ++ (k,v) :: rs ->
  IntMap.elements (IntMap.remove k m) = ls ++ rs.
Proof.
  intros. (*apply prove_elements in H0; auto. apply prove_elements.
  intros. *)
Admitted.

Lemma elements_find : forall T k (v : T) m,
  IntMap.find k m = Some v ->
  exists x y, IntMap.elements m = x ++ (k,v) :: y.
Proof.
  clear. induction m; intros.
  compute in H; congruence.
  simpl in H. generalize (IntMap.Proofs.elements_node m1 m2 k0 e i nil).
  repeat rewrite app_nil_r. intros. rewrite <- H0. clear H0.

  destruct (Ordered_nat.compare k k0).
  eapply IHm1 in H. do 2 destruct H. rewrite H.
  exists x. exists (x0 ++ (k0,e) :: IntMap.elements m2). repeat rewrite app_ass; simpl. reflexivity.

  inversion e0; inversion H; subst; do 2 eexists; reflexivity.
  
  apply IHm2 in H. do 2 destruct H. rewrite H.
  exists (IntMap.elements m1 ++ (k0,e) :: x). eexists. repeat rewrite app_ass; simpl. reflexivity.
Qed.

Lemma elements_add_over : forall T k (v v' : T) m x y,
  IntMap.elements m = x ++ (k,v) :: y ->
  IntMap.elements (IntMap.add k v' m) = x ++ (k,v') :: y.
Proof.
  clear; induction m; intros.
  destruct x; compute in H; congruence.          
Admitted.

(* TODO: how do i instantiate the FMapFacts module?
Require FSets.FMapFacts.
Module IntMap_WS <:  FSets.FMapInterface.WS.
  Module E := Ordered_nat.
  Include IntMap.
End IntMap_WS.

Module Ordered_nat_Props := FSets.FMapFacts.OrdProperties IntMap.
*)

Lemma elements_add_new : forall T k (v : T) m,
  IntMap.find k m = None ->
  exists x y, IntMap.elements m = x ++ y /\ IntMap.elements (IntMap.add k v m) = x ++ (k,v) :: y.
Proof.
  intros.
Admitted.


(*
Ltac reduce_nat_map :=
  cbv beta iota zeta delta 
    [ singleton
      IntMap.height IntMap.cardinal IntMap.empty IntMap.is_empty
      IntMap.mem IntMap.find IntMap.assert_false IntMap.create IntMap.bal
      IntMap.add IntMap.remove_min IntMap.merge IntMap.remove IntMap.join
      IntMap.t_left IntMap.t_opt IntMap.t_right

      Int.Z_as_Int._0 Int.Z_as_Int._1 Int.Z_as_Int._2 Int.Z_as_Int._3
      Int.Z_as_Int.plus Int.Z_as_Int.max
      Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec

      ZArith_dec.Z_gt_le_dec ZArith_dec.Z_ge_lt_dec ZArith_dec.Z_ge_dec
      ZArith_dec.Z_gt_dec 
      ZArith_dec.Zcompare_rec ZArith_dec.Zcompare_rect

      BinInt.Z.add BinInt.Z.max BinInt.Z.pos_sub
      BinInt.Z.double BinInt.Z.succ_double BinInt.Z.pred_double
      
      BinInt.Z.compare

      BinPos.Pos.add BinPos.Pos.compare 
      BinPos.Pos.succ BinPos.Pos.compare_cont

      Compare_dec.nat_compare CompOpp 

      Ordered_nat.compare

      sumor_rec sumor_rect
      sumbool_rec sumbool_rect
      eq_ind_r 

    ].


Goal 
  let m := singleton 10 10 in
  let m := IntMap.add 1 1 m in
  let m := IntMap.add 5 5 m in
  let m := IntMap.add 3 3 m in
  let m := IntMap.add 2 2 m in
    let m := IntMap.remove 3 m in
  Some 5 = IntMap.find 5 m /\
  m = m.
reduce_nat_map.
Abort.
*)