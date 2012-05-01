Require Import HintlessOrderedType.

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

Require HintlessFMapAVL.

Require ZArith.Int.

(*Module IntMap := HintlessFMapAVL.Raw ZArith.Int.Z_as_Int Ordered_nat. *)

Module IntMap.

  Section parametric.
    Inductive t (T : Type) : Type := 
    | MLeaf
    | MBranch : t T -> nat -> T -> t T -> t T.

    Context {T : Type}.

    Definition empty : t T := MLeaf _.

    Section add. (** replace **)
      Variable s : nat.
      Variable v : T.

      Fixpoint add m : t T :=
        match m with
          | MLeaf => MBranch _ (MLeaf _) s v (MLeaf _)
          | MBranch l k v' r =>
            match Compare_dec.lt_eq_lt_dec s k with
              | inleft (left _) => MBranch _ (add l) k v' r 
              | inleft (right _) => MBranch _ l k v r 
              | inright _ => MBranch _ l k v' (add r)
            end
        end.
    End add.

    Fixpoint find (s : nat) (m : t T) : option T :=
      match m with
        | MLeaf => None
        | MBranch l k v r =>
          match Compare_dec.lt_eq_lt_dec s k with
            | inleft (left _) => find s l
            | inleft (right _) => Some v
            | inright _ => find s r
          end
      end.

    Fixpoint insert_at_right (m i : t T) : t T :=
      match m with
        | MLeaf => i
        | MBranch l k v r =>
          MBranch _ l k v (insert_at_right r i)
      end.

    Fixpoint remove (s : nat) (m : t T) : t T :=
      match m with
        | MLeaf => m
        | MBranch l k v r =>
          match Compare_dec.lt_eq_lt_dec s k with
            | inleft (left _) => MBranch _ (remove s l) k v r
            | inleft (right _) => insert_at_right l r
            | inright _ => MBranch _ l k v (remove s r)
          end
      end.

    Lemma remove_add : forall m x v,
      remove x (add x v m) = remove x m.
    Proof.
      clear. induction m; simpl; intros.
      destruct (Compare_dec.lt_eq_lt_dec x x) as [ [ ? | ? ] | ? ]; auto; exfalso; omega.
      case_eq (Compare_dec.lt_eq_lt_dec x n); simpl. intro. case_eq s; simpl; intros; subst.
      rewrite H0. rewrite IHm1. auto.
      rewrite H0. auto.
      intros. rewrite H. rewrite IHm2. auto.
    Qed.

    Lemma find_add : forall m x v,
      find x (add x v m) = Some v.
    Proof.
      clear. induction m; simpl; intros.
      destruct (Compare_dec.lt_eq_lt_dec x x) as [ [ ? | ? ] | ? ]; auto; exfalso; omega.
      case_eq (Compare_dec.lt_eq_lt_dec x n); simpl. intro. case_eq s; simpl; intros; subst.
      rewrite H0. auto.
      rewrite H0. auto.
      intros. rewrite H. auto.
    Qed.

  End parametric.
    
  Section Map.
    Context {T U : Type}.
    Variable f : nat -> T -> U.

    Fixpoint map (m : t T) : t U :=
      match m with
        | MLeaf => MLeaf _
        | MBranch l k v r =>
          MBranch _ (map l) k (f k v) (map r)
      end.
  End Map.

  Section Fold.
    Context {T U : Type}.
    Variable f : nat -> T -> U -> U.

    Fixpoint fold (m : @t T) (acc : U) : U :=
      match m with
        | MLeaf => acc
        | MBranch l k v r =>
          fold r (f k v (fold l acc))
      end.
  End Fold.
  
End IntMap.
