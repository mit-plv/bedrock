Require Import List Eqdep_dec.

Set Implicit Arguments.

Inductive fin : nat -> Type :=
| FO : forall n, fin (S n)
| FS : forall n, fin n -> fin (S n).

Definition finOut n (f : fin n) : match n return fin n -> Type with
                                    | O => fun _ => Empty_set
                                    | S n' => fun f => {f' : _ | f = FS f'} + {f = FO _}
                                  end f :=
  match f with
    | FO _ => inright _ (refl_equal _)
    | FS _ f' => inleft _ (exist _ f' (refl_equal _))
  end.

Definition finArg n (f : fin n) : option (fin (pred n)) :=
  match f with
    | FO _ => None
    | FS _ f' => Some f'
  end.

Lemma fin_inj : forall n (x y : fin n),
  x <> y
  -> FS x <> FS y.
  red; intros.
  assert (finArg (FS x) = finArg (FS y)) by congruence.
  simpl in *; congruence.
Qed.

Hint Immediate fin_inj.

Definition finEq : forall n (x y : fin n), {x = y} + {x <> y}.
  refine (fix finEq n : forall x y : fin n, {x = y} + {x <> y} :=
    match n return forall x y : fin n, {x = y} + {x <> y} with
      | O => fun x _ => match finOut x with end
      | S n' => fun x y => match finOut x, finOut y with
                             | inleft (exist x' _), inleft (exist y' _) => if finEq _ x' y' then left _ _ else right _ _
                             | inright _, inright _ => left _ _
                             | _, _ => right _ _
                           end
    end); clear finEq; abstract (subst; auto; try congruence;
      match goal with
        | [ H : sig _ |- _ ] => destruct H
      end; subst; discriminate).
Defined.

Section get.
  Variable A : Type.

  Fixpoint get (ls : list A) : fin (length ls) -> A :=
    match ls return fin (length ls) -> A with
      | nil => fun f => match f in fin N return match N with
                                                  | O => A
                                                  | _ => unit
                                                end with
                          | FO _ => tt
                          | FS _ _ => tt
                        end
      | x :: ls' => fun f => match f in fin N return match N with
                                                       | O => Empty_set
                                                       | S N' => (fin N' -> A) -> A
                                                     end with
                               | FO _ => fun _ => x
                               | FS _ f' => fun get_ls' => get_ls' f'
                             end (get ls')
    end.
End get.

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall x ls, B x -> hlist ls -> hlist (x :: ls).

  Definition hlist_hd (T : A) (ls : list A) (v : hlist (T :: ls)) : B T :=
    match v in hlist ls return match ls with
                                 | nil => unit
                                 | a :: _ => B a
                               end with
      | HNil => tt
      | HCons _ _ x _ => x 
    end.

  Definition hlist_tl (T : A) (ls : list A) (v : hlist (T :: ls)) : hlist ls :=
    match v in hlist ls return match ls with
                                 | nil => unit
                                 | _ :: ls => hlist ls
                               end with
      | HNil => tt
      | HCons _ _ _ x => x 
    end.

  Variable dec : forall x (y z : B x), option (y = z).

  Definition hlistEq : forall x (y z : hlist x), option (y = z).
    refine (fix hlistEq x (y : hlist x) : forall z : hlist x, option (y = z) :=
      match y in hlist x return forall z : hlist x, option (y = z) with
        | HNil => fun z => match z in hlist x return match x return hlist x -> Type with
                                                       | nil => fun z => option (HNil = z)
                                                       | _ => fun _ => unit
                                                     end z with
                             | HNil => Some _
                             | _ => tt
                           end
        | HCons _ _ v1 y' => fun z => match z in hlist x return match x return hlist x -> Type with
                                                                  | nil => fun _ => unit
                                                                  | t :: x' => fun z => forall (v1 : B t) (y' : hlist x'),
                                                                    (forall v2, option (v1 = v2))
                                                                    -> (forall z', option (y' = z'))
                                                                    -> option (HCons v1 y' = z)
                                                                end z with
                                        | HNil => tt
                                        | HCons _ _ v2 z' => fun v1 _ dec' self => if dec' v2 then if self z' then Some _ else None else None
                                      end v1 y' (dec v1) (hlistEq _ y')
      end); clear hlistEq; abstract congruence.
  Defined.

  Definition hlist_get : forall (ls : list A) (i : fin (length ls)) (h : hlist ls), B (get ls i).
  refine (fix hlist_get (ls : list A) : forall (i : fin (length ls)), hlist ls -> B (get ls i) :=
    match ls as ls return forall (i : fin (length ls)), hlist ls -> B (get ls i) with
      | nil => fun f _ => 
        match f as _ in fin N return match N with 
                                       | 0 => B (get nil f)
                                       | _ => unit
                                     end with
          | FO _ => tt
          | FS _ _ => tt
        end
      | x :: ls' => fun f : fin (length (x :: ls')) => _
(*
        fun z =>
        match f as f' in fin N return match N with 
                                            | 0 => Empty_set
                                            | S N' => forall Heq : N = length (x :: ls'), B x -> hlist ls' -> B (get (x :: ls') match Heq in _ = T return fin T with
                                                                                                                                  | refl_equal => f'
                                                                                                                                end)
                                          end with
          | FO _ => _
          | FS _ _ => _ 
        end _ _ _
*)
    end).
  Require Import Program.
  dependent destruction f. inversion 1. assumption.
  inversion 1. simpl. eapply hlist_get. assumption.
Defined.

End hlist.

Implicit Arguments HNil [A B].
Implicit Arguments HCons [A B x ls].