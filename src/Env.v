Require Import List Eqdep_dec.

Set Implicit Arguments.

Section fin.
  Variable A : Type.
  
  Inductive fin : list A -> Type :=
  | FO : forall x ls, fin (x :: ls)
  | FS : forall x ls, fin ls -> fin (x :: ls).

  Fixpoint lift (ls : list A) e : fin ls -> fin (e ++ ls) :=
    match e as e return fin ls -> fin (e ++ ls) with
      | nil => fun x => x
      | a :: b => fun x => FS a (@lift ls b x)
    end.

  Definition finOut ls (f : fin ls) : match ls return fin ls -> Type with
                                        | nil => fun _ => Empty_set
                                        | _ => fun f => {f' : _ | f = FS _ f'} + {f = FO _ _}
                                      end f :=
  match f with
    | FO _ _ => inright _ (refl_equal _)
    | FS _ _ f' => inleft _ (exist _ f' (refl_equal _))
  end.

  Definition finIfz t (ls : list A) (d : fin (t :: ls))
    : forall (R : fin (t :: ls) -> Type) (h : R (@FO _ _)) (n : forall c, R (@FS _ _ c)), 
    R d :=
    match d as d' in fin ls' return match ls' return fin ls' -> Type with 
                                | nil => fun _ => Empty_set
                                | a :: b => fun d => 
                                  forall (R : fin (a :: b) -> Type) (h : R (@FO _ _)) (n : forall c, R (@FS _ _ c)), R d
                              end d'
      with
      | FO _ _ => fun _ h _ => h
      | FS _ _ x => fun _ _ f => f x
    end.

  Definition finArg ls (f : fin ls) : option (fin (tl ls)) :=
    match f with
      | FO _ _ => None
      | FS _ _ f' => Some f'
    end.

  Lemma fin_inj : forall z ls (x y : fin ls),
    x <> y
    -> FS z x <> FS z y.
    red; intros.
    assert (finArg (FS z x) = finArg (FS z y)) by congruence.
    simpl in *; congruence.
  Qed.

  Hint Immediate fin_inj.

  Definition finEq : forall ls (x y : fin ls), {x = y} + {x <> y}.
    refine (fix finEq ls : forall x y : fin ls, {x = y} + {x <> y} :=
      match ls return forall x y : fin ls, {x = y} + {x <> y} with
        | nil => fun x _ => match finOut x with end
        | _ :: _ => fun x y => match finOut x, finOut y with
                                 | inleft (exist x' _), inleft (exist y' _) => if finEq _ x' y' then left _ _ else right _ _
                                 | inright _, inright _ => left _ _
                                 | _, _ => right _ _
                               end
      end); clear finEq; (subst; auto; try congruence;
        match goal with
          | [ H : sig _ |- _ ] => destruct H
        end; subst; discriminate).
  Defined.

  Fixpoint get (ls : list A) : fin ls -> A :=
    match ls return fin ls -> A with
      | nil => fun f => match f in fin N return match N with
                                                  | nil => A
                                                  | _ => unit
                                                end with
                          | FO _ _ => tt
                          | FS _ _ _ => tt
                        end
      | x :: ls' => fun f => match f in fin N return match N with
                                                       | nil => Empty_set
                                                       | _ :: ls' => (fin ls' -> A) -> A
                                                     end with
                               | FO _ _ => fun _ => x
                               | FS _ _ f' => fun get_ls' => get_ls' f'
                             end (@get ls')
    end.

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

  Fixpoint hlist_get (ls : list A) (i : fin ls) : hlist ls -> B (get i) :=
    match i in fin ls return hlist ls -> B (get i) with
      | FO _ _ => fun hl => hlist_hd hl
      | FS _ _ f' => fun hl => hlist_get f' (hlist_tl hl)
    end.

  Fixpoint absAll (ls : list A) :
    (hlist ls -> Type) -> Type :=
    match ls return (hlist ls -> Type) -> Type with
      | nil => fun R => R (HNil)
      | a :: b => fun R =>
        forall x : B a, absAll (fun y => R (HCons x y))
    end.

  Fixpoint hlistDestruct (ls : list A) (args : hlist ls) {struct args}
    : forall K : hlist ls -> Type, absAll K -> K args :=
      match
        args as args0 in hlist ls0
          return (forall K : hlist ls0 -> Type, absAll K -> K args0)
        with
        | HNil =>
          fun (K : hlist nil -> Type) (cc : absAll K) => cc
        | HCons x0 ls0 x args =>
          fun (K : hlist (x0 :: ls0) -> Type) (cc : absAll K) =>
            hlistDestruct args
            (fun y : hlist ls0 => K (HCons x y)) 
            (cc x)
      end.

End fin.

Implicit Arguments FO [A x ls].
Implicit Arguments FS [A x ls].
Implicit Arguments finIfz [A t ls].

Implicit Arguments get [A].
Implicit Arguments HNil [A B].
Implicit Arguments HCons [A B x ls].
