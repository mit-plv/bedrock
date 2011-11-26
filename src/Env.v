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

  Require Import EquivDec.
  Global Instance finEq_dec ls : EqDec (fin ls) (@eq (fin ls)) :=
    @finEq ls.

  Inductive dcomp T (a b : T) : Type :=
  | Lt | Gt | Eq : a = b -> dcomp a b.
  
  Definition dcomp_option T (a b : T) (d : dcomp a b) : option (a = b) :=
    match d with
      | Eq pf => Some pf
      | _ => None
    end.

  Fixpoint finCmp ls (x : fin ls) : forall y : fin ls, dcomp x y :=
    match x in fin ls return forall y : fin ls, dcomp x y with
      | FO a b => fun y : fin (a :: b) =>
        @finIfz _ _ y (dcomp (FO a b)) (Eq (refl_equal _)) (fun _ => Lt _ _)
      | FS a ls r => fun y : fin (a :: ls) =>
        @finIfz _ _ y (dcomp (FS a r)) (Gt _ _) 
          (fun r' => match finCmp r r' with
                       | Eq pf => Eq (match pf in _ = t return FS a r = FS a t with
                                        | refl_equal => refl_equal _
                                      end)
                                          
                       | Gt => Gt _ _
                       | Lt => Lt _ _ 
                     end)
    end.

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

  Fixpoint liftD (ls : list A) e : forall i : fin ls, { x : fin (e ++ ls) & get x = get i } :=
    match e as e return forall i : fin ls, { x : fin (e ++ ls) & get x = get i } with
      | nil => fun x => existT _ x (refl_equal _)
      | a :: b => fun x => 
        match @liftD ls b x with
          | existT x pf => 
            existT _ (FS a x) (match pf in _ = t
                                 return get (FS a x) = t with
                                 | refl_equal => refl_equal _
                               end)
        end
    end.

  Fixpoint pf_list_simpl A b c (a : list A) : (a ++ b :: nil) ++ c = a ++ b :: c :=
    match a as a return (a ++ b :: nil) ++ c = a ++ b :: c with
      | nil => refl_equal (nil ++ b :: nil ++ c)
      | a' :: b' => match eq_sym (@pf_list_simpl A b c b') in _ = t return a' :: t = a' :: b' ++ b :: c 
                      with
                      | refl_equal => refl_equal _
                    end
    end.

  Definition liftDmid (ls ls' : list A) e (i : fin (ls' ++ ls)) : 
    { x : fin (ls' ++ e ++ ls) & get x = get i }.
  refine ((fix liftDmid (ls'' ls ls' ls''': list A) e : forall (i : fin ls'''),
    ls' ++ ls = ls''' ->
    (forall y : { i' : fin (ls' ++ e ++ ls) &  get i' = get i },
       { x : fin (ls'' ++ ls' ++ e ++ ls) & get x = get i }) ->
    { x : fin (ls'' ++ ls' ++ e ++ ls) & get x = get i } :=
    match ls' as ls' return 
      forall (i : fin ls'''),
        ls' ++ ls = ls''' ->
        (forall y : { i' : fin (ls' ++ e ++ ls) &  get i' = get i },
       { x : fin (ls'' ++ ls' ++ e ++ ls) & get x = get i }) ->
        { x : fin (ls'' ++ ls' ++ e ++ ls) & get x = get i }
      with
      | nil => fun (i : fin ls''') (pf : ls = ls''') =>
        match eq_sym pf in _ = t 
          return ({i' : fin (nil ++ e ++ t) & get i' = get i} ->
            {x : fin (ls'' ++ nil ++ e ++ t) & get x = get i}) ->
          {x : fin (ls'' ++ nil ++ e ++ t) & get x = get i}
          with 
          | refl_equal => fun cc => cc (liftD e i)
        end
      | a :: b => fun i =>
        match i as i in fin ls''' return 
          (a :: b) ++ ls = ls''' ->
          ({i' : fin ((a :: b) ++ e ++ ls) & get i' = get i} ->
            {x : fin (ls'' ++ (a :: b) ++ e ++ ls) & get x = get i}) ->
          {x : fin (ls'' ++ (a :: b) ++ e ++ ls) & get x = get i}
          with 
          | FO x _ => fun pf cc =>
            cc (@existT _ _ (FO _ _) match pf in _ = t return match t with
                                                                | nil => Empty_set
                                                                | x :: _ => a = x
                                                              end
                                       with
                                       | refl_equal => refl_equal _
                                     end)
            
          | FS _ LX f => fun pf cc => 
            match pf_list_simpl a (b ++ e ++ ls) ls'' in _ = t
              return 
              ({i' : fin (b ++ e ++ ls) & get i' = get f} ->
                {x : fin t & get x = get f}) ->
              {x : fin t & get x = get f}
              with
              | refl_equal => 
                @liftDmid (ls'' ++ a :: nil) ls b LX e f 
                match pf in _ = t return
                  match t with
                    | nil => Empty_set 
                    | a' :: b' => b ++ ls = b'
                  end
                  with
                  | refl_equal => refl_equal _
                end
            end
            (fun z => match z with
                        | existT v pf => cc (@existT _ _ (FS a v) pf)
                      end)
        end
    end
    ) nil ls ls' (ls' ++ ls) e i (refl_equal _) (fun i' => i')).
  Defined.
  
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

  Fixpoint hlist_app ll lr : hlist ll -> hlist lr -> hlist (ll ++ lr) :=
    match ll with
      | nil => fun _ x => x
      | _ :: _ => fun l r => HCons (hlist_hd l) (hlist_app (hlist_tl l) r)
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


  Variable cmp : forall x (y z : B x), dcomp y z.
  Definition hlistCmp : forall x (y z : hlist x), dcomp y z.
    refine (fix hlistCmp x (y : hlist x) : forall z : hlist x, dcomp y z :=
      match y in hlist x return forall z : hlist x, dcomp y z with
        | HNil => fun z => match z in hlist x return match x return hlist x -> Type with
                                                       | nil => fun z => dcomp HNil z
                                                       | _ => fun _ => unit
                                                     end z with
                             | HNil => Eq _
                             | _ => tt
                           end
        | HCons _ _ v1 y' => fun z => match z in hlist x return match x return hlist x -> Type with
                                                                  | nil => fun _ => unit
                                                                  | t :: x' => fun z => forall (v1 : B t) (y' : hlist x'),
                                                                    (forall v2, dcomp v1 v2)
                                                                    -> (forall z', dcomp y' z')
                                                                    -> dcomp (HCons v1 y') z
                                                                end z with
                                        | HNil => tt
                                        | HCons _ _ v2 z' => fun v1 _ cmp' self => 
                                          match cmp' v2 with
                                            | Eq _ => 
                                              match self z' with
                                                | Gt => Gt _ _ 
                                                | Lt => Lt _ _ 
                                                | Eq _ => Eq _
                                              end
                                            | Gt => Gt _ _
                                            | Lt => Lt _ _
                                          end
                                      end v1 y' (cmp v1) (hlistCmp _ y')
      end); clear hlistCmp; abstract congruence.
  Defined.

  Fixpoint hlist_get (ls : list A) (i : fin ls) : hlist ls -> B (get i) :=
    match i in fin ls return hlist ls -> B (get i) with
      | FO _ _ => fun hl => hlist_hd hl
      | FS _ _ f' => fun hl => hlist_get f' (hlist_tl hl)
    end.

(*
  Theorem hlist_get_lift : forall ls ls' ls'' (f : fin (ls ++ ls'')) G G' G'',
    hlist_get f (hlist_app G G'') = match liftDmid ls'' ls ls' f with
                                      | existT f' pf =>
                                        match pf in _ = t return B t with
                                          | refl_equal => 
                                            hlist_get f' (hlist_app G (hlist_app G' G''))
                                        end
                                    end.
  Proof.
    induction ls. simpl. intros. unfold liftDmid; simpl.

    clear. induction ls; induction ls'; simpl; intros.
      reflexivity.
      unfold liftDmid. simpl. remember (@nil A) as ZZ. destruct G. 2: inversion HeqZZ.
      simpl in *. erewrite IHls'. 2: econstructor. unfold liftDmid. simpl.
      case_eq (liftD ls' f). instantiate (1 := (hlist_tl G')).
      simpl. intros. admit.
      unfold liftDmid in *. simpl in *. 
*)
      


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

Section hlist_map.
  Variable A : Type.
  Variable F : A -> Type.
  Variable G : A -> Type.
  Variable ff : forall x, F x -> G x.

  Fixpoint hlist_map (ls : list A) (hl : hlist F ls) {struct hl} : hlist G ls :=
    match hl in @hlist _ _ ls return hlist G ls with
      | HNil => HNil
      | HCons _ _ hd tl => 
        HCons (ff hd) (hlist_map tl)
    end.
End hlist_map.

Section hlist_fold2.
  Variables T U V : Type. 
  Variables F G : T -> Type. 
  Variable f : U -> forall t : T, F t -> G t -> U.

  Fixpoint hlist_fold2 ls (l : hlist F ls) {struct l} : hlist G ls -> U -> U :=
    match l in hlist _ ls 
      return hlist G ls -> U -> U
      with
      | HNil => fun _ acc => acc
      | HCons _ _ fr hr => fun r acc =>
        hlist_fold2 hr (hlist_tl r) (f acc fr (hlist_hd r))
    end. 
End hlist_fold2.