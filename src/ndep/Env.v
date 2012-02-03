Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

Section UpdatePosition.
  Variable A : Type.
  
  Variable new : A.

  Fixpoint updatePosition (ls : list A) (n : nat) : list A :=
    match ls with
      | nil => match n with
                 | 0 => new :: nil
                 | S n' => new :: updatePosition nil n'
               end
      | a :: ls' => match n with
                      | 0 => new :: ls'
                      | S n' => a :: updatePosition ls' n'
                    end
    end.

  Definition defaulted (ls : list A) (n : nat) (n' : nat) : option A :=
    match Compare_dec.lt_eq_lt_dec n n' with
      | inleft (left _) => nth_error ls n'
      | inleft (right _) => Some new
      | inright _ => match nth_error ls n' with
                       | None => Some new
                       | Some v => Some v 
                     end
    end.

  Require Import Omega.
  Lemma nth_error_updatePosition_nil : forall n,
    nth_error (updatePosition nil n) n = value new.
    intros.
    induction n; auto.
  Qed.
  Lemma nth_error_updatePosition : forall ls n, nth_error (updatePosition ls n) n = value new.
    double induction ls n; auto.
    intros.
    specialize (H0 H).
    simpl.
    destruct l0; auto. apply nth_error_updatePosition_nil; auto.
  Defined.
  
  Lemma nth_error_updatePosition_not : forall old n' ls n,
    n <> n' ->
    nth_error ls n = Some old ->
    nth_error (updatePosition ls n') n = Some old.
  Proof.
    induction n'; destruct ls; destruct n; simpl; intros; try solve [ discriminate | exfalso; auto | auto ].
  Qed.

  Lemma nth_error_updatePosition_gt : forall n n' ls,
    n < n' ->
    nth_error (updatePosition ls n) n' = nth_error ls n'.
  Proof.
    induction n; simpl; intros.
      destruct n'; destruct ls; simpl; intros; try solve [ auto | exfalso; omega | destruct n'; reflexivity ].

      destruct n'. exfalso; omega.
        destruct ls; simpl. rewrite IHn. destruct n'; auto. omega.
        apply IHn. omega.
  Defined.

  Lemma nth_error_updatePosition_lt : forall n' n ls,
    n' < n ->
    nth_error (updatePosition ls n) n' = 
      match nth_error ls n' with
        | None => Some new
        | Some v => Some v
      end.
  Proof.
    induction n'; simpl; intros.
      destruct n; [ exfalso; omega | ]. destruct ls; auto.
      destruct n; [ exfalso; omega | ]. destruct ls; simpl; rewrite IHn' by omega. destruct n'; auto.
      auto.
  Defined. 

  Theorem nth_error_updatePosition_eq : forall n ls n',
    nth_error (updatePosition ls n) n' = defaulted ls n n'.
  Proof.
    unfold defaulted; intros.
      destruct (lt_eq_lt_dec n n'). destruct s.
      eapply nth_error_updatePosition_gt; auto.
      subst; eapply nth_error_updatePosition; auto.
      eapply nth_error_updatePosition_lt; auto.
  Defined.

End UpdatePosition.

Section MapRepr.
  Variable T : Type.

  Fixpoint repr (ls : list (nat * T)) : list T -> list T :=
    match ls with 
      | nil => fun x => x
      | (n, v) :: ls =>
        fun x => updatePosition v (repr ls x) n
    end.

  Section get.
    Variable n : nat.
    
    Fixpoint get (ls : list (nat * T)) : option T :=
      match ls with
        | nil => None
        | (n',v) :: ls => 
          if Peano_dec.eq_nat_dec n n' then Some v else get ls
      end.
  End get.

  (** This is probably not necessary **)
(*
  Theorem repr_get : forall r ls n v,
    get n r = Some v ->
    nth_error (repr r ls) n = Some v.
  Proof.
    induction r; simpl.
      congruence.
    intros. destruct a. destruct (Peano_dec.eq_nat_dec n n0).
    inversion H; clear H; subst. eapply nth_error_updatePosition.
    
    erewrite nth_error_updatePosition_not; auto.
  Defined.
*)

  Fixpoint defaulted_repr (r : list (nat * T)) (n : nat) : option T :=
    match r with
      | nil => None
      | (a,b) :: r =>
        match defaulted_repr r n with
          | None => if le_lt_dec n a then Some b else None
          | Some v => if eq_nat_dec n a then Some b else Some v 
        end
    end.

  Theorem repr_get_eq : forall r ls n,
    nth_error (repr r ls) n = 
    match get n r with
      | Some v => Some v
      | None => match nth_error ls n with
                  | Some v => Some v 
                  | None => defaulted_repr r n 
                end
    end.
  Proof.
    induction r; simpl; intros.
      destruct (nth_error ls n); reflexivity.

      destruct a.
        rewrite nth_error_updatePosition_eq. unfold defaulted.
        destruct (lt_eq_lt_dec n0 n). destruct s.
          destruct (eq_nat_dec n n0); [ exfalso; omega | ].
          rewrite IHr. destruct (get n r); auto. destruct (nth_error ls n); auto.
          destruct (defaulted_repr r n); auto. destruct (le_lt_dec n n0); try solve [ exfalso; omega ]; auto.

        destruct (eq_nat_dec n n0); [ | exfalso; omega ]; auto.

        destruct (eq_nat_dec n n0); [ exfalso; omega | ].
          rewrite IHr. destruct (get n r); auto. destruct (nth_error ls n); auto.
          destruct (defaulted_repr r n); auto. destruct (le_lt_dec n n0); auto. exfalso; omega.
   Defined.

   (** And all of this simplifies... **)
   Goal forall t u : T, 
     match repr_get_eq ((0, u) :: nil) (t :: nil) 0 return Prop with
       | refl_equal => True 
     end.
     intros. simpl. trivial.
   Qed.

End MapRepr.

(*
  Variable dT : nat -> Type.
  Variable F : nat -> forall x, option (dT x).

  Definition ls := ((bool : Type) :: (nat : Type) :: (unit : Type) :: nil).

  Eval simpl in nth_error (repr ((0, nat:Type) :: nil) ls) 0.

  Definition F_nat (n : nat) : option nat :=
    match @repr_get _ ((0,nat : Type) :: nil) ls 0 nat (refl_equal _) in _ = k return match k with 
                                                                                        | Some T => option T
                                                                                        | None => unit 
                                                                                      end with
      | refl_equal => F n 0
    end.

End MapRepr.
  Parameter dT : nat -> Type.

  Parameter denote : nat -> forall x, option (dT x).

  Hypothesis PF : dT 0 = nat.

  Definition denote_nat (x : nat) : option nat :=
    match repr_get _ _ _ _ _  in _ = k return option k with
      | refl_equal => denote x 0
    end.



  Goal True. 
    pose (match match PF in _ = k return option k with | refl_equal => denote 0 0 end 
            with
              | None => False
            | Some x => x = 0
          end).
    Set Printing All.
    Print PF.


  Print eq_refl.

  @repr_get a b c d pf = refl_equal .

  Lemma repr_get_pf_refl_equal : forall (T : option T -> Type) (F : forall x, T x -> U) a b c d pf,
    ...
    match @repr_get a b c d pf in _ = k return T k with
      | refl_equal => ...
    end
    ...
*)