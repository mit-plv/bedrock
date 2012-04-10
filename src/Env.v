Require Import List.
Require Import Decidables.

Set Implicit Arguments.
Set Strict Implicit.

(* Some tactics for automation of later proofs *)
Ltac caseDestruct t := destruct t; try solve [ simpl in *; discriminate ].

Ltac dintuition := repeat (intuition;
  match goal with
    | [ H : exists _, _ |- _ ] => destruct H
  end).

Ltac unlet := repeat match goal with
                       | [ x := ?y |- _ ] => subst x
                     end.

Ltac hypRewriter := repeat match goal with
                              | [ H : ?x = _ |- context [ ?x ] ] => rewrite H
                              | [ H1 : ?x = _, H2 : context [ ?x ] |- _ ] => rewrite H1 in H2
                            end.

Ltac loop := repeat (repeat (hypRewriter; autorewrite with provers in *); simpl in *; subst; dintuition).

Ltac provers := intuition; loop; unlet; loop; try congruence; firstorder.

(* null hint to initialize db *)
Hint Rewrite app_nil_l : provers.

Section UpdateAt.
  Variable A : Type.
  
  Variable new default : A.

  Fixpoint updateAt (ls : list A) (n : nat) : list A :=
    match n with
      | 0 => new :: tail ls
      | S n => match head ls with
                 | None => default
                 | Some v => v 
               end :: updateAt (tail ls) n
    end.

  Definition defaulted (ls : list A) (n : nat) (n' : nat) : option A :=
    match Compare_dec.lt_eq_lt_dec n n' with
      | inleft (left _) => nth_error ls n'
      | inleft (right _) => Some new
      | inright _ => match nth_error ls n' with
                       | None => Some default
                       | Some v => Some v 
                     end
    end.

  Require Import Omega.
  Lemma nth_error_updateAt : forall n l,
    nth_error (updateAt l n) n = value new.
    induction n; destruct l; simpl; (reflexivity || apply IHn).
  Defined.
  
  Lemma nth_error_updateAt_not : forall old n' ls n,
    n <> n' ->
    nth_error ls n = Some old ->
    nth_error (updateAt ls n') n = Some old.
  Proof.
    induction n'; destruct ls; destruct n; simpl; intros; try solve [ discriminate | exfalso; auto | auto ].
  Qed.

  Lemma nth_error_updateAt_gt : forall n n' ls,
    n < n' ->
    nth_error (updateAt ls n) n' = nth_error ls n'.
  Proof.
    induction n; simpl; intros.
      destruct n'; destruct ls; simpl; intros; try solve [ auto | exfalso; omega | destruct n'; reflexivity ].

      destruct n'. exfalso; omega.
        destruct ls; simpl. rewrite IHn. destruct n'; auto. omega.
        apply IHn. omega.
  Defined.

  Lemma nth_error_updateAt_lt : forall n' n ls,
    n' < n ->
    nth_error (updateAt ls n) n' = 
      match nth_error ls n' with
        | None => Some default
        | Some v => Some v
      end.
  Proof.
    induction n'; simpl; intros.
      destruct n; [ exfalso; omega | ]. destruct ls; auto.
      destruct n; [ exfalso; omega | ]. destruct ls; simpl; rewrite IHn' by omega. destruct n'; auto.
      auto.
  Defined. 

  Theorem nth_error_updateAt_eq : forall n ls n',
    nth_error (updateAt ls n) n' = defaulted ls n n'.
  Proof.
    unfold defaulted; intros.
      destruct (lt_eq_lt_dec n n'). destruct s.
      eapply nth_error_updateAt_gt; auto.
      subst; eapply nth_error_updateAt; auto.
      eapply nth_error_updateAt_lt; auto.
  Defined.

  (** **)
  Fixpoint cast (P : option A -> Type) ls idx
    : P (nth_error (updateAt ls idx) idx) -> P (Some new) :=
    match idx with
      | O => match ls
             return P (nth_error (updateAt ls O) O) -> _ with
               | nil => fun x => x
               | _ => fun x => x
             end
      | S idx => 
        match ls return P (nth_error (updateAt ls (S idx)) (S idx)) -> _ with
          | nil => cast P nil idx
          | _ => cast P _ idx
        end
    end.

  Theorem cast_inj : forall P idx ls x y, cast P ls idx x = cast P ls idx y -> x = y.
  Proof.
    induction idx; destruct ls; simpl; intros; auto.
  Qed.

End UpdateAt.

Section UpdatePosition2.
  Variable A : Type.

  Hint Rewrite nth_error_updateAt : provers.
  Lemma nth_error_updateAt_2 : forall A (ls : list A) d d' a b m n, 
    m <> n ->
    nth_error (updateAt a d (updateAt b d' ls n) m) n = value b.
    induction ls; induction m; induction n; provers.
  Qed.
End UpdatePosition2.

Section MapRepr.
  Variable T : Type.
  Record Repr : Type :=
  { footprint : list (nat * T)
  ; default : T 
  }.

  Definition nil_Repr (d : T) : Repr :=
  {| footprint := nil
   ; default := d
   |}.

  Definition listToRepr (ls : list T) (d : T) : Repr :=
    {| footprint := 
      ((fix listToRepr ls cur : list (nat * T) :=
        match ls with
          | nil => nil
          | l :: ls => (cur, l) :: listToRepr ls (S cur)
        end) ls 0)
     ; default := d
     |}.

  Definition listOptToRepr (ls : list (option T)) (d : T) : Repr :=
    {| footprint := 
      ((fix listToRepr ls cur : list (nat * T) :=
        match ls with
          | nil => nil
          | Some l :: ls => (cur, l) :: listToRepr ls (S cur)
          | None :: ls => listToRepr ls (S cur)
        end) ls 0)
     ; default := d
     |}.

  Fixpoint repr' (d : T) (ls : list (nat * T)) : list T -> list T :=
    match ls with 
      | nil => fun x => x
      | (n, v) :: ls =>
        fun x => updateAt v d (repr' d ls x) n
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

  Definition repr (l : Repr) : list T -> list T :=
    match l with 
      | {| footprint := f ; default := d |} =>
        repr' d f
    end.

  Fixpoint repr_optimize (l : list (nat * T)) (ignore : list nat) : list (nat * T) :=
    match l with
      | nil => nil
      | (n,t) :: b => 
        if List.In_dec (equiv_dec) n ignore then 
          repr_optimize b ignore
        else 
          (n,t) :: repr_optimize b (n :: ignore)
    end.

  Definition repr_combine (l r : Repr) : Repr :=
    {| footprint := repr_optimize (footprint l ++ footprint r) nil
     ; default := default l
     |}.
  (** NOTE: that we don't have any lemmas for combination because we are
   ** relying on Ltac's dynamic types to do combinations
   **)

  Definition repr_get (l : Repr) (n : nat) : option T :=
    get n (footprint l).

End MapRepr.

