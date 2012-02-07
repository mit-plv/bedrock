Require Import List.

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
  
  Variable new : A.

  Fixpoint updateAt (ls : list A) (n : nat) : list A :=
    match ls with
      | nil => match n with
                 | 0 => new :: nil
                 | S n' => new :: updateAt nil n'
               end
      | a :: ls' => match n with
                      | 0 => new :: ls'
                      | S n' => a :: updateAt ls' n'
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
  Lemma nth_error_updateAt_nil : forall n,
    nth_error (updateAt nil n) n = value new.
    intros.
    induction n; auto.
  Qed.
  Lemma nth_error_updateAt : forall ls n, nth_error (updateAt ls n) n = value new.
    double induction ls n; auto.
    intros.
    specialize (H0 H).
    simpl.
    destruct l0; auto. apply nth_error_updateAt_nil; auto.
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
        | None => Some new
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
  Lemma nth_error_updateAt_2 : forall A (ls : list A) a b m n, m <> n -> nth_error (updateAt a (updateAt b ls n) m) n = value b.
    induction ls; induction m; induction n; provers.
  Qed.
End UpdatePosition2.

Section MapRepr.
  Variable T : Type.

  Fixpoint repr (ls : list (nat * T)) : list T -> list T :=
    match ls with 
      | nil => fun x => x
      | (n, v) :: ls =>
        fun x => updateAt v (repr ls x) n
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
    inversion H; clear H; subst. eapply nth_error_updateAt.
    
    erewrite nth_error_updateAt_not; auto.
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

  Definition nth_error_repr (r : list (nat * T)) (ls : list T) (n : nat) 
    : option T :=
    match get n r with
      | Some v => Some v
      | None => match nth_error ls n with
                  | Some v => Some v 
                  | None => defaulted_repr r n 
                end
    end.

  Theorem repr_get_eq : forall r ls n,
    nth_error (repr r ls) n = nth_error_repr r ls n.
  Proof.
    unfold nth_error_repr.
    induction r; simpl; intros.
      destruct (nth_error ls n); reflexivity.

      destruct a.
        rewrite nth_error_updateAt_eq. unfold defaulted.
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

   (** cast **)
   Section CastRepr.
     Variable P : option T -> Type.

     Fixpoint cast_repr d ls idx {struct d}
       : P (nth_error (repr d ls) idx) -> P (match get idx d with
                                               | Some v => Some v
                                               | None => match nth_error ls idx with
                                                           | Some v => Some v 
                                                           | None => defaulted_repr d idx
                                                         end
                                             end).
     rewrite repr_get_eq. auto. 

(* This does reduce, but it might be better to code manually... 
     refine (match d as d
               return 
               P (nth_error (repr d ls) idx) -> P (match get idx d with
                                                     | Some v => Some v
                                                     | None => match nth_error ls idx with
                                                                 | Some v => Some v 
                                                                 | None => defaulted_repr d idx
                                                               end
                                                   end)
               with
               | nil => match nth_error (repr nil ls) idx as k return P k -> P match k with 
                                                                                 | Some v => Some v
                                                                                 | None => None
                                                                               end
                          with
                            | None => fun x => x
                            | _ => fun x => x 
                        end
               | (i,v) :: ds => _
             end).
     simpl.
     refine (match eq_nat_dec idx i as k return 
               P (nth_error (updateAt v (repr ds ls) i) idx) ->
               P match (if k then Some v else get idx ds) with
                   | Some v0 => Some v0
                   | None =>
                     match nth_error ls idx with
                       | Some v0 => Some v0
                       | None =>
                         match defaulted_repr ds idx with
                           | Some v0 => if k then Some v else Some v0
                           | None => if le_lt_dec idx i then Some v else None
                         end
                     end
                 end
               with
               | left pf => match pf in _ = k return P (nth_error (updateAt v (repr ds ls) k) idx) -> P (Some v) with 
                              | refl_equal => cast _ _ _ _
                            end
               | right _ => _ 
             end).
     specialize (cast_repr ds idx (repr ds ls)).
     refine (match get idx ds as k return 
               P (nth_error (updateAt v (repr ds ls) i) idx) ->
               P match k with
                   | Some v0 => Some v0
                   | None =>
                     match nth_error ls idx with
                       | Some v0 => Some v0
                       | None =>
                         match defaulted_repr ds idx with
                           | Some v0 => Some v0
                           | None => if le_lt_dec idx i then Some v else None
                         end
                     end
                 end
               with
               | Some v0 => _
               | None => _ 
             end).

     ).


     refine (match d as d return 

   rewrite repr_get_eq. trivial.
     match idx with
       | O => match ls
                return P (nth_error (updateAt ls O) O) -> _ with
                | nil => fun x => x
                | _ => fun x => x
              end
       | S idx => 
         match ls return P (nth_error (updateAt ls (S idx)) (S idx)) -> _ with
           | nil => cast P idx nil
           | _ => cast P idx _
         end
     end.
*)
     Defined.
     
     Theorem cast_repr_inj : forall d idx ls x y, cast_repr d ls idx x = cast_repr d ls idx y -> x = y.
     Proof.
     Admitted.
   End CastRepr.

End MapRepr.

(** Specializations for exprD **)
Section UpdateAt_exprD.
  Require Import Expr.
  
  Variable types' : list type.
  Variable deltaT : list (nat * type).
  Definition types := repr deltaT types'.
  Variable funcs : functions types.

  Variable uvars vars : env types.

(*
  Definition exprD_repr (e : expr types) idx
    : option match match get idx deltaT with
                     | Some v => Some v
                     | None => match nth_error types' idx with
                                 | Some v => Some v 
                                 | None => defaulted_repr deltaT idx 
                               end
                   end
               with
               | None => Empty_set
               | Some v => Impl v
             end :=
    let res := exprD funcs uvars vars e (tvType idx) in
    @cast_repr _ (fun x => option match x with
                                    | Some t => Impl t 
                                    | None => Empty_set
                                  end) deltaT types' idx res.
*)

(*
  Definition cast_tvar new ls idx
    : tvarD (updateAt new ls idx) (tvType idx) -> Impl new :=
    @cast _ new (fun x => match x with 
                          | Some t => Impl t
                          | None => Empty_set
                        end) _ _.

  Definition cast_repr_tvar d ls idx
    : tvarD (repr d ls) (tvType idx) -> match get idx d with
                                          | Some v => Impl v
                                          | None => match nth_error ls idx with
                                                      | Some v => Impl v 
                                                      | None => match defaulted_repr d idx with
                                                                  | None => Empty_set
                                                                  | Some v => Impl v 
                                                                end
                                                    end
                                        end.
  Check cast_repr.
  intro.
  pose (@cast_repr _ (fun x => match x with 
                          | Some t => Impl t
                          | None => Empty_set
                        end) d ls idx X). simpl in *.
  Admitted.
*)

End UpdateAt_exprD.
