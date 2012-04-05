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
  { footprint : list (list (nat * T))
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
        end) ls 0) :: nil
     ; default := d
     |}.

  Definition listOptToRepr (ls : list (option T)) (d : T) : Repr :=
    {| footprint := 
      ((fix listToRepr ls cur : list (nat * T) :=
        match ls with
          | nil => nil
          | Some l :: ls => (cur, l) :: listToRepr ls (S cur)
          | None :: ls => listToRepr ls (S cur)
        end) ls 0) :: nil
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

  Fixpoint repr_compatible' (l r : list (nat * T)) : Prop :=
    match l with 
      | nil => True
      | (n, v) :: l =>
        v = match get n r with
              | None => v 
              | Some v' => v'
            end
        /\ repr_compatible' l r
    end.

  Definition repr_compatible (l r : Repr) : Prop :=
    repr_compatible' 
      (fold_right (@app _) nil (footprint l))
      (fold_right (@app _) nil (footprint r))
    /\ default l = default r.
(*
  Fixpoint repr_combine' (l r : list (nat * T)) : list (nat * T) :=
    {| footprint := footprint l ++ footprint r
     ; default := default l
l ++ 
    let l_img := List.map (@fst _ _) l in
    List.filter (fun i => if In_dec (Peano_dec.eq_nat_dec) (fst i) l_img then true else false) r.

  Fixpoint merge (l r : list (nat * T)) :=
    match l with
      | nil => r 
      | (n, v) :: l =>
        match get n r with
          | None => (n, v) :: merge l r
          | Some _ => merge l r 
        end
    end.
*)

  Definition repr (l : Repr) : list T -> list T :=
    fun v => fold_right (repr' (default l)) v (footprint l).

  Definition repr_combine (l r : Repr) : Repr :=
    {| footprint := footprint l ++ footprint r
     ; default := default l
     |}.
(*
  Lemma compatible_perm : forall (l r : Repr) x,
    repr_compatible l r ->
    repr (repr_combine l r) x = repr (repr_combine r l) x.
  Proof.
    destruct l; destruct r; unfold repr_compatible, repr_combine, repr; simpl.
    induction footprint0. simpl. rewrite app_nil_r. intuition; subst; auto.
    
    simpl. intros.
    destruct H.
  Admitted.
*)

  Definition repr_get (l : Repr) (n : nat) : option T :=
    (fix find xs :=
      match xs with
        | nil => None
        | x :: xs => match get n x with 
                       | None => find xs
                       | x => x
                     end
      end) (footprint l).
(*
  (** This is probably not necessary **)
  Theorem repr_get_rw : forall r ls d n v,
    get n r = Some v ->
    nth_error (repr' d r ls) n = Some v.
  Proof.
    induction r; simpl.
      congruence.
    intros. destruct a. destruct (Peano_dec.eq_nat_dec n n0).
    inversion H; clear H; subst. eapply nth_error_updateAt.
    
    erewrite nth_error_updateAt_not; auto.
  Defined.
*)

(*
  Definition cast_pf : forall r n ls,
    match repr_get r n with 
      | Some v =>
        nth_error (repr r ls) n = Some v
      | _ => True
    end.
  Proof.
    unfold repr_get. intros.
    destruct r. unfold repr. simpl in *.
    induction (footprint r); trivial.
    case_eq (get n a).
    intros. unfold repr. eapply repr_get_rw in H. assumption.
  Defined.
*)
(**
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
      | None => nth_error (repr r ls) n
    end.

  Theorem repr_get_eq : forall r ls n,
    nth_error (repr r ls) n = nth_error_repr r ls n.
  Proof.
    unfold nth_error_repr.
    induction r; simpl; intros.
      reflexivity.

      destruct a.
        rewrite nth_error_updateAt_eq. unfold defaulted.
        destruct (lt_eq_lt_dec n0 n). destruct s.
          destruct (eq_nat_dec n n0); [ exfalso; omega | ]. eauto.
          destruct (eq_nat_dec n n0); auto; congruence.
        destruct (eq_nat_dec n n0); [ exfalso; omega | ]; auto.
        rewrite IHr. destruct (get n r); auto.
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
                                               | None => nth_error (repr d ls) idx
                                             end).
     intro. rewrite repr_get_eq in X. auto.
     Defined.
     
     Theorem cast_repr_inj : forall d idx ls x y, cast_repr d ls idx x = cast_repr d ls idx y -> x = y.
     Proof.
       induction d; simpl.
         auto.
     Admitted.
   End CastRepr.
**)

End MapRepr.

(*
Section Repr_exprD.
  Require Import Expr.

  Variable types' : list type.

  Section repr.
    Variable knowledge : Repr type.
    Variable funcs : functions (repr knowledge types').
    Variable uvars vars : env (repr knowledge types').    
 
(*   
    Lemma tvarD_repr_repr_get : forall idx,
      tvarD (repr knowledge types') (tvType idx) =
      match
        match repr_get knowledge idx with
          | Some v => Some v
          | None => nth_error (repr knowledge types') idx
        end
        with
        | Some v => Impl v
        | None => Empty_set
      end.
    Proof.
      clear. unfold repr. destruct knowledge. clear. unfold repr_get. simpl in *. induction footprint0; simpl in *; auto.
      destruct a. intros.

      destruct (eq_nat_dec idx n).
      subst. rewrite nth_error_updateAt. reflexivity.
        case_eq (get idx footprint0); intros; auto.
        erewrite nth_error_updateAt_not. 2: eassumption.
        reflexivity.
        
        erewrite repr_get_rw; [ reflexivity | eassumption ].
    Defined.

    Definition exprD_repr (e : expr (repr knowledge types')) (idx : nat)
      : option match match repr_get knowledge idx with
                       | Some v => Some v
                       | None => nth_error (repr knowledge types') idx
                     end
    (** NOTE: This [return Type] is NOT optional, it is necessary to make universes work out **)
                 return Type with 
                 | None => Empty_set
                 | Some v => Impl v
               end :=
      match tvarD_repr_repr_get idx in _ = T return option T with
        | refl_equal => exprD funcs uvars vars e (tvType idx)
      end.
  End repr.

  Definition k : Repr type :=
    {| footprint := (0, {| Impl := nat ; Eq := fun _ _ => None |}) :: nil
     ; default := {| Impl := Empty_set ; Eq := fun _ _ => None |} |}.

  Goal forall fs u v e,
    exprD (types := repr k types') fs u v e (tvType 0) = Some 0 ->
    match exprD_repr k fs u v e 0 with 
      | Some n => n = 0
      | None => False
    end.
    unfold exprD_repr. simpl. unfold eq_ind_r. unfold eq_ind. unfold eq_rect. simpl.
    intros. rewrite H. destruct types'; reflexivity.
  Qed.
*)
  End repr.
End Repr_exprD.
*)
(*
  Section updateAt.
    Variable idx : nat.
    Variable t d : type.
    Variable funcs : functions (updateAt t d types' idx).
    Variable uvars vars : env (updateAt t d types' idx).

    Definition exprD_update (e : expr (updateAt t d types' idx))
      : option (Impl t) :=
      let res := exprD funcs uvars vars e (tvType idx) in
      match res with
        | None => None
        | Some res => Some (@cast type t d  (fun x => match x with
                                                        | Some t => Impl t
                                                        | None => Empty_set
                                                      end) types' idx res)
      end.
  End updateAt.
*)

(*
(** Specializations for exprD **)
Section UpdateAt_exprD.
  Require Import Expr.

  Section repr.
    Variable deltaT : list (nat * type).
    Variable funcs : functions (repr deltaT types').
    Variable uvars vars : env (repr deltaT types').

    Definition exprD_repr (e : expr (repr deltaT types')) idx
      : option match match get idx deltaT with
                       | Some v => Some v
                       | None => nth_error (repr deltaT types') idx
                     end
    (** NOTE: This [return Type] is NOT optional, it is necessary to make universes work out **)
                 return Type with 
                 | None => Empty_set
                 | Some v => Impl v
               end :=
      let res := exprD funcs uvars vars e (tvType idx) in
      match res with
        | None => None
        | Some res =>
          Some (@cast_repr _ (fun x => match x with
                                         | Some t => Impl t 
                                         | None => Empty_set
                                       end) deltaT types' idx res)
      end.
  End repr.

  Section updateAt.
    Variable idx : nat.
    Variable t : type.
    Variable funcs : functions (updateAt t types' idx).
    Variable uvars vars : env (updateAt t types' idx).

    Definition exprD_update (e : expr (updateAt t types' idx))
      : option (Impl t) :=
      let res := exprD funcs uvars vars e (tvType idx) in
      match res with
        | None => None
        | Some res => Some (@cast type t (fun x => match x with
                                                     | Some t => Impl t
                                                     | None => Empty_set
                                                   end) types' idx res)
      end.
  End updateAt.

End UpdateAt_exprD.
*)

(*
Set Printing Universes.
Print Universes "../dump.universes".
*)
