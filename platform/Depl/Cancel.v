(** Cancellation in separation logic implications *)

Require Import AutoSep.

Require Import Depl.Logic.


(** Syntactic substitutions for first-order variables *)
Definition fo_sub := fo_var -> option expr.
Definition fos_empty : fo_sub := fun _ => None.
Definition fos_set (s : fo_sub) (x : fo_var) (e : expr) : fo_sub :=
  fun y => if string_dec y x then Some e else s y.

Theorem fos_set_eq : forall s x e,
  fos_set s x e x = Some e.
Proof.
  unfold fos_set; intros; destruct (string_dec x x); tauto.
Qed.

Theorem fos_set_ne : forall s x e y,
  y <> x
  -> fos_set s x e y = s y.
Proof.
  unfold fos_set; intros; destruct (string_dec y x); tauto.
Qed.

Hint Rewrite fos_set_eq fos_set_ne using congruence.

(** * Local proof automation *)

Inductive notThisOne := NotThisOne.

Ltac t := simpl; intuition;
  repeat (match goal with
            | _ => discriminate
            | _ => progress autorewrite with core in *
            | [ _ : context[match ?E with None => _ | _ => _ end] |- _ ] =>
              let Heq := fresh in case_eq E; [ intros ? Heq | intro Heq ]; rewrite Heq in *
            | [ _ : context[match ?E with Var _ => _ | _ => _ end] |- _ ] => destruct E
            | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; subst
            | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
            | [ H : _ |- _ ] => erewrite H; [ assert notThisOne by constructor | .. ];
              match goal with
                | [ H' : notThisOne |- _ ] => clear H'
                | _ => solve [ eauto ]
              end
            | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; subst
            | [ H1 : vcs _ -> _, H2 : vcs (_ ++ _) |- _ ] =>
              specialize (H1 (vcs_app_bwd1 _ _ H2)) || specialize (H1 (vcs_app_bwd2 _ _ H2))
            | [ H : exists x, _ |- _ ] => destruct H; intuition
          end; simpl in *); eauto.

(** * Substitution *)

Definition sub_expr (s : fo_sub) (e : expr) : option expr :=
  match e with
    | Var x => s x
    | Lift f => Some (Lift f)
  end.

Lemma sub_expr_monotone : forall s s',
  (forall x e, s x = Some e -> s' x = Some e)
  -> forall e e', sub_expr s e = Some e'
    -> sub_expr s' e = Some e'.
Proof.
  destruct e; t.
Qed.

Fixpoint sub_exprs (s : fo_sub) (es : list expr) : option (list expr) :=
  match es with
    | nil => Some nil
    | e :: es =>
      match sub_expr s e with
        | None => None
        | Some e =>
          match sub_exprs s es with
            | None => None
            | Some es => Some (e :: es)
          end
      end
  end.

Lemma sub_exprs_monotone : forall s s',
  (forall x e, s x = Some e -> s' x = Some e)
  -> forall es es', sub_exprs s es = Some es'
    -> sub_exprs s' es = Some es'.
Proof.
  induction es; t; erewrite sub_expr_monotone; eauto.
Qed.

Definition sub_pred (s : fo_sub) (p : pred) : option pred :=
  match p with
    | Named X es =>
      match sub_exprs s es with
        | None => None
        | Some es => Some (Named X es)
      end
    | _ => None
  end.

Lemma sub_pred_monotone : forall s s',
  (forall x e, s x = Some e -> s' x = Some e)
  -> forall p p', sub_pred s p = Some p'
    -> sub_pred s' p = Some p'.
Proof.
  destruct p; t; erewrite sub_exprs_monotone; eauto.
Qed.

(** * Unification *)

Definition unify_expr (s : fo_sub) (lhs rhs : expr) : option (fo_sub * list Prop) :=
  match lhs, rhs with
    | Var x, Var y =>
      match s y with
        | None => Some (fos_set s y (Var x), nil)
        | Some (Var x') => if string_dec x' x then Some (s, nil) else None
        | _ => None
      end
    | Lift f, Lift g => Some (s, (forall fE, f fE = g fE) :: nil)
    | Lift f, Var y =>
      match s y with
        | None => Some (fos_set s y (Lift f), nil)
        | Some (Lift f') => Some (s, (forall fE, f fE = f' fE) :: nil)
        | _ => None
      end
    | _, _ => None
  end.

Theorem unify_expr_sound : forall fE s lhs rhs s' Ps,
  unify_expr s lhs rhs = Some (s', Ps)
  -> vcs Ps
  -> exists rhs', sub_expr s' rhs = Some rhs'
    /\ exprD lhs fE = exprD rhs' fE.
Proof.
  destruct lhs, rhs; t.
Qed.

Theorem unify_expr_monotone : forall s lhs rhs s' Ps,
  unify_expr s lhs rhs = Some (s', Ps)
  -> forall x e, s x = Some e -> s' x = Some e.
Proof.
  destruct lhs, rhs; t.
Qed.

Fixpoint unify_args (s : fo_sub) (lhs rhs : list expr) : option (fo_sub * list Prop) :=
  match lhs, rhs with
    | nil, nil => Some (s, nil)
    | e1 :: lhs, e2 :: rhs =>
      match unify_expr s e1 e2 with
        | None => None
        | Some (s, Ps) =>
          match unify_args s lhs rhs with
            | None => None
            | Some (s, Ps') => Some (s, Ps ++ Ps')
          end
      end
    | _, _ => None
  end.

Lemma map_nil : forall A B (f : A -> B),
  nil = map f nil.
Proof.
  auto.
Qed.

Lemma map_cons : forall A B (f : A -> B) x xs ls,
  ls = f x :: map f xs
  -> ls = map f (x :: xs).
Proof.
  intros; subst; auto.
Qed.

Local Hint Immediate map_nil map_cons.

Local Hint Immediate vcs_app_bwd1 vcs_app_bwd2.

Ltac unify_args := t;
  match goal with
    | [ _ : context[match ?p with pair _ _ => _ end] |- _ ] => destruct p
  end;
  match goal with
    | [ _ : context[unify_args ?s ?lhs ?rhs], IH : forall rhs : list expr, _ |- _ ] =>
      let Heq := fresh in
      specialize (IH rhs s); case_eq (unify_args s lhs rhs); [
        intros ? Heq; rewrite Heq in *;
          match goal with
            | [ p : prod _ _ |- _ ] => destruct p
          end; specialize (IH _ _ eq_refl)
        | intro Heq; rewrite Heq in *; discriminate ]
  end; t.

Local Hint Resolve unify_expr_monotone.

Theorem unify_args_monotone : forall lhs rhs s s' Ps,
  unify_args s lhs rhs = Some (s', Ps)
  -> forall x e, s x = Some e -> s' x = Some e.
Proof.
  induction lhs; destruct rhs; unify_args.
Qed.

Local Hint Resolve unify_args_monotone.

Theorem unify_args_sound : forall fE lhs rhs s s' Ps,
  unify_args s lhs rhs = Some (s', Ps)
  -> vcs Ps
  -> exists rhs', sub_exprs s' rhs = Some rhs'
    /\ map (fun e => exprD e fE) lhs = map (fun e => exprD e fE) rhs'.
Proof.
  induction lhs; destruct rhs; unify_args;
    match goal with
      | [ H : _ |- _ ] => specialize (unify_expr_sound fE _ _ _ _ _ H); t
    end;
    repeat esplit; eauto;
      erewrite sub_expr_monotone; [ eauto | | eauto ]; eauto.
Qed.

Definition unify_pred (s : fo_sub) (lhs rhs : pred) : option (fo_sub * list Prop) :=
  match lhs, rhs with
    | Named X1 es1, Named X2 es2 =>
      if string_dec X1 X2 then unify_args s es1 es2 else None
    | _, _ => None
  end.

Theorem unify_pred_monotone : forall lhs rhs s s' Ps,
  unify_pred s lhs rhs = Some (s', Ps)
  -> forall x e, s x = Some e -> s' x = Some e.
Proof.
  destruct lhs, rhs; unify_args.
Qed.

Theorem unify_pred_sound : forall G (hE : ho_env G) fE lhs rhs s s' Ps,
  unify_pred s lhs rhs = Some (s', Ps)
  -> vcs Ps
  -> exists rhs', sub_pred s' rhs = Some rhs'
    /\ predD lhs hE fE = predD rhs' hE fE.
Proof.
  destruct lhs, rhs; t;
    match goal with
      | [ H : _ |- _ ] => specialize (unify_args_sound fE _ _ _ _ _ H); t
    end.
Qed.


(** * Finally, cancelation *)

(** Result of cancelation *)
Inductive result :=
| Success (NewLhs : normal) (ProveThese : list Prop)
| Failure (Message : Prop).

(*Fixpoint cancel' (s : fo_sub) (lhs : normal) (p : pred) : result.

Definition cancel (lhs rhs : normal) : result.*)
