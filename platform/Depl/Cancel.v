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
            | [ _ : context[match ?p with pair _ _ => _ end] |- _ ] => destruct p
          end; simpl in *); eauto.

(** * Substitution *)

Definition sub_expr (s : fo_sub) (e : expr) : option expr :=
  match e with
    | Var x => s x
    | Lift f => Some (Lift (fun fE => f (fun x => match s x with
                                                    | None => Dyn tt
                                                    | Some e => exprD e fE
                                                  end)))
  end.

Lemma sub_expr_monotone : forall s s' e,
  (forall fE fE', (forall x, s x <> None -> fE x = fE' x) -> exprD e fE = exprD e fE')
  -> (forall x e, s x = Some e -> s' x = Some e)
  -> forall e', sub_expr s e = Some e'
    -> exists e'', sub_expr s' e = Some e''
      /\ forall fE, exprD e' fE = exprD e'' fE.
Proof.
  destruct e; t.
  repeat esplit; simpl; intros.
  apply H; intros.
  specialize (H0 x).
  destruct (s x).
  erewrite H0; eauto.
  tauto.
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

Fixpoint sub_preds (s : fo_sub) (ps : list pred) : option (list pred) :=
  match ps with
    | nil => Some nil
    | p :: ps =>
      match sub_pred s p with
        | None => None
        | Some p =>
          match sub_preds s ps with
            | None => None
            | Some ps => Some (p :: ps)
          end
      end
  end.

Lemma sub_preds_monotone : forall s s',
  (forall x e, s x = Some e -> s' x = Some e)
  -> forall es es', sub_preds s es = Some es'
    -> sub_preds s' es = Some es'.
Proof.
  induction es; t; erewrite sub_pred_monotone; eauto.
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
| Success (NewLhs : list pred) (ProveThese : list Prop)
| Failure (Message : Prop).

(** Result of canceling just one atomic predicate *)
Inductive result1 :=
| Success1 (NewSub : fo_sub) (NewLhs : list pred) (ProveThese : list Prop)
| Failure1 (Message : Prop).

Inductive noMatchFor (rhs : pred) := .

(** Find a LHS match for a single RHS predicate. *)
Fixpoint findMatching (s : fo_sub) (lhs : list pred) (rhs : pred) : result1 :=
  match lhs with
    | nil => Failure1 (noMatchFor rhs)
    | p :: lhs =>
      match unify_pred s p rhs with
        | Some (s, Ps) => Success1 s lhs Ps 
        | None =>
          match findMatching s lhs rhs with
            | Success1 s lhs Ps => Success1 s (p :: lhs) Ps
            | x => x
          end
      end
  end.

Local Hint Resolve unify_pred_monotone.

Theorem findMatching_monotone : forall rhs lhs s s' lhs' Ps,
  findMatching s lhs rhs = Success1 s' lhs' Ps
  -> forall x e, s x = Some e -> s' x = Some e.
Proof.
  induction lhs; t.

  injection H; clear H; intros; subst; eauto.

  specialize (IHlhs s).
  destruct (findMatching s lhs rhs); try discriminate.
  injection H; clear H; intros; subst; eauto.
Qed.

Local Hint Resolve findMatching_monotone.

Theorem findMatching_sound : forall G (hE : ho_env G) S fE rhs lhs s s' lhs' Ps,
  findMatching s lhs rhs = Success1 s' lhs' Ps
  -> vcs Ps
  -> exists rhs', sub_pred s' rhs = Some rhs'
    /\ (SubstsH S (fold_left (fun hp p => starB (predD p hE fE) hp) lhs (empB _))
    ===> SubstsH S (predD rhs' hE fE)
    * SubstsH S (fold_left (fun hp p => starB (predD p hE fE) hp) lhs' (empB _))).
Proof.
  induction lhs; t.

  match goal with
    | [ H : Success1 _ _ _ = Success1 _ _ _ |- _ ] => injection H; clear H; intros; subst
  end.
  eapply unify_pred_sound in H1; eauto; t.
  repeat esplit.
  eapply Himp_trans; [ apply star_out_fwd | ].
  apply SubstsH_star_fwd.

  match goal with
    | [ _ : context[findMatching ?s ?lhs ?rhs], IH : forall s : fo_sub, _ |- _ ] =>
      let Heq := fresh in specialize (IH s); case_eq (findMatching s lhs rhs);
        [ intros ? ? ? Heq; rewrite Heq in *; specialize (IH _ _ _ eq_refl)
          | intros ? Heq; rewrite Heq in *; try discriminate ]
  end.
  match goal with
    | [ H : Success1 _ _ _ = Success1 _ _ _ |- _ ] => injection H; clear H; intros; subst
  end.
  t.
  repeat esplit.

  eapply Himp_trans; [ apply star_out_fwd | ].
  eapply Himp_trans; [ apply SubstsH_star_fwd | ].
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl | apply star_out_bwd ] ].
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl | apply SubstsH_star_bwd ] ].
  eapply Himp_trans; [ | apply Himp_star_assoc ].
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_star_comm | apply Himp_refl ] ].
  eapply Himp_trans; [ | apply Himp_star_assoc' ].
  apply Himp_star_frame; auto; apply Himp_refl.
Qed.

(** Find LHS matches for all RHS predicates. *)
Fixpoint findMatchings (s : fo_sub) (lhs rhs : list pred) : result1 :=
  match rhs with
    | nil => Success1 s lhs nil
    | p :: rhs =>
      match findMatching s lhs p with
        | Success1 s lhs Ps =>
          match findMatchings s lhs rhs with
            | Success1 s lhs Ps' => Success1 s lhs (Ps ++ Ps')
            | x => x
          end
        | x => x
      end
  end.

Theorem findMatchings_monotone : forall rhs lhs s s' lhs' Ps,
  findMatchings s lhs rhs = Success1 s' lhs' Ps
  -> forall x e, s x = Some e -> s' x = Some e.
Proof.
  induction rhs; t.

  case_eq (findMatching s lhs a); intros.
  rewrite H1 in *.
  specialize (IHrhs NewLhs NewSub).
  destruct (findMatchings NewSub NewLhs rhs); try discriminate.
  injection H; clear H; intros; subst.
  eauto.

  rewrite H1 in *; discriminate.
Qed.

Local Hint Resolve findMatchings_monotone.

Theorem findMatchings_sound : forall G (hE : ho_env G) S fE rhs lhs s s' lhs' Ps,
  findMatchings s lhs rhs = Success1 s' lhs' Ps
  -> vcs Ps
  -> exists rhs', sub_preds s' rhs = Some rhs'
    /\ (SubstsH S (fold_left (fun hp p => starB (predD p hE fE) hp) lhs (empB _))
    ===> SubstsH S (fold_left (fun hp p => starB (predD p hE fE) hp) rhs' (empB _))
    * SubstsH S (fold_left (fun hp p => starB (predD p hE fE) hp) lhs' (empB _))).
Proof.
  induction rhs; t.

  injection H; clear H; intros; subst.
  repeat esplit.
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply SubstsH_emp_bwd | apply Himp_refl ] ].
  apply Himp_star_Emp'.

  match goal with
    | [ _ : context[findMatching ?s ?lhs ?rhs] |- _ ] =>
      let Heq := fresh in case_eq (findMatching s lhs rhs); [ intros ? ? ? Heq | intros ? Heq ];
        rewrite Heq in *; try discriminate
  end.
  match goal with
    | [ _ : context[findMatchings ?s ?lhs ?rhs], IH : forall lhs : list pred, _ |- _ ] =>
      let Heq := fresh in specialize (IH lhs s); case_eq (findMatchings s lhs rhs);
        [ intros ? ? ? Heq; rewrite Heq in *; specialize (IH _ _ _ eq_refl)
          | intros ? Heq; rewrite Heq in *; try discriminate ]
  end.
  match goal with
    | [ H : Success1 _ _ _ = Success1 _ _ _ |- _ ] => injection H; clear H; intros; subst
  end; t.
  specialize (findMatching_sound _ hE S fE _ _ _ _ _ _ H1); t.
  erewrite sub_pred_monotone; [ .. | eauto ]; eauto.
  repeat esplit.
  eapply Himp_trans; [ apply H6 | ].
  simpl.
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply star_out_bwd | apply Himp_refl ] ].
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply SubstsH_star_bwd | apply Himp_refl ] ].
  eapply Himp_trans; [ | apply Himp_star_assoc' ].
  apply Himp_star_frame; auto; apply Himp_refl.
Qed.

(** Overall cancelation *)
Definition cancel (lhs rhs : normal) : result :=
  match findMatchings fos_empty (NImpure lhs) (NImpure rhs) with
    | Failure1 msg => Failure msg
    | Success1 s lhs' Ps => Success lhs' (
      (forall x, In x (NQuants rhs) -> s x <> None)
      :: match NPure rhs with
           | None => Ps
           | Some P =>
             (forall fE1 fE2, (forall x, s x <> None -> fE1 x = fE2 x)
               -> P fE1 = P fE2)
             :: (forall fE,
               let fE' := (fun x => match s x with
                                      | None => Dyn tt
                                      | Some e => exprD e fE
                                    end) in
               match NPure lhs with
                 | None => P fE'
                 | Some P1 => P1 fE -> P fE'
               end)
             :: Ps
         end)
  end.

Theorem cancel_sound : forall fE G (hE : ho_env G) S lhs rhs lhs' Ps,
  cancel lhs rhs = Success lhs' Ps
  -> vcs Ps
  -> SubstsH S (normalD lhs hE fE)
  ===> SubstsH S (normalD rhs hE fE)
  * SubstsH S (normalD {| NQuants := NQuants lhs;
    NPure := None;
    NImpure := lhs' |} hE fE).
Proof.
  unfold cancel; intros.
  
  case_eq (findMatchings fos_empty (NImpure lhs) (NImpure rhs)); intros.
  Focus 2.
  rewrite H1 in *; discriminate.

  rewrite H1 in *.
  injection H; clear H; intros; subst.
  inversion H0; clear H0; intros; subst.
  assert (vcs ProveThese) by t.
  specialize (fun fE => findMatchings_sound _ hE S fE _ _ _ _ _ _ H1); intro Hfms.
  eapply Himp_trans; [ | apply Himp_star_comm ].

  Lemma addQuants_gulp : forall G (f : _ -> hpropB G) S p qs fE,
    SubstsH S (addQuants qs (fun fE => f fE * p) fE)
    ===> SubstsH S (addQuants qs f fE) * SubstsH S p.
  Proof.
    induction qs; t.

    apply SubstsH_star_fwd.

    eapply Himp_trans; [ apply SubstsH_ex_fwd | ].
    apply Himp'_ex; intro.
    eapply Himp_trans; [ apply IHqs | ].
    apply Himp_star_frame; try apply Himp_refl.
    eapply Himp_trans; [ | apply SubstsH_ex_bwd ].
    apply Himp_ex_c; eauto.
    eexists; apply Himp_refl.
  Qed.

  eapply Himp_trans; [ | apply addQuants_gulp ].
  simpl.
  apply addQuants_monotone; intros.
  specialize (Hfms fE'); intuition.
  destruct H2; intuition.
  eapply Himp_trans; [ apply multistar_weaken | ].
  instantiate (1 := (match NPure lhs with
                       | Some P => [|P fE'|]
                       | None => Emp
                     end * Emp)%Sep).
  eapply Himp_trans; [ | apply SubstsH_star_bwd ].
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl | apply SubstsH_emp_bwd ] ].
  eapply Himp_trans; [ | apply Himp_star_comm ].
  apply Himp_star_Emp'.
  eapply Himp_trans; [ apply star_out_fwd | ].
  eapply Himp_trans; [ apply SubstsH_star_fwd | ].
  eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply H6 ] | ].
  eapply Himp_trans; [ | apply SubstsH_star_bwd ].
  eapply Himp_trans; [ apply Himp_star_assoc' | ].
  eapply Himp_trans; [ apply Himp_star_comm | ].
  apply Himp_star_frame; try apply Himp_refl.
  
  Lemma sub_expr_closed : forall s e,
    (forall fE fE', exprD e fE = exprD e fE')
    -> forall e', sub_expr s e = Some e'
      -> e' = e.
  Proof.
    destruct e; simpl; intuition.
    exfalso.
    specialize (H (fun _ => Dyn tt) (fun _ => Dyn false)).
    assert (forall x y : unit, x = y).
    destruct x0, y; auto.
    simpl in *.
    apply (f_equal Ty) in H; simpl in *.
    rewrite H in H1.
    specialize (H1 true false); discriminate.
  Qed.

  Lemma sub_pred_closed : forall s p,
    wellScoped nil p
    -> forall p', sub_pred s p = Some p'
      -> p' = p.
  Proof.
    destruct p; simpl; intuition.
    case_eq (sub_exprs s es); intros.
    Focus 2.
    rewrite H1 in H0; discriminate.
    rewrite H1 in H0; injection H0; clear H0; intros; subst.
    f_equal.
    generalize dependent l.
    induction es; simpl; intuition.
    simpl in *.
    case_eq (sub_expr s a); intros.
    Focus 2.
    rewrite H0 in *; discriminate.
    rewrite H0 in *.
    apply sub_expr_closed in H0; eauto.
    subst.
    case_eq (sub_exprs s es); intros.
    Focus 2.
    rewrite H0 in *; discriminate.
    rewrite H0 in *.
    injection H1; clear H1; intros; subst.
    f_equal; eauto.
    intros; eapply H; auto; tauto.
  Qed.

  Lemma sub_preds_closed : forall s ps,
    List.Forall (wellScoped nil) ps
    -> forall ps', sub_preds s ps = Some ps'
      -> ps' = ps.
  Proof.
    induction 1; simpl; intuition.
    case_eq (sub_pred s x); intros.
    Focus 2.
    rewrite H2 in *; discriminate.
    rewrite H2 in *.
    case_eq (sub_preds s l); intros.
    Focus 2.
    rewrite H3 in *; discriminate.
    rewrite H3 in *.
    injection H1; clear H1; intros; subst.
    f_equal; auto.
    eapply sub_pred_closed; eauto.
  Qed.

  Lemma choose_existentials_expr : forall qs fE fE' s e e',
    (forall fE fE', (forall x, In x qs -> fE x = fE' x)
      -> exprD e fE = exprD e fE')
    -> List.Forall (fun x => exists e, s x = Some e /\ fE x = exprD e fE') qs
    -> sub_expr s e = Some e'
    -> exprD e fE' = exprD e' fE.
  Proof.
    destruct e; simpl; intuition.
    Focus 2.
    injection H1; clear H1; intros; subst.
    simpl.
    apply H.
    intros.
    eapply Forall_forall in H0; eauto.
    

  Lemma choose_existentials_exprs : forall qs fE fE' s es es',
    (forall fE fE', (forall x, In x qs -> fE x = fE' x)
      -> forall e, In e es -> exprD e fE = exprD e fE')
    -> List.Forall (fun x => exists e, s x = Some e /\ fE x = exprD e fE') qs
    -> sub_exprs s es = Some es'
    -> map (fun e => exprD e fE') es = map (fun e : expr => exprD e fE) es'.
  Proof.
    induction es; simpl; intuition.

    injection H1; clear H1; intros; subst; auto.

    case_eq (sub_e

  Lemma choose_existentials_pred : forall G (hE : ho_env G) S qs p p' fE fE' s,
     wellScoped qs p
     -> List.Forall (fun x => exists e, s x = Some e /\ fE x = exprD e fE') qs
     -> sub_pred s p = Some p'
     -> SubstsH S (predD p hE fE') ===> SubstsH S (predD p' hE fE).
  Proof.
    destruct p; simpl; intuition.
    case_eq (sub_exprs s es); intros.
    Focus 2.
    rewrite H2 in *; discriminate.
    rewrite H2 in *.
    injection H1; clear H1; intros; subst.
    simpl.
    


  Lemma choose_existentials : forall G (hE : ho_env G) fE S s ps' qs qs' ps fE',
    sub_preds s ps = Some ps'
    -> List.Forall (wellScoped (qs ++ qs')) ps
    -> List.Forall (fun x => exists e, s x = Some e /\ fE x = exprD e fE') qs'
    -> SubstsH S (fold_left (fun hp p => predD p hE fE' * hp) ps' Emp)
    ===> SubstsH S (addQuants qs
      (fun fE0 => fold_left (fun hp p => predD p hE fE0 * hp) ps Emp) fE).
  Proof.
    induction qs; simpl; intuition.

    generalize dependent ps'.
    induction H0; simpl; intuition.
    injection H; clear H; intros; subst.
    apply Himp_refl.
    case_eq (sub_pred s x); intros.
    Focus 2.
    rewrite H3 in H2; discriminate.
    rewrite H3 in *.
    case_eq (sub_preds s l); intros.
    Focus 2.
    rewrite H4 in *; discriminate.
    rewrite H4 in *.
    injection H2; clear H2; intros; subst.
    simpl.
    eapply Himp_trans; [ apply star_out_fwd | ].
    eapply Himp_trans; [ apply SubstsH_star_fwd | ].
    eapply Himp_trans; [ | apply star_out_bwd ].
    eapply Himp_trans; [ | apply SubstsH_star_bwd ].
    apply Himp_star_frame; auto.



    replace ps' with ps.
    admit. (*apply Himp_refl.*)
    symmetry; eapply sub_preds_closed; eauto.

    eapply Himp_trans; [ | apply SubstsH_ex_bwd ].
    case_eq (s a); intros.
    2: solve [ exfalso; eauto ].
    apply Himp_ex_c; exists (exprD e fE).
    apply IHqs.


    

    

  Lemma choose_existentials : forall G (hE : ho_env G) fE S s rhs ps,
    sub_preds s (NImpure rhs) = Some ps
    -> match NPure rhs with
         | None => True
         | Some P => P fE
       end
    -> (forall x T, In (x, T) (NQuants rhs) -> s x <> None)
    -> SubstsH S (fold_left (fun hp p => predD p hE fE * hp) ps Emp)
    ===> SubstsH S (normalD rhs hE fE).
  Proof.
    unfold normalD.
    
  
  specialize (f

  SearchAbout Himp empB.
  apply Himp_emp.
  SearchAbout fold_left SubstsH.