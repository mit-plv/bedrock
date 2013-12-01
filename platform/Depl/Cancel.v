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

Theorem fo_set_eq : forall fE x e,
  fo_set fE x e x = e.
Proof.
  unfold fo_set; intros; destruct (string_dec x x); tauto.
Qed.

Theorem fo_set_ne : forall fE x e y,
  y <> x
  -> fo_set fE x e y = fE y.
Proof.
  unfold fo_set; intros; destruct (string_dec y x); tauto.
Qed.

Hint Rewrite fo_set_eq fo_set_ne using congruence.

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
            | [ H : List.Forall _ (_ :: _) |- _ ] => inversion H; clear H; subst
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

Lemma sub_exprs_monotone : forall s s' es,
  (forall fE fE', (forall x, s x <> None -> fE x = fE' x)
    -> map (fun e => exprD e fE) es = map (fun e => exprD e fE') es)
  -> (forall x e, s x = Some e -> s' x = Some e)
  -> forall es', sub_exprs s es = Some es'
    -> exists es'', sub_exprs s' es = Some es''
      /\ forall fE, map (fun e => exprD e fE) es' = map (fun e => exprD e fE) es''.
Proof.
  induction es; t.
  edestruct sub_expr_monotone; eauto.
  intros.
  specialize (H _ _ H1).
  injection H; eauto.
  t.
  edestruct IHes; eauto.
  intros.
  specialize (H _ _ H1); congruence.
  t.
  exists (x :: x0); t.
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

Lemma sub_pred_monotone : forall G (hE : ho_env G) s s' p xs,
  wellScoped xs p
  -> (forall x, In x xs -> s x <> None)
  -> (forall x e, s x = Some e -> s' x = Some e)
  -> forall p', sub_pred s p = Some p'
    -> exists p'', sub_pred s' p = Some p''
      /\ forall fE, predD p' hE fE = predD p'' hE fE.
Proof.
  destruct p; t.
  edestruct sub_exprs_monotone; eauto.
  generalize dependent l; induction es; simpl in *; intuition.
  f_equal; simpl in *; eauto.
  destruct (sub_expr s a); try discriminate.
  destruct (sub_exprs s es); try discriminate.
  eauto.
  t.
  repeat esplit; t.
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

Lemma sub_preds_monotone : forall G (hE : ho_env G) s s' ps xs,
  List.Forall (wellScoped xs) ps
  -> (forall x, In x xs -> s x <> None)
  -> (forall x e, s x = Some e -> s' x = Some e)
  -> forall ps', sub_preds s ps = Some ps'
    -> exists ps'', sub_preds s' ps = Some ps''
      /\ forall fE, map (fun p => predD p hE fE) ps' = map (fun p => predD p hE fE) ps''.
Proof.
  induction ps; t.

  edestruct sub_pred_monotone; eauto; t.
  edestruct IHps; eauto; t.
  repeat esplit; t.
Qed.

(** * Unification *)

Definition unify_expr (s : fo_sub) (lhs rhs : expr)
  : option (fo_sub * list (fo_env -> fo_sub -> Prop)) :=
  match lhs, rhs with
    | Var x, Var y =>
      match s y with
        | None => Some (fos_set s y (Var x), nil)
        | Some (Var x') => if string_dec x' x then Some (s, nil) else None
        | _ => None
      end
    | Lift f, Lift g => Some (s, (fun fE s' => f fE = g (fun x =>
      match s' x with
        | Some e => exprD e fE
        | None => Dyn tt
      end)) :: nil)
    | Lift f, Var y =>
      match s y with
        | None => Some (fos_set s y (Lift f), nil)
        | Some (Lift f') => Some (s, (fun fE _ => f fE = f' fE) :: nil)
        | _ => None
      end
    | _, _ => None
  end.

Theorem unify_expr_sound : forall fE s s'' lhs rhs s' fs,
  unify_expr s lhs rhs = Some (s', fs)
  -> List.Forall (fun f => f fE s'') fs
  -> (forall x v, s' x = Some v -> s'' x = Some v)
  -> exists rhs', sub_expr s'' rhs = Some rhs'
    /\ exprD lhs fE = exprD rhs' fE.
Proof.
  destruct lhs, rhs; t.
  repeat esplit.
  apply H1; t.
  t.
  repeat esplit.
  apply H1; t.
  t.
Qed.

Theorem unify_expr_monotone : forall s lhs rhs s' fs,
  unify_expr s lhs rhs = Some (s', fs)
  -> forall x e, s x = Some e -> s' x = Some e.
Proof.
  destruct lhs, rhs; t.
Qed.

Fixpoint unify_args (s : fo_sub) (lhs rhs : list expr)
  : option (fo_sub * list (fo_env -> fo_sub -> Prop)) :=
  match lhs, rhs with
    | nil, nil => Some (s, nil)
    | e1 :: lhs, e2 :: rhs =>
      match unify_expr s e1 e2 with
        | None => None
        | Some (s, fs) =>
          match unify_args s lhs rhs with
            | None => None
            | Some (s, fs') => Some (s, fs ++ fs')
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

Local Hint Resolve unify_expr_monotone.

Theorem unify_args_monotone : forall lhs rhs s s' fs,
  unify_args s lhs rhs = Some (s', fs)
  -> forall x e, s x = Some e -> s' x = Some e.
Proof.
  induction lhs; destruct rhs; t.
Qed.

Local Hint Resolve unify_args_monotone.

Lemma Forall_app_fwd1 : forall A (P : A -> Prop) ls2 ls1,
  List.Forall P (ls1 ++ ls2)
  -> List.Forall P ls1.
Proof.
  induction ls1; inversion_clear 1; eauto.
Qed.

Lemma Forall_app_fwd2 : forall A (P : A -> Prop) ls2 ls1,
  List.Forall P (ls1 ++ ls2)
  -> List.Forall P ls2.
Proof.
  induction ls1; simpl; try solve [ eauto ]; inversion_clear 1; eauto.
Qed.

Local Hint Immediate Forall_app_fwd1 Forall_app_fwd2.

Theorem unify_args_sound : forall fE s'' lhs rhs s s' fs,
  unify_args s lhs rhs = Some (s', fs)
  -> List.Forall (fun f => f fE s'') fs
  -> (forall x v, s' x = Some v -> s'' x = Some v)
  -> exists rhs', sub_exprs s'' rhs = Some rhs'
    /\ map (fun e => exprD e fE) lhs = map (fun e => exprD e fE) rhs'.
Proof.
  induction lhs; destruct rhs; t.
  edestruct unify_expr_sound; eauto; t.
  edestruct IHlhs; eauto; t.
Qed.

Definition unify_pred (s : fo_sub) (lhs rhs : pred) : option (fo_sub * list (fo_env -> fo_sub -> Prop)) :=
  match lhs, rhs with
    | Named X1 es1, Named X2 es2 =>
      if string_dec X1 X2 then unify_args s es1 es2 else None
    | _, _ => None
  end.

Theorem unify_pred_monotone : forall lhs rhs s s' fs,
  unify_pred s lhs rhs = Some (s', fs)
  -> forall x e, s x = Some e -> s' x = Some e.
Proof.
  destruct lhs, rhs; t.
Qed.

Theorem unify_pred_sound : forall G (hE : ho_env G) fE s'' lhs rhs s s' fs,
  unify_pred s lhs rhs = Some (s', fs)
  -> List.Forall (fun f => f fE s'') fs
  -> (forall x v, s' x = Some v -> s'' x = Some v)
  -> exists rhs', sub_pred s'' rhs = Some rhs'
    /\ predD lhs hE fE = predD rhs' hE fE.
Proof.
  destruct lhs, rhs; t.
  edestruct unify_args_sound; eauto; t.
Qed.


(** * Finally, cancelation *)

(** Result of cancelation *)
Inductive result :=
| Success (NewLhs : list pred) (ProveThis : Prop)
| Failure (Message : Prop).

(** Result of canceling just one atomic predicate *)
Inductive result1 :=
| Success1 (NewSub : fo_sub) (NewLhs : list pred)
  (ProveThese : list (fo_env -> fo_sub -> Prop))
| Failure1 (Message : Prop).

Inductive noMatchFor (rhs : pred) := .

(** Find a LHS match for a single RHS predicate. *)
Fixpoint findMatching (s : fo_sub) (lhs : list pred) (rhs : pred) : result1 :=
  match lhs with
    | nil => Failure1 (noMatchFor rhs)
    | p :: lhs =>
      match unify_pred s p rhs with
        | Some (s, fs) => Success1 s lhs fs
        | None =>
          match findMatching s lhs rhs with
            | Success1 s lhs fs => Success1 s (p :: lhs) fs
            | x => x
          end
      end
  end.

Local Hint Resolve unify_pred_monotone.

Theorem findMatching_monotone : forall rhs lhs s s' lhs' fs,
  findMatching s lhs rhs = Success1 s' lhs' fs
  -> forall x e, s x = Some e -> s' x = Some e.
Proof.
  induction lhs; t.

  injection H; clear H; intros; subst; eauto.

  specialize (IHlhs s).
  destruct (findMatching s lhs rhs); try discriminate.
  injection H; clear H; intros; subst; eauto.
Qed.

Local Hint Resolve findMatching_monotone.

Theorem findMatching_sound : forall G (hE : ho_env G) S fE rhs s'' lhs s s' lhs' fs,
  findMatching s lhs rhs = Success1 s' lhs' fs
  -> List.Forall (fun f => f fE s'') fs
  -> (forall x v, s' x = Some v -> s'' x = Some v)
  -> exists rhs', sub_pred s'' rhs = Some rhs'
    /\ (SubstsH S (fold_left (fun hp p => starB (predD p hE fE) hp) lhs (empB _))
    ===> SubstsH S (predD rhs' hE fE)
    * SubstsH S (fold_left (fun hp p => starB (predD p hE fE) hp) lhs' (empB _))).
Proof.
  induction lhs; t.

  match goal with
    | [ H : Success1 _ _ _ = Success1 _ _ _ |- _ ] => injection H; clear H; intros; subst
  end.
  edestruct unify_pred_sound; eauto; t.
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
        | Success1 s lhs fs =>
          match findMatchings s lhs rhs with
            | Success1 s lhs fs' => Success1 s lhs (fs ++ fs')
            | x => x
          end
        | x => x
      end
  end.

Theorem findMatchings_monotone : forall rhs lhs s s' lhs' fs,
  findMatchings s lhs rhs = Success1 s' lhs' fs
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

Theorem findMatchings_sound : forall G (hE : ho_env G) S fE rhs s'' lhs s s' lhs' fs,
  findMatchings s lhs rhs = Success1 s' lhs' fs
  -> List.Forall (fun f => f fE s'') fs
  -> (forall x v, s' x = Some v -> s'' x = Some v)
  -> exists rhs', sub_preds s'' rhs = Some rhs'
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
    | [ _ : context[findMatchings ?s ?lhs ?rhs], IH : forall s'' : fo_sub, _ |- _ ] =>
      let Heq := fresh in specialize (IH s'' lhs s); case_eq (findMatchings s lhs rhs);
        [ intros ? ? ? Heq; rewrite Heq in *; specialize (IH _ _ _ eq_refl)
          | intros ? Heq; rewrite Heq in *; try discriminate ]
  end.
  match goal with
    | [ H : Success1 _ _ _ = Success1 _ _ _ |- _ ] => injection H; clear H; intros; subst
  end; t.
  edestruct findMatching_sound; eauto; t.
  edestruct IHrhs; eauto; t.
  repeat esplit.
  eapply Himp_trans; [ apply H5 | ].
  simpl.
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply star_out_bwd | apply Himp_refl ] ].
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply SubstsH_star_bwd | apply Himp_refl ] ].
  eapply Himp_trans; [ | apply Himp_star_assoc' ].
  apply Himp_star_frame; auto; apply Himp_refl.
Qed.

(** Overall cancellation *)
Definition cancel (lhs rhs : normal) : result :=
  match findMatchings fos_empty (NImpure lhs) (NImpure rhs) with
    | Failure1 msg => Failure msg
    | Success1 s lhs' fs => Success lhs' (
      (forall x, In x (NQuants rhs) -> s x <> None)
      /\ (forall fE, List.Forall (fun f => f fE s) fs)
      /\ match NPure rhs with
           | None => True
           | Some P =>
             (forall fE1 fE2, (forall x, s x <> None -> fE1 x = fE2 x)
               -> P fE1 = P fE2)
             /\ (forall fE,
               let fE' := (fun x => match s x with
                                      | None => Dyn tt
                                      | Some e => exprD e fE
                                    end) in
               match NPure lhs with
                 | None => P fE'
                 | Some P1 => P1 fE -> P fE'
               end)
         end)
  end.

Theorem cancel_sound : forall fE G (hE : ho_env G) S lhs rhs lhs' P,
  cancel lhs rhs = Success lhs' P
  -> P
  -> List.Forall (wellScoped (NQuants rhs)) (NImpure rhs)
  -> SubstsH S (normalD lhs hE fE)
  ===> SubstsH S (normalD rhs hE fE)
  * SubstsH S (normalD {| NQuants := NQuants lhs;
    NPure := None;
    NImpure := lhs' |} hE fE).
Proof.
  unfold cancel; intros.
  
  case_eq (findMatchings fos_empty (NImpure lhs) (NImpure rhs)); intros.
  Focus 2.
  rewrite H2 in *; discriminate.

  rewrite H2 in *.
  injection H; clear H; intros; subst; intuition.

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
  edestruct findMatchings_sound; eauto; intuition.
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
  eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply H7 ] | ].
  eapply Himp_trans; [ | apply SubstsH_star_bwd ].
  eapply Himp_trans; [ apply Himp_star_assoc' | ].
  eapply Himp_trans; [ apply Himp_star_comm | ].
  apply Himp_star_frame; try apply Himp_refl.
  clear H7.

  unfold normalD.
  eapply Himp_trans; [ apply Himp_star_frame; [ | apply Himp_refl ] | ].
  instantiate (1 := [| match NPure lhs with
                         | Some P => P fE'
                         | None => True
                       end |]%Sep).
  destruct (NPure lhs).
  apply SubstsH_inj_fwd.
  apply SubstsH_emp_fwd.
  apply Himp_star_pure_c; intro.
  assert (SubstsH S
    (fold_left (fun (hp : hpropB G) (p : pred) => predD p hE fE' * hp) x Emp) ===>
    SubstsH S
    (addQuants (NQuants rhs)
      (fun fE0 : fo_env =>
        fold_left (fun (hp : hpropB G) (p : pred) => predD p hE fE0 * hp)
        (NImpure rhs)
        Emp) fE)).
  2: admit.

  Lemma sub_expr_agrees : forall fE fE' s,
    (forall x v, s x = Some v -> fE x = exprD v fE')
    -> forall e e', sub_expr s e = Some e'
      -> (forall fE fE',
        (forall x, s x <> None -> fE x = fE' x)
        -> exprD e fE = exprD e fE')
      -> exprD e' fE' = exprD e fE.
  Proof.
    destruct e; simpl; intuition.
    erewrite H; eauto.
    injection H0; clear H0; intros; subst.
    simpl.
    apply H1.
    intros.
    specialize (H x).
    destruct (s x); intuition.
    symmetry; auto.
  Qed.

  Lemma sub_exprs_agrees : forall fE fE' s,
    (forall x v, s x = Some v -> fE x = exprD v fE')
    -> forall es es', (forall fE fE',
      (forall x, s x <> None -> fE x = fE' x)
      -> forall e, In e es -> exprD e fE = exprD e fE')
    -> sub_exprs s es = Some es'
    -> map (fun e => exprD e fE') es' = map (fun e => exprD e fE) es.
  Proof.
    induction es; simpl; intuition idtac.

    injection H1; clear H1; intros; subst.
    auto.

    case_eq (sub_expr s a); intros.
    Focus 2.
    rewrite H2 in *; discriminate.
    rewrite H2 in *.
    case_eq (sub_exprs s es); intros.
    Focus 2.
    rewrite H3 in *; discriminate.
    rewrite H3 in *.
    injection H1; clear H1; intros; subst; simpl in *.
    f_equal.
    eapply sub_expr_agrees; eauto.
    eauto.
  Qed.

  Lemma sub_pred_agrees : forall G (hE : ho_env G) S fE fE' qs' s,
    (forall x v, s x = Some v -> fE x = exprD v fE')
    -> List.Forall (fun x => s x <> None)%type qs'
    -> forall p p', wellScoped qs' p
      -> sub_pred s p = Some p'
      -> SubstsH S (predD p' hE fE') ===> SubstsH S (predD p hE fE).
  Proof.
    induction p; simpl; intuition.

    case_eq (sub_exprs s es); intros.
    Focus 2.
    rewrite H3 in *; discriminate.
    rewrite H3 in *.
    injection H2; clear H2; intros; subst; simpl.
    erewrite sub_exprs_agrees; try apply Himp_refl; eauto.
    intros.
    apply H1; eauto.
    intros.
    eapply Forall_forall in H0; eauto.
  Qed.

  Lemma sub_preds_agrees : forall G (hE : ho_env G) S fE fE' qs' s,
    (forall x v, s x = Some v -> fE x = exprD v fE')
    -> List.Forall (fun x => s x <> None)%type qs'
    -> forall ps, List.Forall (wellScoped qs') ps
      -> forall ps', sub_preds s ps = Some ps'
        -> SubstsH S (fold_left (fun hp p => predD p hE fE' * hp) ps' Emp)
        ===> SubstsH S (fold_left (fun hp p => predD p hE fE * hp) ps Emp).
  Proof.
    induction 3; simpl; intuition.

    injection H1; clear H1; intros; subst.
    apply Himp_refl.

    eapply Himp_trans; [ | apply star_out_bwd ].
    eapply Himp_trans; [ | apply SubstsH_star_bwd ].
    case_eq (sub_pred s x); intros.
    Focus 2.
    rewrite H4 in *; discriminate.
    rewrite H4 in *.
    case_eq (sub_preds s l); intros.
    Focus 2.
    rewrite H5 in *; discriminate.
    rewrite H5 in *.
    injection H3; clear H3; intros; subst; simpl.
    eapply Himp_trans; [ apply star_out_fwd | ].
    eapply Himp_trans; [ apply SubstsH_star_fwd | ].
    apply Himp_star_frame; auto.
    eauto using sub_pred_agrees.
  Qed.

  Lemma choose_existentials : forall G (hE : ho_env G) S s ps' ps,
    sub_preds s ps = Some ps'
    -> forall qs, List.Forall (fun x => s x <> None)%type qs
      -> forall qs' fE fE', List.Forall (fun x => s x <> None)%type qs'
        -> (forall x v, s x = Some v -> fE x = exprD v fE' \/ In x qs)
        -> List.Forall (wellScoped (qs' ++ qs)) ps
        -> SubstsH S (fold_left (fun hp p => predD p hE fE' * hp) ps' Emp)
        ===> SubstsH S (addQuants qs
          (fun fE0 => fold_left (fun hp p => predD p hE fE0 * hp) ps Emp) fE).
  Proof.
    induction 2; simpl; intuition.

    rewrite <- app_nil_end in *.
    eapply sub_preds_agrees; eauto.
    firstorder.

    eapply Himp_trans; [ | eapply SubstsH_ex_bwd ].
    apply Himp_ex_c.
    case_eq (s x); intuition idtac.
    exists (exprD e fE').
    rewrite <- DepList.pf_list_simpl in H4.
    eapply IHForall; try apply H4.
    eauto using Forall_app.
    intros.
    destruct (string_dec x x0); subst.
    rewrite H6 in H5; injection H5; clear H5; intros; subst.
    autorewrite with core; auto.
    autorewrite with core; auto.
    specialize (H3 _ _ H6); tauto.
  Qed.

  eapply choose_existentials; eauto.
  eapply Forall_forall; eauto.
  intros.

  Definition dyn1 := Dyn tt.
  Definition dyn2 := Dyn false.

  Theorem dyn_disc : dyn1 <> dyn2.
  Proof.
    intro.
    apply (f_equal Ty) in H.
    simpl in H.
    assert (exists x : unit, forall y, x = y).
    exists tt; destruct y; auto.
    rewrite H in H0.
    destruct H0.
    specialize (H0 (negb x)).
    destruct x; discriminate.
  Qed.

  Lemma unify_expr_adds : forall xs s lhs rhs s' Ps,
    unify_expr s lhs rhs = Some (s', Ps)
    -> (forall fE fE', (forall x, In x xs -> fE x = fE' x)
      -> exprD rhs fE = exprD rhs fE')
      -> forall x, s' x <> None -> s x <> None \/ In x xs.
  Proof.
    destruct lhs, rhs; simpl; intuition idtac; try discriminate.

    destruct (s x0).
    destruct e; try discriminate.
    destruct (string_dec x2 x); subst; try discriminate.
    injection H; clear H; intros; subst; tauto.
    injection H; clear H; intros; subst.
    unfold fos_set in H1.
    destruct (string_dec x1 x0); subst; intuition idtac.
    specialize (H0 (fun _ => dyn1)
      (fun x => if string_dec x x0 then dyn2 else dyn1)).
    simpl in H0.
    destruct (string_dec x0 x0); try tauto.
    destruct (In_dec string_dec x0 xs); intuition idtac.
    match type of H0 with
      | ?P -> _ => assert P
    end.
    intros.
    destruct (string_dec x1 x0); try congruence.
    subst; tauto.
    intuition idtac.
    destruct (dyn_disc H2).

    destruct (s x); try discriminate.
    destruct e; try discriminate.
    injection H; clear H; intros; subst; tauto.
    injection H; clear H; intros; subst.
    specialize (H0 (fun _ => dyn1)
      (fun x0 => if string_dec x x0 then dyn2 else dyn1)).
    simpl in H0.
    unfold fos_set in H1.
    destruct (string_dec x x); try tauto.
    destruct (string_dec x0 x); subst; intuition idtac.
    destruct (In_dec string_dec x xs); intuition idtac.
    match type of H0 with
      | ?P -> _ => assert P
    end.
    intros.
    destruct (string_dec x x0); try congruence.
    subst; tauto.
    intuition idtac.
    destruct (dyn_disc H2).
    
    injection H; clear H; intros; subst; tauto.
  Qed.

  Lemma unify_args_adds : forall xs lhs rhs s s' Ps,
    unify_args s lhs rhs = Some (s', Ps)
    -> (forall fE fE', (forall x, In x xs -> fE x = fE' x)
      -> forall e, In e rhs -> exprD e fE = exprD e fE')
      -> forall x, s' x <> None -> s x <> None \/ In x xs.
  Proof.
    induction lhs; destruct rhs; simpl; intuition idtac; try discriminate.

    injection H; clear H; intros; subst; tauto.
    
    case_eq (unify_expr s a e); intros.
    Focus 2.
    rewrite H2 in *; discriminate.
    rewrite H2 in *.
    destruct p.
    case_eq (unify_args f lhs rhs); intros.
    Focus 2.
    rewrite H3 in *; discriminate.
    rewrite H3 in *.
    destruct p.
    injection H; clear H; intros; subst.
    edestruct IHlhs; try apply H3; eauto.
    edestruct unify_expr_adds; try apply H2; eauto.
  Qed.

  Lemma unify_pred_adds : forall xs rhs s,
    wellScoped xs rhs
    -> forall lhs s' Ps, unify_pred s lhs rhs = Some (s', Ps)
      -> forall x, s' x <> None -> s x <> None \/ In x xs.
  Proof.
    destruct lhs, rhs; simpl in *; intuition idtac; try discriminate.
    destruct (string_dec X X0); subst; try discriminate.
    edestruct unify_args_adds; eauto.
  Qed.    

  Lemma findMatching_adds : forall xs rhs s,
    wellScoped xs rhs
    -> forall lhs s' lhs' Ps, findMatching s lhs rhs = Success1 s' lhs' Ps
      -> forall x, s' x <> None -> s x <> None \/ In x xs.
  Proof.
    induction lhs; simpl; intuition idtac.

    discriminate.

    case_eq (unify_pred s a rhs); intros.
    rewrite H2 in *.
    destruct p.
    injection H0; clear H0; intros; subst.
    edestruct unify_pred_adds; eauto.

    rewrite H2 in *.
    case_eq (findMatching s lhs rhs); intros.
    Focus 2.
    rewrite H3 in *; discriminate.
    rewrite H3 in *.
    injection H0; clear H0; intros; subst.
    eauto.
  Qed.

  Lemma findMatchings_adds : forall xs rhs,
    List.Forall (wellScoped xs) rhs
    -> forall lhs s s' lhs' Ps, findMatchings s lhs rhs = Success1 s' lhs' Ps
      -> forall x, s' x <> None -> s x <> None \/ In x xs.
  Proof.
    induction 1; simpl; intuition idtac.

    injection H; clear H; intros; subst; tauto.

    case_eq (findMatching s lhs x); intros.
    Focus 2.
    rewrite H3 in *; discriminate.
    rewrite H3 in *.
    case_eq (findMatchings NewSub NewLhs l); intros.
    Focus 2.
    rewrite H4 in H1; discriminate.
    rewrite H4 in H1.
    injection H1; clear H1; intros; subst.
    edestruct IHForall; eauto.
    edestruct findMatching_adds; eauto.
  Qed.

  edestruct findMatchings_adds; eauto.
  congruence.
  tauto.
Qed.
