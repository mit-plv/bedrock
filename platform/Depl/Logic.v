Require Import AutoSep.

Set Implicit Arguments.


(** Dynamically typed packages *)
Record dyn := Dyn {
  Ty : Type;
  Va : Ty
}.

(** Type synonym for variables *)
Definition fo_var := string.

(** Environments assigning values to variables *)
Definition fo_env := fo_var -> dyn.

(** Syntax of expressions within predicates *)
Inductive expr :=
| Var (x : fo_var)
| Lift (f : fo_env -> dyn).

(** Meanings of expressions *)
Definition exprD (e : expr) : fo_env -> dyn :=
  match e with
    | Var x => fun E => E x
    | Lift f => f
  end.

Definition fo_empty : fo_env := fun _ => Dyn tt.

(** Setting a value in a valuation *)
Definition fo_set (E : fo_env) (x : fo_var) (v : dyn) : fo_env := 
  fun y => if string_dec y x then v else E y.

(** Environments for higher-order variables *)
Definition ho_var := string.
Definition ho_env (G : list Type) := ho_var -> list dyn -> hpropB G.

(** Separation logic assertions *)
Inductive pred :=
| Pure (P : fo_env -> Prop)
| Star (p1 p2 : pred)
| Exists (x : fo_var) (p1 : pred)
| Named (X : ho_var) (es : list expr).

(** Meanings of assertions *)
Fixpoint predD (p : pred) G (hE : ho_env G) (fE : fo_env) : hpropB G :=
  match p with
    | Pure P => injB _ (P fE)
    | Star p1 p2 => starB (predD p1 hE fE) (predD p2 hE fE)
    | Exists x p1 => exB (fun y => predD p1 hE (fo_set fE x y))
    | Named X es => hE X (map (fun e => exprD e fE) es)
  end.

(** Assertion normal forms *)
Record normal := {
  NQuants : list fo_var;
  NPure : option (fo_env -> Prop);
  NImpure : list pred
}.

(** ...and their meanings *)

Definition propX := propX W (settings * state).
Definition PropX := propX nil.

Fixpoint addQuants (qs : list fo_var) G (f : fo_env -> hpropB G) (fE : fo_env) : hpropB G :=
  match qs with
    | nil => f fE
    | x :: qs' => exB (fun y => addQuants qs' f (fo_set fE x y))
  end.

Definition normalD (n : normal) G (hE : ho_env G) (fE : fo_env) : hpropB G :=
  addQuants (NQuants n) (fun fE =>
    fold_left (fun hp p => starB (predD p hE fE) hp) (NImpure n)
    (match NPure n with
       | None => empB _
       | Some P => injB _ (P fE)
     end)) fE.

(** Normalization *)
Fixpoint normalize (p : pred) : normal :=
  match p with
    | Pure P => {| NQuants := nil; NPure := Some P; NImpure := nil |}
    | Star p1 p2 =>
      let n1 := normalize p1 in
      let n2 := normalize p2 in
        {| NQuants := NQuants n1 ++ NQuants n2;
          NPure := match NPure n1, NPure n2 with
                     | Some P1, Some P2 => Some (fun Ge => P1 Ge /\ P2 Ge)
                     | None, v => v
                     | v, None => v
                   end;
          NImpure := NImpure n1 ++ NImpure n2 |}
    | Exists x p1 =>
      let n1 := normalize p1 in
        {| NQuants := x :: NQuants n1;
          NPure := NPure n1;
          NImpure := NImpure n1 |}
    | Named X es =>
      {| NQuants := nil;
        NPure := None;
        NImpure := p :: nil |}
  end.

(** Before normalizing, we'll want to ensure that all bound variables are distinct. *)

Fixpoint notInList (x : string) (xs : list string) : bool :=
  match xs with
    | nil => true
    | x' :: xs' => if string_dec x' x then false else notInList x xs'
  end.

Fixpoint notsInList (xs1 xs2 : list string) : bool :=
  match xs1 with
    | nil => true
    | x :: xs1' => if notInList x xs2 then notsInList xs1' xs2 else false
  end.

Fixpoint boundVars (p : pred) : option (list fo_var) :=
  match p with
    | Pure _ => Some nil
    | Star p1 p2 =>
      match boundVars p1, boundVars p2 with
        | Some xs1, Some xs2 =>
          if notsInList xs1 xs2 then Some (xs1 ++ xs2) else None
        | _, _ => None
      end
    | Exists x p1 =>
      match boundVars p1 with
        | None => None
        | Some xs => if notInList x xs then Some (x :: xs) else None
      end
    | Named _ _ => Some nil
  end.

(** * Soundness of normalization *)

Lemma Substs_Exists_fwd : forall specs P A G s (Q : A -> propX G),
  interp specs (PropX.Exists (fun x => Substs s (Q x)) ---> P)
  -> interp specs (Substs s (PropX.Exists Q) ---> P).
Proof.
  induction s; simpl; intuition.
Qed.

Lemma Substs_Exists_bwd : forall specs P A G s (Q : A -> propX G),
  interp specs (P ---> PropX.Exists (fun x => Substs s (Q x)))
  -> interp specs (P ---> Substs s (PropX.Exists Q)).
Proof.
  induction s; simpl; intuition.
Qed.

Fixpoint wellScoped (xs : list fo_var) (p : pred) : Prop :=
  match p with
    | Pure f => forall fE fE', (forall x, In x xs -> fE x = fE' x) -> f fE = f fE'
    | Star p1 p2 => wellScoped xs p1 /\ wellScoped xs p2
    | Exists x p1 => wellScoped (x :: xs) p1
    | Named _ es => forall fE fE', (forall x, In x xs -> fE x = fE' x)
      -> forall e, In e es -> exprD e fE = exprD e fE'
  end.

Definition SubstsH G (s : subs _ _ G) (p : hpropB G) : HProp :=
  fun stn sm => Substs s (p stn sm).

Lemma SubstsH_inj_fwd : forall G (s : subs _ _ G) P,
  SubstsH s (injB _ P) ===> injB _ P.
Proof.
  unfold SubstsH; intros; do 2 intro.
  intros.
  unfold injB, inj.
  repeat rewrite Substs_And.
  repeat rewrite Substs_Inj.
  apply Imply_refl.
Qed.

Lemma SubstsH_inj_bwd : forall G (s : subs _ _ G) P,
  injB _ P ===> SubstsH s (injB _ P).
Proof.
  unfold SubstsH; intros; do 2 intro.
  intros.
  unfold injB, inj.
  repeat rewrite Substs_And.
  repeat rewrite Substs_Inj.
  apply Imply_refl.
Qed.

Lemma SubstsH_star_fwd : forall G (s : subs _ _ G) P Q,
  SubstsH s (starB P Q) ===> starB (SubstsH s P) (SubstsH s Q).
Proof.
  unfold SubstsH; intros; do 2 intro.
  intros.
  unfold starB, star.
  apply Substs_Exists_fwd; apply existsL; intro sm1.
  apply Substs_Exists_fwd; apply existsL; intro sm2.
  apply existsR with sm1.
  apply existsR with sm2.
  repeat rewrite Substs_And.
  repeat rewrite Substs_Inj.
  apply Imply_refl.
Qed.

Lemma SubstsH_star_bwd : forall G (s : subs _ _ G) P Q,
  starB (SubstsH s P) (SubstsH s Q) ===> SubstsH s (starB P Q).
Proof.
  unfold SubstsH; intros; do 2 intro.
  intros.
  unfold starB, star.
  apply existsL; intro sm1.
  apply existsL; intro sm2.
  apply Substs_Exists_bwd; apply existsR with sm1.
  apply Substs_Exists_bwd; apply existsR with sm2.
  repeat rewrite Substs_And.
  repeat rewrite Substs_Inj.
  apply Imply_refl.
Qed.

Lemma SubstsH_emp_fwd : forall G (s : subs _ _ G),
  SubstsH s (emp _ _) ===> emp _ _.
Proof.
  unfold SubstsH, emp, inj, injB; intros; do 3 intro.
  repeat rewrite Substs_And.
  repeat rewrite Substs_Inj.
  apply Imply_refl.
Qed.

Lemma SubstsH_emp_bwd : forall G (s : subs _ _ G),
   emp _ _ ===> SubstsH s (emp _ _).
Proof.
  unfold SubstsH, emp, inj, injB; intros; do 3 intro.
  repeat rewrite Substs_And.
  repeat rewrite Substs_Inj.
  apply Imply_refl.
Qed.

Lemma SubstsH_ex_fwd : forall G (s : subs _ _ G) A (P : A -> _),
  SubstsH s (exB P) ===> exB (fun x => SubstsH s (P x)).
Proof.
  unfold SubstsH; intros; do 3 intro.
  intros.
  apply Substs_Exists_fwd; apply existsL; intro it.
  apply existsR with it.
  apply Imply_refl.
Qed.

Lemma SubstsH_ex_bwd : forall G (s : subs _ _ G) A (P : A -> _),
  exB (fun x => SubstsH s (P x)) ===> SubstsH s (exB P).
Proof.
  unfold SubstsH; intros; do 3 intro.
  intros.
  apply existsL; intro it.
  apply Substs_Exists_bwd; apply existsR with it.
  apply Imply_refl.
Qed.

Theorem normalize_sound_fwd : forall p fvs bvs G (hE : ho_env G) fE s,
  wellScoped fvs p
  -> boundVars p = Some bvs
  -> (forall x, In x fvs -> ~In x bvs)
  -> SubstsH s (predD p hE fE) ===> SubstsH s (normalD (normalize p) hE fE).
Proof.
  induction p; simpl.

  unfold normalD; simpl; intros.
  apply Himp_refl.

  Focus 3.
  unfold normalD; simpl; intros.
  eapply Himp_trans; [ | apply SubstsH_star_bwd ].
  eapply Himp_trans; [ | apply Himp_star_comm ].
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply SubstsH_emp_bwd | apply Himp_refl ] ].
  apply Himp_star_Emp'.

  Focus 2.
  unfold normalD; simpl; intros.
  eapply Himp_trans; [ apply SubstsH_ex_fwd | ].
  eapply Himp_trans; [ | apply SubstsH_ex_bwd ].
  apply Himp_ex; intro.
  case_eq (boundVars p); [ intros ? Heq | intro Heq ]; rewrite Heq in *; try discriminate.
  case_eq (notInList x l); intro Heq'; rewrite Heq' in *; try discriminate.
  injection H0; clear H0; intros; subst.
  
  Lemma In_notInList : forall x xs,
    In x xs
    -> notInList x xs = true
    -> False.
  Proof.
    induction xs; simpl; intuition.
    destruct (string_dec a x); subst; try discriminate; tauto.
    destruct (string_dec a x); subst; try discriminate; tauto.
  Qed.

  Local Hint Immediate In_notInList.

  eapply IHp; eauto.
  intro x0; specialize (H1 x0); simpl in *; intuition (subst; eauto).

  intros.
  case_eq (boundVars p1); [ intros ? Heq1 | intro Heq1 ]; rewrite Heq1 in *; try discriminate.
  case_eq (boundVars p2); [ intros ? Heq2 | intro Heq2 ]; rewrite Heq2 in *; try discriminate.
  case_eq (notsInList l l0); intro Heq3; rewrite Heq3 in *; try discriminate.
  injection H0; clear H0; intros; intuition subst.
  eapply Himp_trans; [ apply SubstsH_star_fwd | ].
  unfold normalD; simpl.
  
  Lemma addQuants_app_bwd : forall G (s : subs _ _ G) qs2 f qs1 fE,
    SubstsH s (addQuants qs1 (addQuants qs2 f) fE) ===> SubstsH s (addQuants (qs1 ++ qs2) f fE).
  Proof.
    induction qs1; simpl; intuition.
    apply Himp_refl.

    eapply Himp_trans; [ apply SubstsH_ex_fwd | ].
    eapply Himp_trans; [ | apply SubstsH_ex_bwd ].
    apply Himp_ex; eauto.
  Qed.

  eapply Himp_trans; [ | apply addQuants_app_bwd ].

  Lemma addQuants_monotone : forall G (s : subs _ _ G) f g qs fE,
    (forall fE', (forall x, ~In x qs -> fE' x = fE x)
      -> SubstsH s (f fE') ===> SubstsH s (g fE'))
    -> SubstsH s (addQuants qs f fE) ===> SubstsH s (addQuants qs g fE).
  Proof.
    induction qs; simpl; intuition.
    eapply Himp_trans; [ apply SubstsH_ex_fwd | ].
    eapply Himp_trans; [ | apply SubstsH_ex_bwd ].
    apply Himp_ex; intro.
    apply IHqs; intros.
    apply H; intros.
    rewrite H0; eauto.
    unfold fo_set.
    destruct (string_dec x a); subst; auto.
    exfalso; eauto.
  Qed.

  eapply Himp_trans; [ | apply addQuants_monotone ].

  Lemma addQuants_push_bwd' : forall G (s : subs _ _ G) f p2 qs fE,
    SubstsH s (addQuants qs f fE) * SubstsH s p2 ===>
    SubstsH s (addQuants qs (fun fE' : fo_env => f fE' * p2) fE).
  Proof.
    induction qs; simpl; intuition.

    apply SubstsH_star_bwd.

    eapply Himp_trans; [ apply Himp_star_frame; [ apply SubstsH_ex_fwd | apply Himp_refl ] | ].
    eapply Himp_trans; [ | apply SubstsH_ex_bwd ].
    eapply Himp_trans; [ apply Himp_ex_star | ].
    apply Himp_ex; auto.
  Qed.

  Lemma addQuants_push_bwd : forall G (s : subs _ _ G) p1 f qs fE p2,
    SubstsH s p1 ===> SubstsH s (addQuants qs f fE)
    -> SubstsH s p1 * SubstsH s p2 ===>
      SubstsH s (addQuants qs (fun fE' => f fE' * p2) fE).
  Proof.
    induction qs; simpl; intuition.

    eapply Himp_trans; [ | apply SubstsH_star_bwd ].
    apply Himp_star_frame; auto; apply Himp_refl.

    eapply Himp_trans; [ apply Himp_star_frame; [ apply H | apply Himp_refl ] | ]; clear H.
    eapply Himp_trans; [ apply Himp_star_frame; [ apply SubstsH_ex_fwd | apply Himp_refl ] | ].
    eapply Himp_trans; [ | apply SubstsH_ex_bwd ].
    eapply Himp_trans; [ apply Himp_ex_star | ].
    apply Himp_ex; intro.
    apply addQuants_push_bwd'.
  Qed.

  apply addQuants_push_bwd.
  eapply IHp1; eauto using in_or_app.
  simpl; intros.
  eapply Himp_trans; [ apply SubstsH_star_fwd | ].
  eapply Himp_trans; [ | apply addQuants_monotone ].
  eapply Himp_trans; [ apply Himp_star_comm | ].
  apply addQuants_push_bwd.
  
  Lemma normalize_boundVars : forall x p xs,
    boundVars p = Some xs
    -> In x (NQuants (normalize p))
    -> In x xs.
  Proof.
    induction p; simpl; intuition.

    case_eq (boundVars p1); [ intros ? Heq1 | intro Heq1 ]; rewrite Heq1 in *; try discriminate.
    case_eq (boundVars p2); [ intros ? Heq2 | intro Heq2 ]; rewrite Heq2 in *; try discriminate.
    case_eq (notsInList l l0); intro Heq3; rewrite Heq3 in *; try discriminate.
    injection H; clear H; intros; subst.
    apply in_app_or in H0; intuition.

    subst.
    case_eq (boundVars p); [ intros ? Heq1 | intro Heq1 ]; rewrite Heq1 in *; try discriminate.
    case_eq (notInList x l); intro Heq3; rewrite Heq3 in *; try discriminate.
    injection H; clear H; intros; subst.
    simpl; tauto.

    case_eq (boundVars p); [ intros ? Heq1 | intro Heq1 ]; rewrite Heq1 in *; try discriminate.
    case_eq (notInList x0 l); intro Heq3; rewrite Heq3 in *; try discriminate.
    injection H; clear H; intros; subst.
    simpl; eauto.
  Qed.

  Lemma weaken_predD : forall G (s : subs _ _ G) hE p xs fE fE',
    wellScoped xs p
    -> (forall x, In x xs -> fE x = fE' x)
    -> SubstsH s (predD p hE fE) ===> SubstsH s (predD p hE fE').
  Proof.
    induction p; simpl; intuition.

    erewrite H by eassumption.
    apply Himp_refl.

    eapply Himp_trans; [ apply SubstsH_star_fwd | ].
    eapply Himp_trans; [ | apply SubstsH_star_bwd ].
    apply Himp_star_frame; eauto.

    eapply Himp_trans; [ apply SubstsH_ex_fwd | ].
    eapply Himp_trans; [ | apply SubstsH_ex_bwd ].
    apply Himp_ex; intro.
    eapply IHp; eauto.
    simpl; intuition subst.
    unfold fo_set; destruct (string_dec x0 x0); tauto.
    unfold fo_set; destruct (string_dec x0 x); intuition.

    Lemma weaken_exprsD : forall fE fE' es,
      (forall e, In e es -> exprD e fE = exprD e fE')
      -> map (fun e  => exprD e fE) es = map (fun e : expr => exprD e fE') es.
    Proof.
      induction es; simpl; intuition idtac.
      f_equal; eauto.
    Qed.

    erewrite weaken_exprsD by (eapply H; eauto).
    apply Himp_refl.
  Qed.

  eapply Himp_trans; [ eapply weaken_predD | eapply IHp2 ]; simpl; eauto.
  intros.
  symmetry; apply H; intros; intro.
  eapply normalize_boundVars in H4.
  2: eauto.
  eauto using in_or_app.
  eauto using in_or_app.
  simpl; intros.

  Lemma split_star : forall P1 P2 G (s : subs _ _ G) hE fE ps2 ps1,
    SubstsH s (fold_left (fun hp p => (predD p hE fE * hp)%Sep)
      ps1 match P1 with
            | Some P => [|P fE|]%Sep
            | None => Emp%Sep
          end)
      * SubstsH s (fold_left (fun hp p => (predD p hE fE * hp)%Sep)
        ps2 match P2 with
            | Some P => [|P fE|]%Sep
            | None => Emp%Sep
            end)
      ===> SubstsH s (fold_left (fun hp p => (predD p hE fE * hp)%Sep)
          (ps1 ++ ps2)
          match
            match P1 with
              | Some P1 =>
                match P2 with
                  | Some P2 => Some (fun Ge => P1 Ge /\ P2 Ge)%type
                  | None => Some P1
                end
              | None => P2
            end
            with
            | Some P => [|P fE|]%Sep
            | None => Emp%Sep
          end).
  Proof.
    induction ps1; simpl; intuition.

    destruct P1.
    eapply Himp_trans; [ apply Himp_star_frame; [ apply SubstsH_inj_fwd | apply Himp_refl ] | ].
    apply Himp_star_pure_c; intro.
    
    Lemma multistar_weaken' : forall G (s : subs _ _ G) (f f' : hpropB G -> pred -> hpropB G),
      (forall a a', SubstsH s a ===> SubstsH s a'
        -> forall p, SubstsH s (f a p) ===> SubstsH s (f' a' p))
      -> forall ps acc acc',
        SubstsH s acc ===> SubstsH s acc'
        -> SubstsH s (fold_left f ps acc)
        ===> SubstsH s (fold_left f' ps acc').
    Proof.
      induction ps; simpl; intuition.
    Qed.

    Lemma multistar_weaken : forall G (s : subs _ _ G) hE fE ps acc acc',
      SubstsH s acc ===> SubstsH s acc'
      -> SubstsH s (fold_left (fun hp p => predD p hE fE * hp) ps acc)
      ===> SubstsH s (fold_left (fun hp p => predD p hE fE * hp) ps acc').
    Proof.
      intros; apply multistar_weaken'; auto.
      intros.
      eapply Himp_trans; [ apply SubstsH_star_fwd | ].
      eapply Himp_trans; [ | apply SubstsH_star_bwd ].
      apply Himp_star_frame; auto; apply Himp_refl.
    Qed.

    apply multistar_weaken.
    destruct P2.
    eapply Himp_trans; [ apply SubstsH_inj_fwd | ].
    eapply Himp_trans; [ | apply SubstsH_inj_bwd ].
    eapply Himp_trans; [ | apply Himp_star_Emp ].
    eapply Himp_trans; [ apply Himp_star_Emp' | ].
    eapply Himp_trans; [ apply Himp_star_comm | ].
    apply Himp_star_pure_c; intro.
    eapply Himp_trans; [ | apply Himp_star_comm ].
    apply Himp_star_pure_cc; auto; apply Himp_refl.
    eapply Himp_trans; [ apply SubstsH_emp_fwd | ].
    eapply Himp_trans; [ | apply SubstsH_inj_bwd ].
    eapply Himp_trans; [ | apply Himp_star_Emp ].
    eapply Himp_trans; [ | apply Himp_star_comm ].
    apply Himp_star_pure_cc; auto; apply Himp_refl.
    eapply Himp_trans; [ apply Himp_star_frame; [ apply SubstsH_emp_fwd | apply Himp_refl ] | ].
    apply Himp_star_Emp.

    Lemma star_out_fwd : forall G (s : subs _ _ G) hE fE P ps Q,
      SubstsH s (fold_left (fun hp p => (predD p hE fE * hp)%Sep) ps (star P Q))
      ===> SubstsH s (star P (fold_left (fun hp p => (predD p hE fE * hp)%Sep) ps Q)).
    Proof.
      induction ps; simpl; intuition.

      apply Himp_refl.

      eapply Himp_trans; [ apply multistar_weaken | ]; auto.
      simpl; intros.
      eapply Himp_trans; [ apply SubstsH_star_fwd | ].
      eapply Himp_trans; [ | apply SubstsH_star_bwd ].
      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply SubstsH_star_fwd ] | ].
      eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl | apply SubstsH_star_bwd ] ].
      eapply Himp_trans; [ apply Himp_star_assoc' | ].      
      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_star_comm | apply Himp_refl ] | ].
      apply Himp_star_assoc.
    Qed.

    Lemma star_out_bwd : forall G (s : subs _ _ G) hE fE P ps Q,
      SubstsH s (star P (fold_left (fun hp p => (predD p hE fE * hp)%Sep) ps Q))
      ===> SubstsH s (fold_left (fun hp p => (predD p hE fE * hp)%Sep) ps (star P Q)).
    Proof.
      induction ps; simpl; intuition.

      apply Himp_refl.

      eapply Himp_trans; [ | apply multistar_weaken ]; auto.
      eapply Himp_trans; [ apply SubstsH_star_fwd | ].
      eapply Himp_trans; [ | apply SubstsH_star_bwd ].
      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply SubstsH_star_fwd ] | ].
      eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl | apply SubstsH_star_bwd ] ].
      eapply Himp_trans; [ apply Himp_star_assoc' | ].      
      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_star_comm | apply Himp_refl ] | ].
      apply Himp_star_assoc.
    Qed.

    eapply Himp_trans; [ | apply star_out_bwd ].
    eapply Himp_trans; [ | apply SubstsH_star_bwd ].
    eapply Himp_trans; [ apply Himp_star_frame; [ apply star_out_fwd | apply Himp_refl ] | ].
    eapply Himp_trans; [ apply Himp_star_frame; [ apply SubstsH_star_fwd | apply Himp_refl ] | ].
    eapply Himp_trans; [ apply Himp_star_assoc | ].
    apply Himp_star_frame; auto.
    apply Himp_refl.
  Qed.

  eapply Himp_trans; [ apply SubstsH_star_fwd | ].
  eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply multistar_weaken ] | ].
  instantiate (1 := match NPure (normalize p1) with
                      | Some P => [|P fE'0|]
                      | None => Emp
                    end%Sep).

  Lemma wellScoped_NPure : forall p fvs bvs, wellScoped fvs p
    -> boundVars p = Some bvs
    -> (forall x, In x fvs -> ~In x bvs)
    -> forall fE fE', (forall x, In x fvs \/ In x bvs -> fE x = fE' x)
      -> match NPure (normalize p) with
           | None => True
           | Some P => P fE = P fE'
         end.
  Proof.
    induction p; simpl; intuition.

    case_eq (boundVars p1); [ intros ? Heq1 | intro Heq1 ]; rewrite Heq1 in *; try discriminate.
    case_eq (boundVars p2); [ intros ? Heq2 | intro Heq2 ]; rewrite Heq2 in *; try discriminate.
    case_eq (notsInList l l0); intro Heq3; rewrite Heq3 in *; try discriminate.
    injection H0; clear H0; intros; subst.
    assert (HIn1 : forall x, In x fvs -> In x l -> False) by eauto using in_or_app.
    assert (HIn2 : forall x, In x fvs -> In x l0 -> False) by eauto using in_or_app.
    assert (H'1 : forall x, In x fvs \/ In x l -> fE x = fE' x) by intuition eauto using in_or_app.
    assert (H'2 : forall x, In x fvs \/ In x l0 -> fE x = fE' x) by intuition eauto using in_or_app.
    specialize (IHp1 _ _ H2 eq_refl HIn1 _ _ H'1).
    specialize (IHp2 _ _ H3 eq_refl HIn2 _ _ H'2).
    destruct (NPure (normalize p1)), (NPure (normalize p2)); congruence.
    
    case_eq (boundVars p); [ intros ? Heq1 | intro Heq1 ]; rewrite Heq1 in *; try discriminate.
    case_eq (notInList x l); intro Heq3; rewrite Heq3 in *; try discriminate.
    injection H0; clear H0; intros; subst.
    eapply IHp; eauto.
    simpl in *; intuition (subst; eauto).
    simpl in *; intuition (subst; eauto).
  Qed.

  eapply wellScoped_NPure in H2.
  destruct (NPure (normalize p1)).
  rewrite H2.
  apply Himp_refl.
  apply Himp_refl.
  eauto.
  eauto using in_or_app.
  intuition eauto using in_or_app.
  symmetry; apply H0; intros.
  eapply normalize_boundVars in H4.
  2: eauto.
  eauto using in_or_app.
  symmetry; apply H0; intros.
  eapply normalize_boundVars in H4.
  2: eauto.

  Lemma notsInList_true : forall x ls2 ls1,
    notsInList ls1 ls2 = true
    -> In x ls1
    -> In x ls2
    -> False.
  Proof.
    induction ls1; simpl; intuition.
    subst.
    generalize (In_notInList _ _ H1).
    destruct (notInList x ls2); intuition congruence.
    generalize (In_notInList a ls2).
    destruct (notInList a ls2); intuition.
  Qed.

  eauto using notsInList_true.

  Lemma multistar_weaken'' : forall G (s : subs _ _ G) (f f' : hpropB G -> pred -> hpropB G),
    forall ps,
      List.Forall (fun p => forall a a', SubstsH s a ===> SubstsH s a'
        -> SubstsH s (f a p) ===> SubstsH s (f' a' p)) ps
      -> forall acc acc', SubstsH s acc ===> SubstsH s acc'
        -> SubstsH s (fold_left f ps acc)
        ===> SubstsH s (fold_left f' ps acc').
  Proof.
    induction 1; simpl; intuition.
  Qed.

  eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply multistar_weaken'' ] | ].
  2: apply Himp_refl.
  2: instantiate (1 := (fun hp p => predD p hE fE'0 * hp)%Sep).
  simpl.
  apply Forall_forall; intros.
  eapply Himp_trans; [ apply SubstsH_star_fwd | ].
  eapply Himp_trans; [ | apply SubstsH_star_bwd ].
  apply Himp_star_frame; auto.

  Lemma NImpure_wellScoped : forall G (hE : ho_env G) x p bvs fvs,
    boundVars p = Some bvs
    -> wellScoped fvs p
    -> In x (NImpure (normalize p))
    -> forall fE fE', (forall x, In x bvs \/ In x fvs -> fE x = fE' x)
      -> predD x hE fE = predD x hE fE'.
  Proof.
    induction p; simpl; intuition idtac.

    case_eq (boundVars p1); [ intros ? Heq1 | intro Heq1 ]; rewrite Heq1 in *; try discriminate.
    case_eq (boundVars p2); [ intros ? Heq2 | intro Heq2 ]; rewrite Heq2 in *; try discriminate.
    case_eq (notsInList l l0); intro Heq3; rewrite Heq3 in *; try discriminate.
    injection H; clear H; intros; subst.
    apply in_app_or in H1; intuition idtac.
    eapply IHp1; intuition eauto using in_or_app.
    eapply IHp2; intuition eauto using in_or_app.

    case_eq (boundVars p); [ intros ? Heq1 | intro Heq1 ]; rewrite Heq1 in *; try discriminate.
    case_eq (notInList x0 l); intro Heq3; rewrite Heq3 in *; try discriminate.
    injection H; clear H; intros; subst.
    simpl in *.
    eapply IHp; intuition eauto using in_or_app.
    simpl in *; intuition eauto using in_or_app.

    subst.
    simpl.
    f_equal.
    apply weaken_exprsD; eauto.
  Qed.

  erewrite NImpure_wellScoped; try apply H4 || apply Himp_refl; eauto.
  intuition eauto using in_or_app.
  symmetry; apply H0.
  intros.
  eapply normalize_boundVars in H6; eauto using notsInList_true.
  symmetry; apply H0.
  intros.
  eapply normalize_boundVars in H6.
  2: eauto.
  eauto using in_or_app.
  eapply Himp_trans; [ apply Himp_star_comm | ].
  apply split_star.
Qed.

Theorem normalize_sound_bwd : forall p fvs bvs G (hE : ho_env G) fE s,
  wellScoped fvs p
  -> boundVars p = Some bvs
  -> (forall x, In x fvs -> ~In x bvs)
  -> SubstsH s (normalD (normalize p) hE fE) ===> SubstsH s (predD p hE fE).
Proof.
  induction p; simpl.

  unfold normalD; simpl; intros.
  apply Himp_refl.

  Focus 3.
  unfold normalD; simpl; intros.
  eapply Himp_trans; [ apply SubstsH_star_fwd | ].
  eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply SubstsH_emp_fwd ] | ].
  eapply Himp_trans; [ apply Himp_star_comm | ].
  apply Himp_star_Emp.

  Focus 2.
  unfold normalD; simpl; intros.
  eapply Himp_trans; [ apply SubstsH_ex_fwd | ].
  eapply Himp_trans; [ | apply SubstsH_ex_bwd ].
  apply Himp_ex; intro.
  case_eq (boundVars p); [ intros ? Heq | intro Heq ]; rewrite Heq in *; try discriminate.
  case_eq (notInList x l); intro Heq'; rewrite Heq' in *; try discriminate.
  injection H0; clear H0; intros; subst.
  eapply IHp; eauto.
  intro x0; specialize (H1 x0); simpl in *; intuition (subst; eauto).

  intros.
  case_eq (boundVars p1); [ intros ? Heq1 | intro Heq1 ]; rewrite Heq1 in *; try discriminate.
  case_eq (boundVars p2); [ intros ? Heq2 | intro Heq2 ]; rewrite Heq2 in *; try discriminate.
  case_eq (notsInList l l0); intro Heq3; rewrite Heq3 in *; try discriminate.
  injection H0; clear H0; intros; intuition subst.
  eapply Himp_trans; [ | apply SubstsH_star_bwd ].
  unfold normalD; simpl.
  
  Lemma addQuants_app_fwd : forall G (s : subs _ _ G) qs2 f qs1 fE,
    SubstsH s (addQuants (qs1 ++ qs2) f fE) ===> SubstsH s (addQuants qs1 (addQuants qs2 f) fE).
  Proof.
    induction qs1; simpl; intuition.
    apply Himp_refl.

    eapply Himp_trans; [ apply SubstsH_ex_fwd | ].
    eapply Himp_trans; [ | apply SubstsH_ex_bwd ].
    apply Himp_ex; eauto.
  Qed.

  eapply Himp_trans; [ apply addQuants_app_fwd | ].
  eapply Himp_trans; [ apply addQuants_monotone | ].
  Focus 2.

  Lemma addQuants_push_fwd' : forall G (s : subs _ _ G) f p2 qs fE,
    SubstsH s (addQuants qs (fun fE' : fo_env => f fE' * p2) fE) ===>
    SubstsH s (addQuants qs f fE) * SubstsH s p2.
  Proof.
    induction qs; simpl; intuition.

    apply SubstsH_star_fwd.

    eapply Himp_trans; [ | apply Himp_star_frame; [ apply SubstsH_ex_bwd | apply Himp_refl ] ].
    eapply Himp_trans; [ apply SubstsH_ex_fwd | ].
    apply Himp'_ex; intro.
    eapply Himp_trans; [ apply IHqs | ].
    apply Himp_star_frame.
    apply Himp_ex_c; exists x; apply Himp_refl.
    apply Himp_refl.
  Qed.

  Lemma addQuants_push_fwd : forall G (s : subs _ _ G) p1 f qs fE p2,
    SubstsH s (addQuants qs f fE) ===> SubstsH s p1
    -> SubstsH s (addQuants qs (fun fE' => f fE' * p2) fE) ===>
    SubstsH s p1 * SubstsH s p2.
  Proof.
    induction qs; simpl; intuition.

    eapply Himp_trans; [ apply SubstsH_star_fwd | ].
    apply Himp_star_frame; auto; apply Himp_refl.

    eapply Himp_trans; [ apply SubstsH_ex_fwd | ].
    apply Himp'_ex; intro.
    apply IHqs.
    eapply Himp_trans; [ | apply H ].
    eapply Himp_trans; [ | apply SubstsH_ex_bwd ].
    apply Himp_ex_c; eexists; apply Himp_refl.
  Qed.

  apply addQuants_push_fwd.
  eapply IHp1; eauto using in_or_app.
  simpl; intros.
  eapply Himp_trans; [ | apply SubstsH_star_bwd ].
  eapply Himp_trans; [ apply addQuants_monotone | ].
  Focus 2.
  eapply Himp_trans; [ | apply Himp_star_comm ].
  apply addQuants_push_fwd.
  eapply Himp_trans; [ eapply IHp2 | eapply weaken_predD ]; simpl; eauto using in_or_app.
  intros.
  apply H; intros; intro.
  eapply normalize_boundVars in H4.
  2: eauto.
  eauto using in_or_app.
  simpl; intros.

  Lemma join_star : forall P1 P2 G (s : subs _ _ G) hE fE ps2 ps1,
    SubstsH s (fold_left (fun hp p => (predD p hE fE * hp)%Sep)
      (ps1 ++ ps2)
      match
        match P1 with
          | Some P1 =>
            match P2 with
              | Some P2 => Some (fun Ge => P1 Ge /\ P2 Ge)%type
              | None => Some P1
            end
          | None => P2
        end
        with
        | Some P => [|P fE|]%Sep
        | None => Emp%Sep
      end) ===>
    SubstsH s (fold_left (fun hp p => (predD p hE fE * hp)%Sep)
      ps1 match P1 with
            | Some P => [|P fE|]%Sep
            | None => Emp%Sep
          end)
    * SubstsH s (fold_left (fun hp p => (predD p hE fE * hp)%Sep)
      ps2 match P2 with
            | Some P => [|P fE|]%Sep
            | None => Emp%Sep
          end).
  Proof.
    induction ps1; simpl; intuition.

    destruct P1.
    eapply Himp_trans; [ | apply Himp_star_frame; [ apply SubstsH_inj_bwd | apply Himp_refl ] ].
    eapply Himp_trans; [ apply multistar_weaken | ].
    instantiate (1 := ([|P fE|] *
      match
        match P2 with
          | Some P0 => Some (fun Ge : fo_env => P Ge /\ P0 Ge)
          | None => Some P
        end with
        | Some P0 => [|P0 fE|]
        | None => Emp
      end)%Sep).
    destruct P2.
    eapply Himp_trans; [ apply SubstsH_inj_fwd | ].
    eapply Himp_trans; [ | apply SubstsH_star_bwd ].
    eapply Himp_trans; [ | apply Himp_star_frame; apply SubstsH_inj_bwd ].
    eapply Himp_trans; [ apply Himp_star_Emp' | ].
    eapply Himp_trans; [ apply Himp_star_comm | ].
    apply Himp_star_pure_c; intro.
    eapply Himp_trans; [ apply Himp_star_Emp' | ].
    apply Himp_star_frame.
    eapply Himp_trans; [ | apply Himp_star_Emp ].
    eapply Himp_trans; [ | apply Himp_star_comm ].
    apply Himp_star_pure_cc; apply Himp_refl || tauto.
    eapply Himp_trans; [ | apply Himp_star_Emp ].
    eapply Himp_trans; [ | apply Himp_star_comm ].
    apply Himp_star_pure_cc; apply Himp_refl || tauto.
    eapply Himp_trans; [ apply SubstsH_inj_fwd | ].
    eapply Himp_trans; [ | apply SubstsH_star_bwd ].
    eapply Himp_trans; [ | apply Himp_star_frame; apply SubstsH_inj_bwd ].    
    eapply Himp_trans; [ apply Himp_star_Emp' | ].
    eapply Himp_trans; [ apply Himp_star_comm | ].
    apply Himp_star_pure_c; intro.    
    eapply Himp_trans; [ apply Himp_star_Emp' | ].
    apply Himp_star_frame.
    eapply Himp_trans; [ | apply Himp_star_Emp ].
    eapply Himp_trans; [ | apply Himp_star_comm ].
    apply Himp_star_pure_cc; apply Himp_refl || tauto.
    eapply Himp_trans; [ | apply Himp_star_Emp ].
    eapply Himp_trans; [ | apply Himp_star_comm ].
    apply Himp_star_pure_cc; apply Himp_refl || tauto.
    eapply Himp_trans; [ apply star_out_fwd | ].
    eapply Himp_trans; [ apply SubstsH_star_fwd | ].
    apply Himp_star_frame.
    eapply Himp_trans; [ apply SubstsH_inj_fwd | ].
    apply Himp_refl.
    destruct P2; apply multistar_weaken.
    eapply Himp_trans; [ apply SubstsH_inj_fwd | ].
    eapply Himp_trans; [ | apply SubstsH_inj_bwd ].
    eapply Himp_trans; [ apply Himp_star_Emp' | ].
    eapply Himp_trans; [ apply Himp_star_comm | ].
    apply Himp_star_pure_c; intro.
    eapply Himp_trans; [ | apply Himp_star_Emp ].
    eapply Himp_trans; [ | apply Himp_star_comm ].
    apply Himp_star_pure_cc; apply Himp_refl || tauto.
    eapply Himp_trans; [ apply SubstsH_inj_fwd | ].
    eapply Himp_trans; [ | apply SubstsH_inj_bwd ].
    eapply Himp_trans; [ apply Himp_star_Emp' | ].
    eapply Himp_trans; [ apply Himp_star_comm | ].
    apply Himp_star_pure_c; intro.
    eapply Himp_trans; [ | apply Himp_star_Emp ].
    eapply Himp_trans; [ | apply Himp_star_comm ].
    apply Himp_star_pure_cc; apply Himp_refl || tauto.
    eapply Himp_trans; [ | eapply Himp_star_frame; [ apply SubstsH_emp_bwd | apply Himp_refl ] ].
    apply Himp_star_Emp'.

    eapply Himp_trans; [ apply star_out_fwd | ].
    eapply Himp_trans; [ | apply Himp_star_frame; [ apply star_out_bwd | apply Himp_refl ] ].
    eapply Himp_trans; [ | apply Himp_star_frame; [ apply SubstsH_star_bwd | apply Himp_refl ] ].
    eapply Himp_trans; [ | apply Himp_star_assoc' ].
    eapply Himp_trans; [ apply SubstsH_star_fwd | ].
    apply Himp_star_frame.
    apply Himp_refl.
    eauto.
  Qed.

  eapply Himp_trans; [ | apply SubstsH_star_bwd ].
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl | apply multistar_weaken ] ].
  Focus 2.
  instantiate (1 := match NPure (normalize p1) with
                      | Some P => [|P fE'0|]
                      | None => Emp
                    end%Sep).
  eapply wellScoped_NPure in H2.
  destruct (NPure (normalize p1)).
  rewrite H2.
  apply Himp_refl.
  apply Himp_refl.
  eauto.
  eauto using in_or_app.
  intuition eauto using in_or_app.
  apply H0; intros.
  eapply normalize_boundVars in H4.
  2: eauto.
  eauto using in_or_app.
  apply H0; intros.
  eapply normalize_boundVars in H4.
  2: eauto.
  eauto using notsInList_true.
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl | apply multistar_weaken'' ] ].
  3: apply Himp_refl.
  instantiate (1 := (fun hp p => predD p hE fE'0 * hp)%Sep).
  Focus 2.
  simpl.
  apply Forall_forall; intros.
  eapply Himp_trans; [ apply SubstsH_star_fwd | ].
  eapply Himp_trans; [ | apply SubstsH_star_bwd ].
  apply Himp_star_frame; auto.
  erewrite NImpure_wellScoped; try apply H4 || apply Himp_refl; eauto.
  intuition eauto using in_or_app.
  apply H0.
  intros.
  eapply normalize_boundVars in H6; eauto using notsInList_true.
  apply H0.
  intros.
  eapply normalize_boundVars in H6.
  2: eauto.
  eauto using in_or_app.
  eapply Himp_trans; [ | apply Himp_star_comm ].
  apply join_star.
Qed.

Theorem wellScoped_weaken : forall p xs1 xs2,
  wellScoped xs1 p
  -> (forall x, In x xs1 -> In x xs2)
  -> wellScoped xs2 p.
Proof.
  induction p; simpl; intuition eauto.
  eapply IHp; eauto.
  simpl; intuition.
Qed.

Lemma normalize_wellScoped_NImpure' : forall p fvs,
  wellScoped fvs p
  -> List.Forall (wellScoped (NQuants (normalize p) ++ fvs)) (NImpure (normalize p)).
Proof.
  induction p; simpl; intuition.

  apply Folds.Forall_app.
  rewrite <- app_assoc; auto.
  apply IHp1.
  eapply wellScoped_weaken; eauto using in_or_app.
  eapply Forall_weaken; [ | apply IHp2; eauto ].
  intros; eapply wellScoped_weaken; eauto.
  intros ? Hin; eapply in_app_or in Hin; intuition eauto using in_or_app.

  eapply Forall_weaken; [ | apply IHp; eauto ].
  intros; eapply wellScoped_weaken; eauto.
  intros ? Hin; eapply in_app_or in Hin; simpl in *; intuition eauto using in_or_app.
Qed.

Theorem normalize_wellScoped_NImpure : forall p,
  wellScoped nil p
  -> List.Forall (wellScoped (NQuants (normalize p))) (NImpure (normalize p)).
Proof.
  intros; rewrite (app_nil_end (NQuants (normalize p))).
  eauto using normalize_wellScoped_NImpure'.
Qed.
