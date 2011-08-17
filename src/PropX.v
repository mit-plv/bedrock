Require Import List.

Set Implicit Arguments.


Section machine.
  Variables pc state : Type.

  Inductive var : list Type -> Type -> Type :=
  | VO : forall T Ts, var (T :: Ts) T
  | VS : forall T Ts T', var Ts T -> var (T' :: Ts) T.

  Implicit Arguments VO [T Ts].
  Implicit Arguments VS [T Ts T'].

  Inductive propX (G : list Type) : Type :=
  | Inj : Prop -> propX G
  | Cptr : pc -> (state -> propX G) -> propX G
  | And : propX G -> propX G -> propX G
  | Or : propX G -> propX G -> propX G
  | Imply : propX G -> propX G -> propX G
  | Forall : forall A, (A -> propX G) -> propX G
  | Exists : forall A, (A -> propX G) -> propX G

  | Var : forall A, var G A -> A -> propX G
  | ForallX : forall A, propX (A :: G) -> propX G
  | ExistsX : forall A, propX (A :: G) -> propX G.

  Implicit Arguments Inj [G].

  Definition PropX := propX nil.

  Fixpoint liftV G T (v : var G T) G' : var (G ++ G') T :=
    match v with
      | VO _ _ => VO
      | VS _ _ _ v' => VS (liftV v' _)
    end.

  Fixpoint lift G (p : propX G) G' : propX (G ++ G') :=
    match p with
      | Inj P => Inj P
      | Cptr i f => Cptr i (fun x => lift (f x) _)
      | And p1 p2 => And (lift p1 _) (lift p2 _)
      | Or p1 p2 => Or (lift p1 _) (lift p2 _)
      | Imply p1 p2 => Imply (lift p1 _) (lift p2 _)
      | Forall _ f => Forall (fun x => lift (f x) _)
      | Exists _ f => Exists (fun x => lift (f x) _)

      | Var _ x v => Var (liftV x _) v
      | ForallX _ p => ForallX (lift p _)
      | ExistsX _ p => ExistsX (lift p _)
    end.

  Fixpoint last (G : list Type) : Type :=
    match G with
      | nil => unit
      | T :: nil => T
      | _ :: G' => last G'
    end.

  Fixpoint eatLast (G : list Type) : list Type :=
    match G with
      | nil => nil
      | _ :: nil => nil
      | x :: G' => x :: eatLast G'
    end.

  Definition varContra T (v : var nil T) T' : T' :=
    match v in var G' _ return match G' with
                                 | nil => T'
                                 | _ :: _ => unit
                               end with
      | VO _ _ => tt
      | _ => tt
    end.

  Definition substMore G T T' : var (eatLast G) T -> var (eatLast (T' :: G)) T :=
    match G with
      | nil => fun v => v
      | T0 :: G' => match G' return var (eatLast (T0 :: G')) T -> var (eatLast (T' :: T0 :: G')) T with
                      | nil => fun v => varContra v _
                      | T1 :: G'' => fun v => VS v
                    end
    end.

  Definition substMoreEq G T T' : var G T -> T = last G -> T = last (T' :: G) :=
    match G with
      | nil => fun v _ => varContra v _
      | T0 :: G' => fun _ Heq => Heq
    end.

  Fixpoint substV G T (v : var G T) : var (eatLast G) T + {T = last G} :=
    match v in var G T return var (eatLast G) T + {T = last G} with
      | VO _ nil => inright _ (refl_equal _)
      | VO _ _ => inleft _ VO
      | VS _ G' _ v' => match substV v' with
                          | inright Heq => inright _ (substMoreEq _ v' Heq)
                          | inleft v'' => inleft _ (substMore _ _ v'')
                        end
    end.

  Fixpoint subst G (p : propX G) (p' : last G -> PropX) : propX (eatLast G) :=
    match p with
      | Inj P => Inj P
      | Cptr i f => Cptr i (fun x => subst (f x) p')
      | And p1 p2 => And (subst p1 p') (subst p2 p')
      | Or p1 p2 => Or (subst p1 p') (subst p2 p')
      | Imply p1 p2 => Imply (subst p1 p') (subst p2 p')
      | Forall _ f => Forall (fun x => subst (f x) p')
      | Exists _ f => Exists (fun x => subst (f x) p')

      | Var _ x v => match substV x with
                       | inleft x' => Var x' v
                       | inright Heq => lift (p' (match Heq in _ = T return T with
                                                    | refl_equal => v
                                                  end)) _
                     end
      | ForallX A p1 => match G return propX (A :: G) -> propX (eatLast (A :: G)) -> propX (eatLast G) with
                          | nil => fun p1 _ => ForallX p1
                          | _ :: _ => fun _ rc => ForallX rc
                        end p1 (subst p1 (match G return (last G -> PropX) -> last (A :: G) -> PropX with
                                            | nil => fun _ _ => Inj True
                                            | _ => fun p' => p'
                                          end p'))
      | ExistsX A p1 => match G return propX (A :: G) -> propX (eatLast (A :: G)) -> propX (eatLast G) with
                          | nil => fun p1 _ => ExistsX p1
                          | _ :: _ => fun _ rc => ExistsX rc
                        end p1 (subst p1 (match G return (last G -> PropX) -> last (A :: G) -> PropX with
                                            | nil => fun _ _ => Inj True
                                            | _ => fun p' => p'
                                          end p'))
    end.

  Definition Subst A (p : propX (A :: nil)) (p' : A -> PropX) : PropX := subst p p'.

  Definition spec := state -> PropX.
  Definition codeSpec := pc -> option spec.

  Section specs.
    Variable specs : codeSpec.

    Inductive valid (G : list PropX) : PropX -> Prop :=
    | Env : forall P,
      In P G
      -> valid G P

    | Inj_I : forall (p : Prop),
      p
      -> valid G (Inj p)

    | Inj_E : forall p Q,
      valid G (Inj p)
      -> (p -> valid G Q)
      -> valid G Q

    | Cptr_I : forall f a,
      specs f = Some (fun x => a x)
      -> valid G (Cptr f a)

    | Cptr_E : forall f a Q,
      valid G (Cptr f a)
      -> (specs f = Some (fun x => a x) -> valid G Q)
      -> valid G Q

    | And_I : forall P Q,
      valid G P
      -> valid G Q
      -> valid G (And P Q)

    | And_E1 : forall P Q,
      valid G (And P Q)
      -> valid G P
    | And_E2 : forall P Q,
      valid G (And P Q)
      -> valid G Q

    | Or_I1 : forall P Q,
      valid G P
      -> valid G (Or P Q)
    | Or_I2 : forall P Q,
      valid G Q
      -> valid G (Or P Q)

    | Or_E : forall P Q R,
      valid G (Or P Q)
      -> valid (P :: G) R
      -> valid (Q :: G) R
      -> valid G R

    | Imply_I : forall P Q,
      valid (P :: G) Q
      -> valid G (Imply P Q)

    | Imply_E : forall P Q,
      valid G (Imply P Q)
      -> valid G P
      -> valid G Q

    | Forall_I : forall A P,
      (forall B : A, valid G (P B))
      -> valid G (Forall P)

    | Forall_E : forall A P (B : A),
      valid G (Forall P)
      -> valid G (P B)

    | Exists_I : forall A P (B : A),
      valid G (P B)
      -> valid G (Exists P)

    | Exists_E : forall A P Q,
      valid G (Exists P)
      -> (forall B : A, valid (P B :: G) Q)
      -> valid G Q

    | ForallX_I : forall A P,
      (forall a : A -> PropX, valid G (Subst P a))
      -> valid G (ForallX P)

    | ExistsX_I : forall A P (a : A -> PropX),
      valid G (Subst P a)
      -> valid G (ExistsX P).

    Inductive normal (G : list PropX) : PropX -> Prop :=
    | Coer : forall P,
      neutral G P
      -> normal G P

    | NoInj_I : forall p : Prop,
      p
      -> normal G (Inj p)

    | NoInj_E : forall p Q,
      neutral G (Inj p)
      -> (p -> normal G Q)
      -> normal G Q

    | NoCptr_I : forall f a,
      specs f = Some (fun x => a x)
      -> normal G (Cptr f a)

    | NoCptr_E : forall f a Q,
      neutral G (Cptr f a)
      -> (specs f = Some (fun x => a x) -> normal G Q)
      -> normal G Q

    | NoAnd_I : forall P Q,
      normal G P
      -> normal G Q
      -> normal G (And P Q)

    | NoOr_I1 : forall P Q,
      normal G P
      -> normal G (Or P Q)
    | NoOr_I2 : forall P Q,
      normal G Q
      -> normal G (Or P Q)

    | NoOr_E : forall P Q R,
      neutral G (Or P Q)
      -> normal (P :: G) R
      -> normal (Q :: G) R
      -> normal G R

    | NoImply_I : forall P Q,
      normal (P :: G) Q
      -> normal G (Imply P Q)

    | NoForall_I : forall A P,
      (forall B : A, normal G (P B))
      -> normal G (Forall P)

    | NoExists_I : forall A P (B : A),
      normal G (P B)
      -> normal G (Exists P)

    | NoExists_E : forall A P Q,
      neutral G (Exists P)
      -> (forall B : A, normal (P B :: G) Q)
      -> normal G Q

    | NoForallX_I : forall A P,
      (forall a : A -> PropX, normal G (Subst P a))
      -> normal G (ForallX P)

    | NoExistsX_I : forall A P (a : A -> PropX),
      normal G (Subst P a)
      -> normal G (ExistsX P)

    with neutral (G : list PropX) : PropX -> Prop :=
    | NoEnv : forall P,
      In P G
      -> neutral G P

    | NoAnd_E1 : forall P Q,
      neutral G (And P Q)
      -> neutral G P
    | NoAnd_E2 : forall P Q,
      neutral G (And P Q)
      -> neutral G Q

    | NoImply_E : forall P Q,
      neutral G (Imply P Q)
      -> normal G P
      -> neutral G Q

    | NoForall_E : forall A P (B : A),
      neutral G (Forall P)
      -> neutral G (P B).

    Scheme normal_min := Minimality for normal Sort Prop
    with neutral_min := Minimality for neutral Sort Prop.

    Combined Scheme normal_neutral_min from normal_min, neutral_min.

    Inductive normalP (G : list PropX) : PropX -> Prop :=
    | NopCoer : forall P,
      neutralP G P
      -> normalP G P

    | NopInj_I : forall p : Prop,
      p
      -> normalP G (Inj p)

    | NopInj_E : forall p Q,
      neutralP G (Inj p)
      -> (p -> normalP G Q)
      -> normalP G Q

    | NopCptr_I : forall f a,
      specs f = Some (fun x => a x)
      -> normalP G (Cptr f a)

    | NopCptr_E : forall f a Q,
      neutralP G (Cptr f a)
      -> (specs f = Some (fun x => a x) -> normalP G Q)
      -> normalP G Q

    | NopAnd_I : forall P Q,
      normalP G P
      -> normalP G Q
      -> normalP G (And P Q)

    | NopOr_I1 : forall P Q,
      normalP G P
      -> normalP G (Or P Q)
    | NopOr_I2 : forall P Q,
      normalP G Q
      -> normalP G (Or P Q)

    | NopOr_E : forall P Q R,
      neutralP G (Or P Q)
      -> normalP (P :: G) R
      -> normalP (Q :: G) R
      -> normalP G R

    | NopImply_I : forall P Q,
      normalP (P :: G) Q
      -> normalP G (Imply P Q)

    | NopForall_I : forall A P,
      (forall B : A, normalP G (P B))
      -> normalP G (Forall P)

    | NopExists_I : forall A P (B : A),
      normalP G (P B)
      -> normalP G (Exists P)

    | NopExists_E : forall A P Q,
      neutralP G (Exists P)
      -> (forall B : A, normalP (P B :: G) Q)
      -> normalP G Q

    | NopForallX_I : forall A P,
      (forall a : A -> PropX, normalP G (Subst P a))
      -> normalP G (ForallX P)

    | NopExistsX_I : forall A P (a : A -> PropX),
      normalP G (Subst P a)
      -> normalP G (ExistsX P)

    with neutralP (G : list PropX) : PropX -> Prop :=
    | Coer' : forall P,
      normalP G P
      -> neutralP G P

    | NopEnv : forall P,
      In P G
      -> neutralP G P

    | NopAnd_E1 : forall P Q,
      neutralP G (And P Q)
      -> neutralP G P
    | NopAnd_E2 : forall P Q,
      neutralP G (And P Q)
      -> neutralP G Q

    | NopImply_E : forall P Q,
      neutralP G (Imply P Q)
      -> normalP G P
      -> neutralP G Q

    | NopForall_E : forall A P (B : A),
      neutralP G (Forall P)
      -> neutralP G (P B).

    Scheme normalP_min := Minimality for normalP Sort Prop
    with neutralP_min := Minimality for neutralP Sort Prop.

    Combined Scheme normalP_neutralP_min from normalP_min, neutralP_min.


    Inductive seq (G : list PropX) : PropX -> Prop :=
    | Inj_R : forall p : Prop,
      p
      -> seq G (Inj p)

    | Inj_L : forall (p : Prop) Q,
      In (Inj p) G
      -> (p -> seq G Q)
      -> seq G Q

    | Cptr_R : forall f a,
      specs f = Some (fun x => a x)
      -> seq G (Cptr f a)

    | Cptr_L : forall f a Q,
      In (Cptr f a) G
      -> (specs f = Some (fun x => a x) -> seq G Q)
      -> seq G Q

    | And_R : forall P Q,
      seq G P
      -> seq G Q
      -> seq G (And P Q)

    | And_L1 : forall P Q R,
      In (And P Q) G
      -> seq (P :: G) R
      -> seq G R
    | And_L2 : forall P Q R,
      In (And P Q) G
      -> seq (Q :: G) R
      -> seq G R

    | Or_R1 : forall P Q,
      seq G P
      -> seq G (Or P Q)
    | Or_R2 : forall P Q,
      seq G Q
      -> seq G (Or P Q)

    | Or_L : forall P Q R,
      In (Or P Q) G
      -> seq (P :: G) R
      -> seq (Q :: G) R
      -> seq G R

    | Imply_R : forall P Q,
      seq (P :: G) Q
      -> seq G (Imply P Q)

    | Imply_L : forall P Q R,
      In (Imply P Q) G
      -> seq G P
      -> seq (Q :: G) R
      -> seq G R

    | Init : forall P,
      In P G
      -> seq G P

    | Forall_R : forall A P,
      (forall B : A, seq G (P B))
      -> seq G (Forall P)

    | Forall_L : forall A P (B : A) Q,
      In (Forall P) G
      -> seq (P B :: G) Q
      -> seq G Q

    | Exists_R : forall A P (B : A),
      seq G (P B)
      -> seq G (Exists P)

    | Exists_L : forall A P Q,
      In (Exists P) G
      -> (forall B : A, seq (P B :: G) Q)
      -> seq G Q

    | ForallX_R : forall A P,
      (forall a : A -> PropX, seq G (Subst P a))
      -> seq G (ForallX P)

    | ExistsX_R : forall A P (a : A -> PropX),
      seq G (Subst P a)
      -> seq G (ExistsX P).


    Inductive seqP (G : list PropX) : PropX -> Prop :=
    | Cut : forall P Q,
      seqP G P
      -> seqP (P :: G) Q
      -> seqP G Q

    | CInj_R : forall p : Prop,
      p
      -> seqP G (Inj p)

    | CInj_L : forall (p : Prop) Q,
      In (Inj p) G
      -> (p -> seqP G Q)
      -> seqP G Q

    | CCptr_R : forall f a,
      specs f = Some (fun x => a x)
      -> seqP G (Cptr f a)

    | CCptr_L : forall f a Q,
      In (Cptr f a) G
      -> (specs f = Some (fun x => a x) -> seqP G Q)
      -> seqP G Q

    | CAnd_R : forall P Q,
      seqP G P
      -> seqP G Q
      -> seqP G (And P Q)

    | CAnd_L1 : forall P Q R,
      In (And P Q) G
      -> seqP (P :: G) R
      -> seqP G R
    | CAnd_L2 : forall P Q R,
      In (And P Q) G
      -> seqP (Q :: G) R
      -> seqP G R

    | COr_R1 : forall P Q,
      seqP G P
      -> seqP G (Or P Q)
    | COr_R2 : forall P Q,
      seqP G Q
      -> seqP G (Or P Q)

    | COr_L : forall P Q R,
      In (Or P Q) G
      -> seqP (P :: G) R
      -> seqP (Q :: G) R
      -> seqP G R

    | CImply_R : forall P Q,
      seqP (P :: G) Q
      -> seqP G (Imply P Q)

    | CImply_L : forall P Q R,
      In (Imply P Q) G
      -> seqP G P
      -> seqP (Q :: G) R
      -> seqP G R

    | CInit : forall P,
      In P G
      -> seqP G P

    | CForall_R : forall A P,
      (forall B : A, seqP G (P B))
      -> seqP G (Forall P)

    | CForall_L : forall A P (B : A) Q,
      In (Forall P) G
      -> seqP (P B :: G) Q
      -> seqP G Q

    | CExists_R : forall A P (B : A),
      seqP G (P B)
      -> seqP G (Exists P)

    | CExists_L : forall A P Q,
      In (Exists P) G
      -> (forall B : A, seqP (P B :: G) Q)
      -> seqP G Q

    | CForallX_R : forall A P,
      (forall a : A -> PropX, seqP G (Subst P a))
      -> seqP G (ForallX P)

    | CExistsX_R : forall A P (a : A -> PropX),
      seqP G (Subst P a)
      -> seqP G (ExistsX P).

    Hint Constructors valid normal neutral normalP neutralP seqP.


    Theorem normal_neutral_sound : forall G,
      (forall P, normal G P -> valid G P)
      /\ (forall P, neutral G P -> valid G P).
      apply normal_neutral_min; eauto.
    Qed.

    Theorem normalP_neutralP_sound : forall G,
      (forall P, normalP G P -> valid G P)
      /\ (forall P, neutralP G P -> valid G P).
      apply normalP_neutralP_min; eauto.
    Qed.

    Theorem normalP_complete : forall G P, valid G P -> normalP G P.
      induction 1; eauto.
    Qed.

    Theorem neutralP_complete : forall G P, valid G P -> neutralP G P.
      induction 1; eauto.
    Qed.

    Hint Extern 1 (In _ _) => simpl; tauto.

    Hint Extern 3 (incl _ _) =>
      let x := fresh "x" in intro x;
        repeat match goal with
                 | [ H : incl _ _ |- _ ] => generalize (H x); clear H
               end; simpl; intuition (subst; assumption).

    Theorem incl_cons : forall A x (G G' : list A),
      incl G G'
      -> incl (x :: G) (x :: G').
      auto.
    Qed.

    Hint Resolve incl_cons.

    Lemma normal_neutral_weaken : forall G,
      (forall Q, normal G Q
      -> (forall G', incl G G'
        -> normal G' Q))
    /\ (forall Q, neutral G Q
      -> (forall G', incl G G'
        -> neutral G' Q)).
      apply normal_neutral_min; eauto; eauto 7.
    Qed.

    Lemma normal_weaken : forall G Q, normal G Q
      -> forall G', incl G G'
        -> normal G' Q.
      generalize normal_neutral_weaken; firstorder.
    Qed.

    Lemma neutral_weaken : forall G Q, neutral G Q
      -> forall G', incl G G'
        -> neutral G' Q.
      generalize normal_neutral_weaken; firstorder.
    Qed.

    Hint Extern 1 (normal _ _) =>
      match goal with
        | [ H : normal _ _ |- _ ] => apply (normal_weaken H)
      end.

    Hint Extern 1 (neutral _ _) =>
      match goal with
        | [ H : neutral _ _ |- _ ] => apply (neutral_weaken H)
      end.

    Lemma incl_cons2 : forall A (P P0 : A) G G0,
      incl G (P :: G0)
      -> incl (P0 :: G) (P :: P0 :: G0).
      auto.
    Qed.

    Hint Immediate incl_cons2.

    Lemma In_incl : forall A (ls1 ls2 : list A) x,
      In x ls1
      -> incl ls1 ls2
      -> In x ls2.
      intuition.
    Qed.

    Hint Resolve In_incl.

    Lemma subst_Env : forall P0 G P G0,
      In P0 G
      -> incl G (P :: G0)
      -> neutral G0 P
      -> neutral G0 P0.
      intros ? ? ? ? H1 H2; generalize (H2 _ H1); simpl; intuition; subst; auto.
    Qed.

    Hint Immediate subst_Env.

    Lemma normal_neutral_subst : forall P PG, (forall Q, normal PG Q
      -> (forall G, incl PG (P :: G)
        -> neutral G P
        -> normal G Q))
    /\ (forall Q, neutral PG Q
      -> (forall G, incl PG (P :: G)
        -> neutral G P
        -> neutral G Q)).
      intro; apply normal_neutral_min; eauto; eauto 7.
    Qed.

    Lemma normal_subst : forall G P Q,
      normal (P :: G) Q
      -> neutral G P
      -> normal G Q.
      generalize normal_neutral_subst; firstorder.
    Qed.

    Hint Resolve normal_subst.

    Theorem seq_sound : forall G P, seq G P -> normal G P.
      induction 1; eauto.
    Qed.

    Hint Resolve Init Inj_R Cptr_R And_R Or_R1 Or_R2 Imply_R Forall_R Exists_R ForallX_R ExistsX_R.

    Ltac ready con := eapply con; solve [ eauto ].

    Ltac doLeft := intros;
      ready Inj_L || ready Cptr_L || ready And_L1 || ready And_L2 || ready Or_L
        || ready Imply_L || ready Forall_L || ready Exists_L.

    Theorem seq_weaken : forall G p, seq G p
      -> forall G', incl G G'
        -> seq G' p.
      induction 1; eauto; doLeft.
    Qed.

    Section seq_complete.
      Hint Resolve seq_weaken.

      Theorem seq_complete : forall G,
        (forall P, normal G P
          -> seq G P)
        /\ (forall P, neutral G P
          -> forall Q, seq (P :: G) Q
            -> seq G Q).
        apply normal_neutral_min; eauto; intros;
          match goal with
            | [ H : _ |- _ ] => apply H; doLeft
          end.
      Qed.
    End seq_complete.

    Hint Extern 2 (seq _ _) =>
      match goal with
        | [ H : seq _ _ |- _ ] => apply (seq_weaken H)
        | [ H : forall x : ?A, seq _ _, B : ?A |- _ ] => apply (seq_weaken (H B))
      end.

    Lemma normalP_neutralP_weaken : forall G,
      (forall Q, normalP G Q
        -> (forall G', incl G G'
          -> normalP G' Q))
      /\ (forall Q, neutralP G Q
        -> (forall G', incl G G'
          -> neutralP G' Q)).
      apply normalP_neutralP_min; eauto; eauto 7.
    Qed.

    Lemma normalP_weaken : forall G Q, normalP G Q
      -> forall G', incl G G'
        -> normalP G' Q.
      generalize normalP_neutralP_weaken; firstorder.
    Qed.

    Lemma neutralP_weaken : forall G Q, neutralP G Q
      -> forall G', incl G G'
        -> neutralP G' Q.
      generalize normalP_neutralP_weaken; firstorder.
    Qed.

    Hint Extern 1 (normalP _ _) =>
      match goal with
        | [ H : normalP _ _ |- _ ] => apply (normalP_weaken H)
      end.

    Hint Extern 1 (neutralP _ _) =>
      match goal with
        | [ H : neutralP _ _ |- _ ] => apply (neutralP_weaken H)
      end.

    Lemma subst_EnvP : forall P0 G P G0,
      In P0 G
      -> incl G (P :: G0)
      -> neutralP G0 P
      -> neutralP G0 P0.
      intros ? ? ? ? H1 H2; generalize (H2 _ H1); simpl; intuition; subst; auto.
    Qed.

    Hint Immediate subst_EnvP.

    Lemma normalP_neutralP_subst : forall P PG,
      (forall Q, normalP PG Q
        -> (forall G, incl PG (P :: G)
          -> neutralP G P
          -> normalP G Q))
      /\ (forall Q, neutralP PG Q
        -> (forall G, incl PG (P :: G)
          -> neutralP G P
          -> neutralP G Q)).
      intro; apply normalP_neutralP_min; eauto; intros; eapply NopOr_E; eauto.
    Qed.

    Lemma normalP_subst : forall G P Q,
      normalP (P :: G) Q
      -> neutralP G P
      -> normalP G Q.
      generalize normalP_neutralP_subst; firstorder.
    Qed.

    Hint Resolve normalP_subst.

    Theorem seqP_sound : forall G P, seqP G P -> normalP G P.
      induction 1; eauto.
    Qed.

    Theorem seqP_weaken : forall G p, seqP G p
      -> forall G', incl G G'
        -> seqP G' p.
      induction 1; eauto.
    Qed.

    Hint Resolve seqP_weaken.

    Theorem seqP_complete : forall G,
      (forall P, normalP G P
        -> seqP G P)
      /\ (forall P, neutralP G P
        -> forall Q, seqP (P :: G) Q
          -> seqP G Q).
      apply normalP_neutralP_min; eauto.
    Qed.

    Hint Extern 0 (seq ?G0 ?R) =>
      match goal with
        | [ _ : seq (?P :: _) R, IH : forall PG Q0, _ -> forall G, incl _ (?P :: _) -> _ |- _ ] =>
          apply IH with (P :: G0);
            repeat match goal with
                     | [ IH : forall PG Q0, _ -> forall G, incl _ (_ :: _) -> _ |- _ ] => clear IH
                   end
      end.

    Inductive head : Type := HInj | HCptr | HAnd | HOr | HImply
    | HForall | HExists | HVar | HForallX | HExistsX.

    Definition headOf G (p : propX G) : head :=
      match p with
        | Inj _ => HInj
        | Cptr _ _ => HCptr
        | And _ _ => HAnd
        | Or _ _ => HOr
        | Imply _ _ => HImply
        | Forall _ _ => HForall
        | Exists _ _ => HExists
        | Var _ _ _ => HVar
        | ForallX _ _ => HForallX
        | ExistsX _ _ => HExistsX
      end.

    Ltac equate E E' := let H := fresh "H" in assert (H : E = E') by reflexivity; clear H.

    Ltac intuitionPlus := try tauto; repeat match goal with
                                              | [ H : ex _ |- _ ] => destruct H
                                              | [ H : _ /\ _ |- _ ] => destruct H
                                            end; solve [ eauto ].

    Hint Extern 1 (seq _ _) =>
      match goal with
        | _ => match goal with
                 | [ _ : match ?E with Inj _ => _ | Cptr _ _ => _ | And _ _ => _ | Or _ _ => _ | Imply _ _ => _
                           | Forall _ _ => _ | Exists _ _ => _ | Var _ _ _ => _ | ForallX _ _ => _ | ExistsX _ _ => _ end |- _ ] =>
                 destruct E; intuitionPlus
               end
        | [ H : _ |- _ ] => eapply H; [ match goal with
                                          | [ _ : match ?E with Inj _ => _ | Cptr _ _ => _ | And _ _ => _ | Or _ _ => _ | Imply _ _ => _
                                                    | Forall _ _ => _ | Exists _ _ => _ | Var _ _ _ => _ | ForallX _ _ => _ | ExistsX _ _ => _ end
                                              |- match ?E' with Inj _ => _ | Cptr _ _ => _ | And _ _ => _ | Or _ _ => _ | Imply _ _ => _
                                                   | Forall _ _ => _ | Exists _ _ => _ | Var _ _ _ => _ | ForallX _ _ => _ | ExistsX _ _ => _ end ] =>
                                          equate E' E; destruct E; intuitionPlus
                                        end | solve [ eauto ] ]
      end.

    Ltac innerPredicative := let GG := fresh "GG" in induction 1; intro GG; destruct GG; intuition;
        try match goal with
              | [ H1 : incl _ _, H2 : In _ _ |- _ ] => generalize (H1 _ H2); simpl; intuition; subst; intuition
            end;
        repeat match goal with
                 | [ H : _ -> forall GG : list Type, _ |- _ ] => specialize (fun pf => H pf nil); simpl in H
                 | [ H : forall GG : list Type, _ |- _ ] => specialize (H nil); simpl in H
               end;
        doLeft || solve [ eauto ]
          || (try match goal with
                    | [ H : ex _ |- _ ] => destruct H
                  end;
          match goal with
            | [ H : _, B : _, G0 : _, P : _ |- _ ] => 
              apply H with B (P B :: G0); eauto;
                match goal with
                  | [ IH : _ |- _ ] => solve [ apply IH with (Forall P); eauto
                    | apply IH with B (Exists P); eauto
                    | apply IH with (ForallX P); eauto
                    | apply IH with B (ExistsX P); eauto ]
                end
          end).

    Lemma inner_Forall : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG as GG0 return (propX GG0 -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | Forall A0 P =>
                  (forall B : A0, seq G (P B)) /\
                  (forall (a : A0) (PG0 : list PropX) (Q0 : PropX),
                    seq PG0 Q0 ->
                    forall G0 : list (propX nil),
                      incl PG0 (P a :: G0) -> seq G0 (P a) -> seq G0 Q0)
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
      innerPredicative.
    Qed.

    Lemma inner_Exists : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG as GG0 return (propX GG0 -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | Exists A0 P =>
                  (exists B, seq G (P B)) /\
                  (forall (a : A0) (PG0 : list PropX) (Q0 : PropX),
                    seq PG0 Q0 ->
                    forall G0 : list (propX nil),
                      incl PG0 (P a :: G0) -> seq G0 (P a) -> seq G0 Q0)
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
      innerPredicative.
    Qed.

    Lemma inner_ForallX : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG as GG0 return (propX GG0 -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | ForallX A0 P =>
                  forall B, seq G (Subst P B)
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
      innerPredicative.
    Qed.

    Lemma inner_ExistsX : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG as GG0 return (propX GG0 -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | ExistsX A0 P =>
                  exists B, seq G (Subst P B)
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
      innerPredicative.
    Qed.

    Ltac outerPredicative :=
      induction 2; intuition;
        try match goal with
              | [ |- match ?E with Inj _ => _ | Cptr _ _ => _ | And _ _ => _ | Or _ _ => _ | Imply _ _ => _
                       | Forall _ _ => _ | Exists _ _ => _ | Var _ _ _ => _ | ForallX _ _ => _ | ExistsX _ _ => _ end ] =>
              destruct E; intuition; doLeft
            end;
        match goal with
          | [ H : _, _ : incl _ (?P :: _) |- _ ] => solve [ specialize (inner_Forall H P); eauto
            | specialize (inner_Exists H P); eauto
            | specialize (inner_ForallX H P); eauto
            | specialize (inner_ExistsX H P); eauto ]
        end.

    Lemma outer_Forall : forall PG Q, seq PG Q
      -> forall G P, seq G P ->
        match P with
          | Forall A p =>
            (forall (a : A) (PG0 : list PropX) (Q0 : PropX),
              seq PG0 Q0 ->
              forall G0 : list (propX nil),
                incl PG0 (p a :: G0) -> seq G0 (p a) -> seq G0 Q0) ->
            incl PG (P :: G) -> seq G Q
          | _ => True
        end.
      outerPredicative.
    Qed.

    Lemma outer_Exists : forall PG Q, seq PG Q
      -> forall G P, seq G P ->
        match P with
          | Exists A p =>
            (forall (a : A) (PG0 : list PropX) (Q0 : PropX),
              seq PG0 Q0 ->
              forall G0 : list (propX nil),
                incl PG0 (p a :: G0) -> seq G0 (p a) -> seq G0 Q0) ->
            incl PG (P :: G) -> seq G Q
          | _ => True
        end.
      outerPredicative.
    Qed.

    Lemma outer_ForallX : forall PG Q, seq PG Q
      -> forall G P, seq G P ->
        match P with
          | ForallX A p =>
            incl PG (P :: G) -> seq G Q
          | _ => True
        end.
      outerPredicative.
    Qed.

    Lemma outer_ExistsX : forall PG Q, seq PG Q
      -> forall G P, seq G P ->
        match P with
          | ExistsX A p =>
            incl PG (P :: G) -> seq G Q
          | _ => True
        end.
      outerPredicative.
    Qed.

    Ltac inver := try discriminate;
      repeat match goal with
               | [ H : _ = ?E |- _ ] => 
                 match E with
                   | Some _ => fail 1
                   | _ =>
                     injection H; clear H; intros; repeat match goal with
                                                            | [ H : ?X = ?Y |- _ ] => subst X || subst Y
                                                          end
                 end
             end.

    Lemma cut_admissibility' : forall GG (P : propX GG),
      match GG return propX GG -> Prop with
        | _ :: _ => fun _ => True
        | nil => fun P => forall PG Q, seq PG Q
          -> forall G, incl PG (P :: G)
          -> seq G P
          -> seq G Q
      end P.
      induction P; destruct G; intuition;
        match goal with
          | [ H1 : _, H2 : _ |- _ ] => solve [ specialize (outer_Forall H1 H2); eauto
            | specialize (outer_Exists H1 H2); eauto
            | specialize (outer_ForallX H1 H2); eauto
            | specialize (outer_ExistsX H1 H2); eauto ]
          | _ =>
            match goal with
              | [ x : var nil _ |- _ ] => inversion x
              | [ _ : incl ?PG (_ :: ?G) |- _ ] =>
                match goal with
                  | [ H : seq G ?P |- _ ] =>
                    generalize dependent H; remember P; induction 1; intros; subst
                end; try solve [ eapply seq_weaken; [ eassumption | eauto ] ];
                instantiate
            end;
            match goal with
              | [ _ : incl ?PG (_ :: ?G) |- _ ] =>
                try (progress inver; repeat match goal with
                                              | [ IH : _ = _ -> incl _ _ -> seq _ _ |- _ ] => clear IH
                                              | [ IH : forall x, _ = _ -> incl _ _ -> seq _ _ |- _ ] => clear IH
                                            end;
                instantiate;
                  match goal with
                    | [ H : seq PG _ |- _ ] => generalize dependent G; generalize dependent H; induction 1; intros;
                      try match goal with
                            | [ H1 : incl _ _, H2 : In _ _ |- _ ] => generalize (H1 _ H2); simpl; intuition; subst
                          end; inver
                  end)
            end; (doLeft || eauto);
            instantiate;
              repeat match goal with
                       | [ H : seq (?P :: ?G) ?R |- seq ?G0 _ ] =>
                         match G with
                           | G0 => fail 1
                           | _ => assert (seq (P :: G0) R); [ eauto | clear H ]
                         end
                     end; eauto
        end.
    Qed.

    Theorem cut_admissibility : forall P G Q,
      seq G P
      -> seq (P :: G) Q
      -> seq G Q.
      intros; eapply (@cut_admissibility' nil); eauto.
    Qed.

    Hint Resolve cut_admissibility.

    Theorem cut_elimination : forall G P,
      seqP G P
      -> seq G P.
      induction 1; eauto; doLeft.
    Qed.

    Lemma seqP_complete' : forall G P, normalP G P
      -> seqP G P.
      generalize seqP_complete; firstorder.
    Qed.

    Theorem normalization : forall G P,
      valid G P
      -> normal G P.
      intros; apply seq_sound; apply cut_elimination; apply seqP_complete';
        apply normalP_complete; assumption.
    Qed.

    Definition interp := valid nil.

    Lemma neutral_contra' : forall G P, neutral G P
      -> G = nil
      -> False.
      induction 1; simpl in *; intros; subst; intuition.
    Qed.

    Lemma neutral_contra : forall P, neutral nil P
      -> False.
      intros; eapply neutral_contra'; eauto.
    Qed.

    Hint Immediate neutral_contra.

    Hint Unfold interp.

    Theorem normal_sound : forall G P, normal G P -> valid G P.
      generalize normal_neutral_sound; firstorder.
    Qed.

    Hint Immediate normal_sound.

    Ltac sound := intros;
      match goal with
        | [ H : interp ?E |- _ ] =>
          match goal with
            | [ x : _ |- _ ] => match x with
                                  | E => fail 2
                                end
            | _ =>
              generalize (normalization H); clear H; intro H; inversion H; clear H; subst;
                try solve [ elimtype False; eauto ]; inver; intuition; subst; auto
          end
      end.

    Theorem Inj_sound : forall p, interp (Inj p) -> p.
      sound.
    Qed.

    Theorem Cptr_sound : forall f a, interp (Cptr f a)
      -> specs f = Some (fun x => a x).
      sound.
    Qed.

    Theorem And_sound : forall P Q, interp (And P Q)
      -> interp P /\ interp Q.
      sound.
    Qed.

    Theorem Or_sound : forall P Q, interp (Or P Q)
      -> interp P \/ interp Q.
      sound.
    Qed.

    Theorem Imply_sound : forall P Q, interp (Imply P Q)
      -> interp P -> interp Q.
      intros ? ? H; generalize (normalization H); eauto.
    Qed.

    Ltac soundQ := let H := fresh "H" in intros ? H; apply normalization in H; inversion H;
      try solve [ elimtype False; eauto ]; inver; intuition; subst; auto.

    Lemma Forall_sound' : forall P, interp P
      -> match P with
           | Forall _ P => forall x, interp (P x)
           | _ => True
         end.
      soundQ.
    Qed.

    Theorem Forall_sound : forall A (P : A -> _), interp (Forall P)
      -> forall x, interp (P x).
      intros ? ? H; apply Forall_sound' in H; auto.
    Qed.      

    Lemma Exists_sound' : forall P, interp P
      -> match P with
           | Exists _ P => exists x, interp (P x)
           | _ => True
         end.
      soundQ; eauto.
    Qed.

    Theorem Exists_sound : forall A (P : A -> _), interp (Exists P)
      -> exists x, interp (P x).
      intros ? ? H; apply Exists_sound' in H; auto.
    Qed.

    Lemma ForallX_sound' : forall P, interp P
      -> match P with
           | ForallX _ P => forall f, interp (Subst P f)
           | _ => True
         end.
      soundQ.
    Qed.

    Theorem ForallX_sound : forall A (P : propX (A :: nil)), interp (ForallX P)
      -> forall f, interp (Subst P f).
      intros ? ? H; apply ForallX_sound' in H; auto.
    Qed.

    Lemma ExistsX_sound' : forall P, interp P
      -> match P with
           | ExistsX _ P => exists f, interp (Subst P f)
           | _ => True
         end.
      soundQ; eauto.
    Qed.

    Theorem ExistsX_sound : forall A (P : propX (A :: nil)), interp (ExistsX P)
      -> exists f, interp (Subst P f).
      intros ? ? H; apply ExistsX_sound' in H; auto.
    Qed.
  End specs.
End machine.

Implicit Arguments VO [T Ts].
Implicit Arguments VS [T Ts T'].

Implicit Arguments Inj [pc state G].
Notation "[< p >]" := (Inj p) : PropX_scope.
Infix "/\" := And : PropX_scope.
Infix "\/" := Or : PropX_scope.
Infix "-->" := Imply (at level 86, right associativity) : PropX_scope.

Notation "'Al' x , P" := (Forall (fun x => P)) (x ident, at level 89) : PropX_scope.
Notation "'Al' x : A , P" := (Forall (fun x : A => P)) (x ident, at level 89) : PropX_scope.
Notation "'Ex' x , P" := (Exists (fun x => P)) (x ident, at level 89) : PropX_scope.
Notation "'Ex' x : A , P" := (Exists (fun x : A => P)) (x ident, at level 89) : PropX_scope.

Notation "'AlX' , P" := (ForallX P) (x ident, at level 89) : PropX_scope.
Notation "'AlX' : A , P" := (ForallX (A := A) P) (x ident, at level 89) : PropX_scope.
Notation "'ExX' , P" := (ExistsX P) (x ident, at level 89) : PropX_scope.
Notation "'ExX' : A , P" := (ExistsX (A := A) P) (x ident, at level 89) : PropX_scope.

Implicit Arguments Var [pc state G A].
Infix "@" := Var (at level 75) : PropX_scope.

Delimit Scope PropX_scope with PropX.
Bind Scope PropX_scope with PropX propX.

Notation "^[ p ]" := (lift p _) : PropX_scope.

Arguments Scope interp [type_scope type_scope _ PropX_scope].
Arguments Scope valid [type_scope type_scope _ PropX_scope PropX_scope].
