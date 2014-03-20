(** A theory of algebraic datatypes with associated invariants *)

Require Import AutoSep.

Require Import Depl.Logic.


(** * Syntax of algebraic datatype definitions *)

(** A datatype's rep. predicate takes as argument a single functional-model value in [dyn]. *)

(** One constructor of a datatype *)
Record con := {
  Name : string;
  (* Identifier for this constructor, to use in executable code *)
  Recursive : list string;
  (** Names for the "record fields" that actually exist at runtime,
    * referencing other objects of this same datatype.
    * In [Condition] below, these names refer to the _functional_models_ of the recursive arguments.
    * There's no need to refer to their pointer values. *)
  Nonrecursive : list string;
  (** Names of the remaining fields that don't point to further objects of this datatype.
    * These _do_ get bound to machine-word values. *)
  Condition : pred
  (** Finally, the property describing associated memory resources.
    * It does _not_ describe the transitive conditions imposed by other values of the same algebraic
    * datatype that this node points to.
    * A variable "this" is available to refer to the model of this node. *)
}.

Definition datatype := (string * list con)%type.


(** * Semantics of datatypes *)

(** This type summarizes the shape of a datatype value, for purposes of well-founded recursion. *)
Inductive skeleton :=
| Skeleton (sks : list skeleton).

Section Semantics.
  Open Scope Sep_scope.

  Variable hE : ho_env nil.

  (** We'll represent recursive arguments as pairs of models and pointers.
    * Here are some functions to disentangle them. *)
  Definition addrs : list (dyn * W) -> list W := map (@snd _ _).
  Definition models : list (dyn * W) -> list dyn := map (@fst _ _).

  (** Nonrecursive fields are all [W], but we'll want to convert them to [dyn]. *)
  Definition dynify : list W -> list dyn := map (@Dyn _).

  (** Helpers for building first-order variable environments *)
  Fixpoint make_fo (names : list string) (values : list dyn) (base : fo_env) : fo_env :=
    match names, values with
      | name :: names, valu :: values =>
        fo_set (make_fo names values base) name valu
      | _, _ => base
    end.

  Section children.
    (** Stand-in for the final rep. predicate we define *)
    Variable self : skeleton -> dyn -> W -> HProp.

    (** In the main constructor denotation definition, we will need to iterate over all recursive children,
      * in a way that the termination checker understands.  Here's a helper function for just that. *)
    Fixpoint children (sks : list skeleton) (rs : list (dyn * W)) : HProp :=
      match sks, rs with
        | sk :: sks, r :: rs => self sk (fst r) (snd r) * children sks rs
        | _, _ => Emp
      end.

    Definition conD
      (c : con)             (* Which constructor are we representing? *)
      (tag : W)             (* Which numeric tag has been assigned to it? *)
      (sks : list skeleton) (* Which skeleton goes with this node? *)
      (model : dyn)         (* What functional model was passed to the overall rep. predicate? *)
      (ptr : W)             (* What is the first address used to represent this type? *)
      : HProp :=
      (* There exist values for the recursive and nonrecursive fields... *)
      Ex rs, Ex ns,
        (* Laid out at the appropriate address, we find the tag and arguments. *)
        ptsto32m _ ptr O (tag :: ns ++ addrs rs)
        (* We picked the right number of fields in each category. *)
        * [| length rs = length (Recursive c) |]
        * [| length ns = length (Nonrecursive c) |]
        (* The side condition holds w.r.t. the field values. *)
        * predD (Condition c) hE
        (make_fo ("this" :: Recursive c ++ Nonrecursive c) (model :: models rs ++ dynify ns) fo_empty)
        (* Finally, all child nodes are accounted for. *)
        * children sks rs.
  End children.

  (** Let's focus in on one datatype. *)
  Variable dt : datatype.

  (** The final rep. predicate *)
  Fixpoint datatypeD (sk : skeleton) (model : dyn) (ptr : W) : HProp :=
    match sk with
      | Skeleton sks =>
        (** It turned out to be the [n]th constructor, whose definition is [c]... *)
        Ex n, Ex c, [| nth_error (snd dt) n = Some c |]
          (* ...and this node is sitting in memory where we expect it. *)
          * conD datatypeD c n sks model ptr
    end.
End Semantics.


(** * Normalized datatype definitions *)

Record ncon := {
  NName : string;
  NRecursive : list string;
  NNonrecursive : list string;
  NCondition : normal
}.

Definition ndatatype := (string * list ncon)%type.

Definition normalizeCon (c : con) : ncon := {|
  NName := Name c;
  NRecursive := Recursive c;
  NNonrecursive := Nonrecursive c;
  NCondition := normalize (Condition c)
|}.

Definition normalizeDatatype (dt : datatype) : ndatatype :=
  (fst dt, map normalizeCon (snd dt)).


(** * Functions to construct key formulas related to constructing and deconstructing datatype values *)

(** Multiple substitution for first-order variables, recording where we left off in eating arguments *)
Fixpoint nsubsts (xs : list fo_var) (args : list expr) (n : normal) : normal * list expr :=
  match xs, args with
    | x :: xs', e :: args' => nsubsts xs' args' (nsubst x e n)
    | _, _ => (n, args)
  end.

(** Constructing recursive subgoals for the recursive arguments of a constructor *)
Fixpoint recursives (dtName : string) (xs : list fo_var) (args : list expr) : list pred :=
  match xs, args with
    | x :: xs', e :: args' => Named dtName (Var x :: e :: nil) :: recursives dtName xs' args'
    | _, _ => nil
  end.

(** What chunk of state do we expect to see associated with arguments to a new construction? *)
Definition allocatePre (dtName : string) (c : ncon) (args : list expr) : normal :=
  let (cond, recs) := nsubsts (NNonrecursive c) args (NCondition c) in
  {|
    NQuants := NRecursive c ++ NQuants cond;
    NPure := NPure cond;
    NImpure := recursives dtName (NRecursive c) recs ++ NImpure cond
  |}.

Section allocatePre_sound.
  Variable dt : datatype.
  Variable tag : nat.
  Variable c : con.

  Hypothesis Htag : nth_error (snd dt) tag = Some c.
  (* The constructor we think we're using really is found at the right position in the type defn. *)

  Variable hE : ho_env nil.

  Hypothesis HhE_fwd : forall m p, hE (fst dt) (m :: Dyn p :: nil)
    ===> (Ex sk, datatypeD hE dt sk m p).
  Hypothesis HhE_bwd : forall m p, (Ex sk, datatypeD hE dt sk m p)
    ===> hE (fst dt) (m :: Dyn p :: nil).
  (* The higher-order variable environment is interpreting this datatype's name in the proper way. *)

  Lemma allocatePre_sound' : forall argFvs fvs bvs,
    wellScoped fvs (Condition c)
    -> boundVars (Condition c) = Some bvs
    -> (forall x, In x fvs -> ~In x bvs)
    -> NoDup (Recursive c)
    -> (forall x, In x (Recursive c) -> ~In x bvs)
    -> (forall x, In x (Nonrecursive c) -> ~In x bvs)
    -> (forall x, In x (Recursive c) -> ~In x argFvs)
    -> (forall x, In x (Nonrecursive c) -> ~In x argFvs)
    -> (forall x, In x bvs -> ~In x argFvs)
    -> (forall x, In x argFvs -> In x fvs)
    -> (forall x, In x (Nonrecursive c) -> ~In x (Recursive c))
    -> forall args fE ws, length args = length (Nonrecursive c) + length (Recursive c)
    -> map (fun e => exprD e fE) args = map (@Dyn W) ws
    -> (forall fE1 fE2, (forall x, In x argFvs -> fE1 x = fE2 x)
      -> List.Forall (fun e => exprD e fE1 = exprD e fE2) args)
    -> normalD (allocatePre (fst dt) (normalizeCon c) args) hE fE
    ===> Ex sks, Ex rs, [| length rs = length (Recursive c) |]
    * [| addrs rs = skipn (length (Nonrecursive c)) ws |]
    * children (datatypeD hE dt) sks rs
    * predD (Condition c) hE
    (make_fo (Recursive c ++ Nonrecursive c)
      (models rs ++ dynify (firstn (length (Nonrecursive c)) ws)) fE).
  Proof.
    destruct c; simpl in *.
    clear Htag.
    intros until args; generalize dependent Recursive0; generalize dependent Nonrecursive0;
      generalize dependent Condition0;
        induction args; unfold allocatePre; simpl; intros.

    destruct Nonrecursive0; simpl in *; try discriminate.
    destruct Recursive0; simpl in *; try discriminate.
    apply Himp_ex_c; exists nil.
    apply Himp_ex_c; exists nil.
    simpl.
    do 2 (eapply Himp_trans; [ | apply Himp_star_assoc' ]).
    do 2 (apply Himp_star_pure_cc; auto).
    destruct ws; simpl in *; congruence.
    eapply Himp_trans; [ | apply Himp_star_Emp' ].
    apply addSubstsH.
    eapply normalize_sound_bwd; eauto.
    unfold not in *; eauto.

    destruct Nonrecursive0; simpl in *; intros.

    destruct Recursive0; simpl in *; try discriminate.
    injection H10; clear H10; intros.
    unfold allocatePre in IHargs; simpl in IHargs.
    specialize (IHargs Condition0 H H0 nil); simpl in IHargs; intuition.
    inversion_clear H2.
    specialize (H14 Recursive0); simpl in H14; intuition.
    apply Himp'_ex; fold addQuants; simpl; intro r.
    eapply Himp_trans; [ apply addSubstsH; apply addQuants_monotone | ].
    intros.
    apply star_out_fwd.
    destruct ws; simpl in *; try discriminate.
    injection H11; clear H11; intros.

    Lemma addQuants_push_fwdPlus : forall f p qs fE,
      (forall fE1 fE2, (forall x, ~In x qs -> fE1 x = fE2 x) -> p fE1 = p fE2)
      -> addQuants qs (fun fE' : fo_env => p fE' * f fE') fE ===>
      p fE * addQuants qs f fE.
    Proof.
      induction qs; simpl; intuition.

      apply Himp_refl.

      apply Himp'_ex; intro y.
      eapply Himp_trans; [ apply IHqs; eauto | ].
      apply Himp_star_frame.
      apply Himp_refl'.
      apply H; intros.
      unfold fo_set.
      destruct (string_dec x a); intuition.
      apply Himp_ex_c; exists y; apply Himp_refl.
    Qed.

    eapply Himp_trans; [ apply addQuants_push_fwdPlus | ].
    intros.
    do 2 f_equal.
    apply H16; intro.
    apply in_app_or in H17; intuition eauto using normalize_boundVars.
    f_equal.
    specialize (H12 fE1 fE2).

    Ltac proveHyp H :=
      match type of H with
        | ?P -> _ => assert P; [ | intuition idtac ]
      end.

    proveHyp H12.
    intuition idtac.
    apply H16; intro.
    apply in_app_or in H18; intuition eauto using normalize_boundVars.
    inversion H18; auto.

    simpl.
    assert (Hscoped : forall fE1 fE2,
      (forall x, In x argFvs -> fE1 x = fE2 x) -> List.Forall (fun e => exprD e fE1 = exprD e fE2) args).
    intros.
    specialize (H12 fE1 fE2); intuition idtac.
    inversion H17; auto.

    Theorem map_same : forall A B (f g : A -> B) ls,
      List.Forall (fun x => f x = g x) ls
      -> map f ls = map g ls.
    Proof.
      induction 1; simpl; intuition.
    Qed.

    eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | eapply H2; eauto ] | ]; clear H2.
    erewrite map_same.
    eassumption.
    simpl.
    specialize (H12 (fo_set fE s r) fE).
    proveHyp H12.
    intros; unfold fo_set.
    destruct (string_dec x s); intuition subst.
    exfalso; eauto.
    inversion H16; auto.

    replace (exprD a (fo_set fE s r)) with (exprD a fE).
    rewrite H14.
    eapply Himp_trans; [ apply Himp_star_frame; [ apply HhE_fwd | apply Himp_refl ] | ].
    eapply Himp_trans; [ apply Himp_ex_star | ].
    apply Himp'_ex; intro sk.
    eapply Himp_trans; [ apply Himp_star_comm | ].
    eapply Himp_trans; [ apply Himp_ex_star | ].
    apply Himp'_ex; intro sks.
    eapply Himp_trans; [ apply Himp_ex_star | ].
    apply Himp'_ex; intro rs.
    apply Himp_ex_c; exists (sk :: sks).
    apply Himp_ex_c; exists ((r, w) :: rs).
    simpl.
    rewrite <- app_nil_end.
    unfold fo_set at 2.
    destruct (string_dec s s); try tauto.

    Lemma make_fo_unused : forall base values' values names,
      length values = length names
      -> make_fo names (values ++ values') base = make_fo names values base.
    Proof.
      induction values; destruct names; simpl; intuition.
      f_equal; auto.
    Qed.

    eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_star_assoc | apply Himp_refl ] | ].
    do 2 (eapply Himp_trans; [ apply Himp_star_assoc | ]).
    do 2 (apply Himp_star_pure_c; intro).
    repeat rewrite make_fo_unused by (unfold models; rewrite map_length; auto).
    do 2 (eapply Himp_trans; [ | apply Himp_star_assoc' ]).
    do 2 (apply Himp_star_pure_cc; auto).
    congruence.
    assert (predD Condition0 hE (make_fo Recursive0 (models rs) (fo_set fE s r))
      ===> predD Condition0 hE (fo_set (make_fo Recursive0 (models rs) fE) s r)).
    apply addSubstsH.
    eapply weaken_predD; eauto; intros.
    
    Lemma make_fo_reorder : forall s r x xs vs fE,
      ~In s xs
      -> make_fo xs vs (fo_set fE s r) x = fo_set (make_fo xs vs fE) s r x.
    Proof.
      induction xs; destruct vs; simpl; intuition.
      unfold fo_set at 1 3.
      destruct (string_dec x a); subst.
      destruct (string_dec a s); subst.
      tauto.
      unfold fo_set.
      destruct (string_dec a a); tauto.
      destruct (string_dec x s); subst.
      rewrite IHxs by auto.
      unfold fo_set.
      destruct (string_dec s s); tauto.
      rewrite IHxs by auto.
      unfold fo_set.
      destruct (string_dec x s); intuition.
      destruct (string_dec x a); intuition.
    Qed.

    apply make_fo_reorder; auto.

    generalize H17; clear.
    generalize (datatypeD hE dt); intro.
    generalize (children h); intro.
    generalize (predD Condition0 hE); intro.
    sepLemma.

    specialize (H12 fE (fo_set fE s r)).
    match type of H12 with
      | ?P -> _ => assert P
    end.
    intuition idtac.
    unfold fo_set.
    destruct (string_dec x s); subst; auto.
    exfalso; eauto.
    intuition idtac.
    inversion H16; auto.


    (** Case where recursive args are exhausted and we start on the nonrecursives *)
    destruct ws; simpl in *; try discriminate.
    injection H11; clear H11; intros.
    injection H10; clear H10; intros.
    unfold allocatePre in IHargs; simpl in IHargs.
    specialize (IHargs (psubst s a Condition0)).

    proveHyp IHargs.
    apply wellScoped_psubst.
    eapply wellScoped_weaken; eauto; simpl; tauto.
    intros.
    specialize (H12 fE1 fE2); intuition.
    proveHyp H12.
    auto.
    inversion H16; auto.

    Theorem boundVars_psubst : forall x e p,
      boundVars (psubst x e p) = boundVars p.
    Proof.
      induction p; simpl; intuition idtac;
        repeat match goal with
                 | [ H : _ |- _ ] => rewrite H
               end; auto.
    Qed.

    rewrite boundVars_psubst in *; intuition idtac.
    specialize (H16 Nonrecursive0); intuition idtac.
    proveHyp H16; eauto.
    proveHyp H17; eauto.
    specialize (H18 Recursive0); intuition idtac.
    proveHyp H17; eauto.
    specialize (H19 fE ws); intuition idtac.
    proveHyp H19.
    intros.
    specialize (H12 fE1 fE2).
    proveHyp H12.
    eauto.
    inversion H21; auto.

    Theorem normalize_psubst : forall x a p,
      normalize (psubst x a p) = nsubst x a (normalize p).
    Proof.
      induction p; simpl; intuition idtac;
        repeat match goal with
                 | [ H : _ |- _ ] => rewrite H
               end; auto.

      unfold nsubst; simpl.
      f_equal.
      2: symmetry; apply map_app.
      destruct (NPure (normalize p1)); auto.
      destruct (NPure (normalize p2)); auto.
    Qed.

    rewrite normalize_psubst in *.
    eapply Himp_trans; [ apply H20 | ]; clear H20.
    do 2 (apply Himp_ex; intro).
    do 2 (eapply Himp_trans; [ apply Himp_star_assoc | ]).
    do 2 (apply Himp_star_pure_c; intro).
    do 2 (eapply Himp_trans; [ | apply Himp_star_assoc' ]).
    do 2 (apply Himp_star_pure_cc; auto).
    apply Himp_star_frame; [ apply Himp_refl | ].

    Lemma map_extensional : forall A B (f1 f2 : A -> B) ls,
      (forall x, f1 x = f2 x)
      -> map f1 ls = map f2 ls.
      induction ls; simpl; intuition.
    Qed.

    Lemma psubst_fwd : forall x a hE p fvs bvs fE,
      wellScoped fvs p
      -> boundVars p = Some bvs
      -> ~In x bvs
      -> (forall fE1 fE2, (forall y, ~In y bvs -> fE1 y = fE2 y)
        -> exprD a fE1 = exprD a fE2)
      -> predD (psubst x a p) hE fE
      ===> predD p hE (fo_set fE x (exprD a fE)).
      induction p; simpl; intuition idtac.

      apply Himp_refl.

      caser.
      apply Himp_star_frame; eauto.
      eapply IHp1; eauto using in_or_app.
      intros; apply H2; intros.
      apply H0; intro.
      eauto using in_or_app.
      eapply IHp2; eauto using in_or_app.
      intros; apply H2; intros.
      apply H0; intro.
      eauto using in_or_app.

      caser.
      apply Himp_ex; intro.
      eapply Himp_trans; [ eapply IHp; eauto | ]; clear IHp.
      apply addSubstsH.
      eapply weaken_predD; eauto.
      intros.
      clear H0.
      intuition idtac.
      unfold fo_set.
      repeat match goal with
               | [ |- context[if ?E then _ else _] ] => destruct E; subst; try congruence
             end.
      apply H2; intuition idtac.
      destruct (string_dec y x0); congruence.

      apply Himp_refl'; f_equal.
      rewrite map_map.
      eauto using map_extensional, esubst_correct'.
    Qed.

    eapply Himp_trans; [ eapply psubst_fwd; eauto | ].
    intros.
    specialize (H12 fE1 fE2).
    proveHyp H12.
    eauto.
    inversion H23; auto.

    Lemma make_fo_irrel : forall xs2 vs2 x v y,
      y <> x
      -> forall xs1 vs1 fE,
        length xs1 = length vs1
        -> make_fo (xs1 ++ x :: xs2) (vs1 ++ v :: vs2) fE y
        = make_fo (xs1 ++ xs2) (vs1 ++ vs2) fE y.
      clear; induction xs1; destruct vs1; simpl; intuition.
      unfold fo_set.
      destruct (string_dec y x); tauto.
      unfold fo_set.
      destruct (string_dec y a); auto.
    Qed.

    apply addSubstsH.
    eapply weaken_predD; eauto.
    intros.
    unfold fo_set.
    destruct (string_dec x s); subst.
    unfold fo_set.
    destruct (string_dec s s); intuition.

    Lemma make_fo_middle : forall xs2 vs2 x v xs1 vs1 fE,
      length vs1 = length xs1
      -> ~In x xs1
      -> make_fo (xs1 ++ x :: xs2) (vs1 ++ v :: vs2) fE x = v.
    Proof.
      induction xs1; destruct vs1; simpl; intuition.
      unfold fo_set; destruct (string_dec x x); tauto.
      unfold fo_set; destruct (string_dec x a); subst; intuition.
    Qed.

    rewrite make_fo_middle; intuition eauto.
    2: unfold models; rewrite map_length; assumption.
    specialize (H12 fE (make_fo (Recursive0 ++ Nonrecursive0)
      (models v0 ++ dynify (firstn (Datatypes.length Nonrecursive0) ws)) fE)).
    proveHyp H12.
    intros.

    Lemma make_fo_skip : forall x xs vs fE,
      ~In x xs
      -> make_fo xs vs fE x = fE x.
    Proof.
      induction xs; destruct vs; simpl; intuition.
      unfold fo_set.
      destruct (string_dec x a); intuition.
    Qed.

    symmetry; apply make_fo_skip; intuition idtac.
    apply in_app_or in H23; intuition eauto.
    inversion_clear H23.
    congruence.

    destruct (In_dec string_dec x Recursive0).

    Lemma make_fo_app1 : forall x xs2 vs2 xs1 vs1 fE,
      In x xs1
      -> length vs1 = length xs1
      -> make_fo (xs1 ++ xs2) (vs1 ++ vs2) fE x = make_fo xs1 vs1 fE x.
    Proof.
      induction xs1; destruct vs1; simpl; intuition; subst.
      unfold fo_set.
      destruct (string_dec x x); tauto.
      unfold fo_set.
      destruct (string_dec x a); subst; auto.
    Qed.

    do 2 rewrite make_fo_app1 by (eauto; unfold models; rewrite map_length; assumption).
    reflexivity.

    Lemma make_fo_app2 : forall x xs2 vs2 xs1 vs1 fE,
      ~In x xs1
      -> length vs1 = length xs1
      -> make_fo (xs1 ++ xs2) (vs1 ++ vs2) fE x = make_fo xs2 vs2 fE x.
    Proof.
      induction xs1; destruct vs1; simpl; intuition; subst.
      unfold fo_set.
      destruct (string_dec x a); subst; intuition.
    Qed.

    do 2 rewrite make_fo_app2 by (eauto; unfold models; rewrite map_length; assumption).
    simpl.
    unfold fo_set.
    destruct (string_dec x s); intuition.
  Qed.

  Theorem allocatePre_sound : forall m p bvs argFvs,
    wellScoped (Recursive c ++ Nonrecursive c) (Condition c)
    -> boundVars (Condition c) = Some bvs
    -> (forall x, In x (Nonrecursive c) -> ~In x bvs)
    -> (forall x, In x (Recursive c) -> ~In x bvs)
    -> (forall x, In x (Nonrecursive c) -> ~In x argFvs)
    -> (forall x, In x (Recursive c) -> ~In x argFvs)
    -> (forall x, In x (Recursive c) -> ~In x (Nonrecursive c))
    -> (forall x, In x argFvs -> ~In x bvs)
    -> NoDup (Recursive c)
    -> forall (ns : list expr) rs fE nws rws, length ns = length (Nonrecursive c)
    -> length rs = length (Recursive c)
    -> map (fun e => exprD e fE) ns = map (@Dyn W) nws
    -> map (fun e => exprD e fE) rs = map (@Dyn W) rws
    -> (forall fE1 fE2,
      (forall x, In x argFvs -> fE1 x = fE2 x)
      -> List.Forall (fun e : expr => exprD e fE1 = exprD e fE2) (ns ++ rs))
    -> ptsto32m _ p O (natToW tag :: nws ++ rws)
    * normalD (allocatePre (fst dt) (normalizeCon c) (ns ++ rs)) hE fE
    ===> Ex sk, datatypeD hE dt sk m p.
  Proof.
    Opaque ptsto32m.
    intros.
    eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl |
      eapply (@allocatePre_sound' argFvs (argFvs ++ Recursive c ++ Nonrecursive c));
        intuition eauto using wellScoped_weaken, in_or_app] | ].

    eapply in_app_or in H13; intuition eauto.
    eapply in_app_or in H15; intuition eauto.
    rewrite app_length; congruence.
    rewrite map_app, H10, H11; rewrite <- map_app; eauto.

    eapply Himp_trans; [ apply Himp_star_comm | ].
    eapply Himp_trans; [ apply Himp_ex_star | ].
    apply Himp'_ex; intro sks.
    eapply Himp_trans; [ apply Himp_ex_star | ].
    apply Himp'_ex; intro rs'.
    apply Himp_ex_c; exists (Skeleton sks).
    simpl.
    apply Himp_ex_c; exists tag.
    apply Himp_ex_c; exists c.
    apply Himp_star_pure_cc; auto.
    unfold conD.
    apply Himp_ex_c; exists rs'.
    apply Himp_ex_c; exists nws.

    Lemma firstn_app1 : forall A (ls2 ls1 : list A),
      firstn (length ls1) (ls1 ++ ls2) = ls1.
    Proof.
      induction ls1; simpl; intuition.
    Qed.

    Lemma map_len : forall A1 A2 B (f1 : A1 -> B) (f2 : A2 -> B) ls1 ls2,
      map f1 ls1 = map f2 ls2
      -> length ls1 = length ls2.
    Proof.
      induction ls1; destruct ls2; simpl; intuition.
    Qed.

    rewrite <- H8.
    erewrite (@map_len _ _ _ _ _ ns) by eauto.
    rewrite firstn_app1.

    Lemma hackedy_hack_hack : forall P (P' : Prop) Q R S S' (T : Prop) R',
      T
      -> (P' -> R ===> R')
      -> (P' -> S ===> S')
      -> ([|P|] * [|P'|] * Q * R) * S ===> S' * [|P|] * [|T|] * R' * Q.
    Proof.
      sepLemma.
      etransitivity; [ apply himp_star_comm | ].
      apply Himp_star_frame; (hnf; auto).
    Qed.

    apply hackedy_hack_hack; intuition idtac.
    
    Lemma skipn_app1 : forall A (ls2 ls1 : list A),
      skipn (length ls1) (ls1 ++ ls2) = ls2.
    Proof.
      induction ls1; simpl; intuition.
    Qed.

    2: rewrite H13, skipn_app1; apply Himp_refl.
    simpl.
    replace (fo_set
      (make_fo (Recursive c ++ Nonrecursive c) (models rs' ++ dynify nws)
        fo_empty) "this" m)
    with (make_fo (Recursive c ++ Nonrecursive c) (models rs' ++ dynify nws) fo_empty) by admit.
    (* This is obviously an unsound rewrite, but it's a useful placeholder
     * while I figure out the right way to incorporate "this". *)

    apply addSubstsH.
    eapply weaken_predD; eauto.

    Lemma make_fo_overwritten : forall x xs vs fE1 fE2,
      In x xs
      -> length vs = length xs
      -> make_fo xs vs fE1 x = make_fo xs vs fE2 x.
    Proof.
      induction xs; destruct vs; simpl; intuition; subst; try discriminate.
      unfold fo_set.
      destruct (string_dec x x); tauto.
      unfold fo_set.
      destruct (string_dec x a); auto.
    Qed.

    intros; eapply make_fo_overwritten; eauto.
    repeat rewrite app_length.
    apply map_len in H10.
    apply map_len in H11.
    unfold models, dynify.
    repeat rewrite map_length.
    rewrite skipn_app1 in H13; subst.
    unfold addrs in H11.
    rewrite map_length in H11.
    congruence.
  Qed.

End allocatePre_sound.
