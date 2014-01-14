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

  Variable hO : ho_env nil.

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
        * predD (Condition c) hO
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

  Lemma allocatePre_sound' : forall fvs bvs,
    wellScoped fvs (Condition c)
    -> boundVars (Condition c) = Some bvs
    -> (forall x, In x bvs -> ~In x fvs)
    -> NoDup (Recursive c)
    -> (forall x, In x (Recursive c) -> ~In x bvs)
    -> (forall x, In x (Recursive c) -> ~In x fvs)
    -> forall args fE ws, length args = length (Nonrecursive c) + length (Recursive c)
    -> map (fun e => exprD e fE) args = map (@Dyn W) ws
    -> (forall fE1 fE2, (forall x, ~In x (Recursive c) -> ~In x bvs -> fE1 x = fE2 x)
      -> List.Forall (fun e => exprD e fE1 = exprD e fE2) args)
    -> normalD (allocatePre (fst dt) (normalizeCon c) args) hE fE
    ===> Ex sks, Ex rs, [| length rs = length (Recursive c) |]
    * children (datatypeD hE dt) sks rs
    * predD (Condition c) hE
    (make_fo (Recursive c ++ Nonrecursive c)
      (models rs ++ dynify (firstn (length (Recursive c)) ws)) fE).
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
    eapply Himp_trans; [ | apply Himp_star_assoc' ].
    apply Himp_star_pure_cc; auto.
    eapply Himp_trans; [ | apply Himp_star_Emp' ].
    apply addSubstsH.
    eapply normalize_sound_bwd; eauto.
    unfold not in *; eauto.

    destruct Nonrecursive0; simpl in *; intros.

    destruct Recursive0; simpl in *; try discriminate.
    injection H5; clear H5; intros.
    unfold allocatePre in IHargs; simpl in IHargs.
    specialize (IHargs Condition0 H H0 nil Recursive0); simpl in IHargs; intuition.
    apply Himp'_ex; fold addQuants; simpl; intro r.
    eapply Himp_trans; [ apply addSubstsH; apply addQuants_monotone | ].
    intros.
    apply star_out_fwd.
    destruct ws; simpl in *; try discriminate.
    injection H6; clear H6; intros.
    inversion_clear H2.

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
    apply H2; intro.
    apply in_app_or in H11; intuition eauto using normalize_boundVars.
    f_equal.
    specialize (H7 fE1 fE2).
    match type of H7 with
      | ?P -> _ => assert P
    end.
    intuition idtac.
    apply H2; intro.
    apply in_app_or in H12; intuition eauto using normalize_boundVars.
    intuition idtac.
    inversion H13; auto.

    simpl.
    assert (Hscoped : forall fE1 fE2,
      (forall x, (s = x \/ In x Recursive0 -> False) ->
        (In x bvs -> False) -> fE1 x = fE2 x)
       -> List.Forall (fun e => exprD e fE1 = exprD e fE2) args).
    intros.
    specialize (H7 fE1 fE2); intuition idtac.
    inversion H12; auto.

    Theorem map_same : forall A B (f g : A -> B) ls,
      List.Forall (fun x => f x = g x) ls
      -> map f ls = map g ls.
    Proof.
      induction 1; simpl; intuition.
    Qed.

    eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply IHargs; eauto ] | ].
    erewrite map_same.
    eassumption.
    simpl.
    eapply Forall_weaken; [ | apply Hscoped ].
    simpl; eauto; intros.
    intros; unfold fo_set.
    destruct (string_dec x s); intuition subst; tauto.

    replace (exprD a (fo_set fE s r)) with (exprD a fE).
    rewrite H8.
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
    eapply Himp_trans; [ apply Himp_star_assoc |  ].
    apply Himp_star_pure_c; intro.
    repeat rewrite make_fo_unused by (unfold models; rewrite map_length; auto).
    eapply Himp_trans; [ | apply Himp_star_assoc' ].
    apply Himp_star_pure_cc; auto.
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
      
    generalize H11; clear.
    generalize (datatypeD hE dt); intro.
    generalize (children h); intro.
    generalize (predD Condition0 hE); intro.
    sepLemma.

    specialize (H7 fE (fo_set fE s r)).
    match type of H7 with
      | ?P -> _ => assert P
    end.
    intuition idtac.
    unfold fo_set.
    destruct (string_dec x s); subst; auto; tauto.
    intuition idtac.
    inversion H12; auto.


    (** Case where recursive args are exhausted and we start on the nonrecursives *)
    admit.
  Qed.

End allocatePre_sound.
