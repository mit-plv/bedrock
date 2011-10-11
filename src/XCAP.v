(* An adaptation of Ni & Shao's XCAP program logic *)

Require Import Bool String.

Require Import Word IL LabelMap PropX.

Set Implicit Arguments.


(* The type of basic block preconditions (assertions) *)
Definition prop := PropX W state.
Definition assert := settings -> state -> prop.


(* A self-contained unit of code *)
Record module := {
  Imports : LabelMap.t assert;
  (* Which other blocks do we assume are available, and with what preconditions? *)
  Blocks : LabelMap.t (assert * block)
  (* The blocks that we provide, with precondition and code for each *)
}.

(* What must be verified for an individual block? *)
Definition blockOk (imps : LabelMap.t assert) (pre : assert) (bl : block) :=
  forall stn specs, (forall l pre, LabelMap.MapsTo l pre imps
    -> exists w, Labels stn l = Some w
      /\ specs w = Some (pre stn))
    -> forall st, interp specs (pre stn st) -> exists st', evalBlock stn st bl = Some st'
      /\ exists l, Labels stn l = Some (fst st')
        /\ exists pre', LabelMap.MapsTo l pre' imps
          /\ interp specs (pre' stn (snd st')).

Section moduleOk.
  Variable m : module.

  (* Calculate preconditions of all labels that are legal to mention. *)
  Definition allPreconditions := LabelMap.fold (fun l x m =>
    LabelMap.add l (fst x) m) (Blocks m) (Imports m).

  (* What must be verified for a full module? *)
  Definition moduleOk :=
    forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
      -> blockOk allPreconditions pre bl.

  (** Safety theorem *)

  Hypothesis closed : LabelMap.cardinal (Imports m) = 0.

  Hint Constructors SetoidList.InA.

  Lemma allPreconditions_just_blocks' : forall l pre mp,
    LabelMap.MapsTo l pre (LabelMap.fold (fun l x m => LabelMap.add l (fst x) m) (Blocks m) mp)
    -> LabelMap.MapsTo l pre mp
      \/ exists bl, LabelMap.MapsTo l (pre, bl) (Blocks m).
    clear closed; intros.
    rewrite LabelMap.fold_1 in H.
    apply LabelMap.elements_1 in H.
    assert (SetoidList.InA (@LabelMap.eq_key_elt _) (l, pre) (LabelMap.elements mp)
      \/ exists bl, SetoidList.InA (@LabelMap.eq_key_elt _) (l, (pre, bl)) (LabelMap.elements (Blocks m))).
    generalize dependent mp.
    induction (LabelMap.elements (Blocks m)); intuition; simpl in *; eauto.

    specialize (IHl0 _ H); clear H.
    destruct IHl0 as [ | [ ] ]; intuition.
    apply LabelMap.elements_2 in H.
    apply (proj1 (LabelFacts.add_mapsto_iff _ _ _ _ _)) in H; intuition; subst.
    right; eexists.
    apply SetoidList.InA_cons_hd; hnf; simpl; eauto.
    apply LabelMap.elements_1 in H1.
    eauto.
    eauto.

    intuition; eauto.
    apply LabelMap.elements_2 in H1; eauto.
    destruct H1.
    apply LabelMap.elements_2 in H0; eauto.
  Qed.

  Lemma allPreconditions_just_blocks : forall l pre, LabelMap.MapsTo l pre allPreconditions
    -> exists bl, LabelMap.MapsTo l (pre, bl) (Blocks m).
    intros.
    apply allPreconditions_just_blocks' in H; firstorder.

    rewrite LabelMap.cardinal_1 in closed.
    apply LabelMap.elements_1 in H.
    destruct (LabelMap.elements (Imports m)); simpl in *.
    inversion H.
    discriminate.
  Qed.

  Variable stn : settings.
  Variable prog : program.

  Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
    -> Labels stn l2 = Some w
    -> l1 = l2.

  Hypothesis agree : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
    -> exists w, Labels stn l = Some w
      /\ prog w = Some bl.

  Hypothesis ok : moduleOk.

  Definition specs : codeSpec W state := fun w =>
    LabelMap.fold (fun l p pre =>
      match pre with
        | Some _ => pre
        | None => match Labels stn l with
                    | None => None
                    | Some w' => if weq w w'
                      then Some (fst p stn)
                      else pre
                  end
      end) (Blocks m) None.

  Theorem InA_weaken : forall A (P : A -> A -> Prop) (x : A) (ls : list A),
    SetoidList.InA P x ls
    -> forall (P' : A -> A -> Prop) x',
      (forall y, P x y -> P' x' y)
      -> SetoidList.InA P' x' ls.
    induction 1; simpl; intuition.
  Qed.

  Lemma specsOk : forall l pre, LabelMap.MapsTo l pre allPreconditions
    -> exists w, Labels stn l = Some w
      /\ specs w = Some (pre stn).
    unfold specs; intros.

    destruct (allPreconditions_just_blocks H); clear H.

    destruct (agree H0); intuition.
    do 2 esplit; eauto.

    apply LabelMap.elements_1 in H0.
    rewrite LabelMap.fold_1.
    generalize (LabelMap.elements_3w (Blocks m)).
    generalize (fun l pre bl H => @agree l pre bl (LabelMap.elements_2 H)); clear agree; intro agree.
    unfold assert in *.
    match goal with
      | [ |- _ -> List.fold_left _ ?X _ = _ ] => induction X
    end; simpl in *.
    inversion H0.

    case_eq (Labels stn (fst a)); intros.

    destruct (weq x0 w); subst.
    inversion H0; clear H0; subst.
    hnf in H5; simpl in H5; intuition; subst.
    destruct a; simpl in *; subst; simpl in *.
    clear.
    induction l0; simpl; intuition.

    inversion H3; subst.
    eapply inj in H; eauto; subst.
    elimtype False.
    apply H6; clear H6.
    eapply InA_weaken; eauto.
    intros.
    subst.
    hnf in H0; simpl in H0; intuition.

    inversion H0; clear H0; subst.
    hnf in H5; simpl in H5; intuition; subst.
    unfold LabelMap.key in *.
    congruence.
    inversion H3; eauto.

    unfold LabelMap.key in *.
    specialize (@agree (fst a) (fst (snd a)) (snd (snd a))).
    destruct agree.
    apply SetoidList.InA_cons; left.
    hnf; simpl.
    intuition.
    simpl.
    destruct (snd (A := label) a); auto.
    intuition; congruence.
  Qed.

  Lemma safety' : forall st' st'', reachable stn prog st' st''
    -> forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
      -> forall st, interp specs (pre stn st)
        -> forall w, Labels stn l = Some w
          -> st' = (w, st)
        -> exists l', Labels stn l' = Some (fst st'')
          /\ exists pre', exists bl', LabelMap.MapsTo l' (pre', bl') (Blocks m)
            /\ interp specs (pre' stn (snd st'')).
    induction 1; simpl; intuition; subst; simpl in *.
    eauto 6.

    specialize (ok H1).
    red in ok.
    specialize (@ok stn _ specsOk _ H2).
    destruct ok; clear ok; intuition.
    destruct H6; intuition.
    destruct H7; intuition.
    apply allPreconditions_just_blocks in H7; destruct H7.
    eapply IHreachable; eauto.
    unfold step in H; simpl in H.
    destruct (agree H1); intuition.
    rewrite H9 in H3; injection H3; clear H3; intros; subst.
    rewrite H10 in H.
    rewrite H5 in H.
    injection H; clear H; intros; subst.
    destruct st'; simpl in *; congruence.
  Qed.

  Theorem safety'' : forall st st', reachable stn prog st st'
    -> forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
      -> Some (fst st) = Labels stn l -> interp specs (pre stn (snd st))
      -> step stn prog st' <> None.
    induction 1; simpl; intuition.

    unfold step in H2.
    destruct (agree H); intuition.
    rewrite <- H0 in H4; injection H4; clear H4; intros; subst.
    rewrite H5 in H2.
    specialize (ok H specsOk _ H1).
    destruct ok; intuition.
    congruence.

    specialize (ok H1 specsOk _ H3).
    destruct ok; clear ok; intuition.
    destruct H7; intuition.
    destruct H8; intuition.
    apply allPreconditions_just_blocks in H8.
    destruct H8.

    unfold step in H.
    destruct (agree H1); intuition.
    rewrite <- H2 in H10; injection H10; clear H10; intros; subst.
    rewrite H11 in H.
    rewrite H in H6; injection H6; clear H H6; intros; subst.

    eauto.
  Qed.

  Theorem safety : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
    -> forall w, Labels stn l = Some w
      -> forall st, interp specs (pre stn st)
        -> safe stn prog (w, st).
    unfold safe; intros; eapply safety''; eauto.
  Qed.
End moduleOk.


(** * Safe linking of modules *)
Section link.
  Variables m1 m2 : module.

  Definition union A (mp1 mp2 : LabelMap.t A) : LabelMap.t A :=
    LabelMap.fold (@LabelMap.add _) mp1 mp2.

  Definition diff A B (mp1 : LabelMap.t A) (mp2 : LabelMap.t B) : LabelMap.t A :=
    LabelMap.fold (fun k v mp => if LabelMap.mem k mp2 then mp else LabelMap.add k v mp) mp1 (@LabelMap.empty _).

  Definition link := {|
    Imports := union (diff (Imports m1) (Blocks m2)) (diff (Imports m2) (Blocks m1));
    Blocks := union (Blocks m1) (Blocks m2)
  |}.

  Hypothesis m1Ok : moduleOk m1.
  Hypothesis m2Ok : moduleOk m2.

  (* No label should be duplicated between the blocks of the two modules. *)
  Hypothesis NoDups : LabelMap.fold (fun k v b => b || LabelMap.mem k (Blocks m2)) (Blocks m1) false = false.

  (* Any import of one module provided by the other should have agreement on specification. *)
  Definition importsOk (Imp : LabelMap.t assert) (Blo : LabelMap.t (assert * block)) :=
    LabelMap.fold (fun l pre P =>
      match LabelMap.find l Blo with
        | None => P
        | Some (pre', _) => pre = pre' /\ P
      end) Imp True.

  Hypothesis ImportsOk1 : importsOk (Imports m1) (Blocks m2).
  Hypothesis ImportsOk2 : importsOk (Imports m2) (Blocks m1).

  (* Finally, modules shouldn't import their own labels. *)
  Definition noSelfImport (m : module) :=
    LabelMap.fold (fun l _ b => b || LabelMap.mem l (Imports m)) (Blocks m) false = false.

  Hypothesis NoSelfImport1 : noSelfImport m1.
  Hypothesis NoSelfImport2 : noSelfImport m2.
  
  Theorem MapsTo_union : forall A k v (mp1 mp2 : LabelMap.t A),
    LabelMap.MapsTo k v (union mp1 mp2)
    -> LabelMap.MapsTo k v mp1 \/ LabelMap.MapsTo k v mp2.
    unfold union; intros.
    rewrite LabelMap.fold_1 in H.
    generalize (@LabelMap.elements_2 _ mp1).
    generalize dependent mp2.
    induction (LabelMap.elements mp1); simpl in *; intuition; simpl in *.
    apply IHl in H; clear IHl.
    intuition.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst.
    left; apply H0.
    constructor.
    hnf.
    tauto.

    eauto.
  Qed.

  Lemma blockOk_impl : forall imps imps' p bl,
    (forall k v, LabelMap.MapsTo k v imps
      -> LabelMap.MapsTo k v imps')
    -> blockOk imps p bl
    -> blockOk imps' p bl.
    unfold blockOk; intuition.
    specialize (H0 stn specs0).
    match type of H0 with
      | ?P -> _ => assert P by auto; intuition
    end.
    specialize (H4 _ H2); destruct H4; intuition.
    destruct H5; intuition.
    destruct H6; intuition.
    eauto 8.
  Qed.

  Lemma fold_mono1 : forall A F ls b,
    List.fold_left (fun (a : bool) (x : A) => a || F x) ls b = false
    -> b = false.
    induction ls; simpl; intuition.
    apply IHls in H.
    destruct b; simpl in *; congruence.
  Qed.

  Lemma fold_mono2 : forall A F ls b,
    List.fold_left (fun (a : bool) (x : A) => a || F x) ls b = false
    -> List.Forall (fun x => F x = false) ls.
    induction ls; simpl; intuition.
    specialize (fold_mono1 _ _ _ H).
    destruct b; try discriminate.
    eauto.
  Qed.

  Lemma link_allPreconditions : forall k v m m', LabelMap.MapsTo k v (allPreconditions m)
    -> (forall k v, LabelMap.MapsTo k v (Blocks m) -> LabelMap.MapsTo k v (Blocks m'))
    -> (forall k v, LabelMap.MapsTo k v (Imports m) -> LabelMap.MapsTo k v (Imports m')
      \/ exists bl, LabelMap.MapsTo k (v, bl) (Blocks m'))
    -> noSelfImport m'
    -> LabelMap.MapsTo k v (allPreconditions m').
    unfold allPreconditions, noSelfImport; intros.
    repeat rewrite LabelMap.fold_1 in *.
    generalize (fun k v (H : SetoidList.InA (@LabelMap.eq_key_elt _) (k, v) (LabelMap.elements (Blocks m))) => H0 k v (LabelMap.elements_2 H));
      clear H0; intro H0.

    generalize (LabelMap.elements_3w (Blocks m)).
    induction (LabelMap.elements (Blocks m)); simpl in *; intuition.

    clear H0.
    apply fold_mono2 in H2.
    apply H1 in H; clear H1; intuition.

    generalize dependent (Imports m').
    induction (LabelMap.elements (Blocks m')); simpl; intuition; simpl in *.
    inversion H2; clear H2; intros; subst; simpl in *.
    specialize (IHl _ H5 H0).
    
    assert (LabelMap.MapsTo k v t -> LabelMap.MapsTo k v (LabelMap.add a0 a t)).
    intros; apply LabelMap.add_2; auto.
    intro; subst.
    generalize (LabelMap.mem_1 (ex_intro (fun v => LabelMap.MapsTo _ v _) _ H0)); congruence.
    generalize dependent (LabelMap.add a0 a t).
    clear H0 H3 H4 H5; generalize dependent t.
    induction l; simpl in *; intuition; simpl in *.
    eapply IHl; eauto; intros.
    apply LabelFacts.add_mapsto_iff in H0; intuition; subst.
    apply LabelMap.add_1; auto.
    apply LabelMap.add_2; auto.


    destruct H0.
    generalize (LabelMap.elements_3w (Blocks m')).
    apply LabelMap.elements_1 in H.
    generalize dependent (Imports m').
    induction (LabelMap.elements (Blocks m')); simpl; intuition.
    inversion H.
    inversion H2; clear H2; intros; subst.
    inversion H; clear H; intros; subst.
    red in H2; intuition; subst; simpl in *; subst.
    destruct a; simpl in *; subst; simpl in *.
    inversion H0; clear H0; intros; subst.
    hnf in H2; simpl in H2; intuition; subst; simpl in *.
    assert (LabelMap.MapsTo k0 v (LabelMap.add k0 v t)).
    apply LabelMap.add_1; auto.
    generalize dependent (LabelMap.add k0 v t).
    generalize H4; clear.
    induction l; simpl; intuition.
    apply H; auto.
    apply LabelMap.add_2; auto.
    intro; subst.
    apply H4; auto.
    constructor.
    reflexivity.
    
    intuition.
    inversion H0; clear H0; intros; subst.
    apply H in H6; clear H; auto.
    assert (LabelMap.MapsTo k v t -> LabelMap.MapsTo k v (LabelMap.add (fst a) (fst (snd a)) t)).
    intro.
    apply LabelMap.add_2; auto.
    intro; subst.
    generalize (LabelMap.mem_1 (ex_intro (fun v => LabelMap.MapsTo _ v _) _ H)); congruence.
    generalize dependent (LabelMap.add (fst a) (fst (snd a)) t).
    generalize H6; clear.
    generalize t.
    induction l; simpl; intuition.
    simpl in *.
    eapply IHl in H6; eauto.
    intro.
    apply LabelFacts.add_mapsto_iff in H0; intuition; subst.
    apply LabelMap.add_1; auto.
    apply LabelMap.add_2; auto.


    inversion H3; clear H3; intros; subst.
    assert (LabelMap.MapsTo (fst a) (snd a) (Blocks m')).
    apply H0.
    constructor.
    destruct a; hnf; auto.
    assert (k = fst a /\ v = fst (snd a)
      \/ LabelMap.MapsTo k v
      (List.fold_left
        (fun (a : LabelMap.t assert) (p : label * (assert * block)) =>
          LabelMap.add (fst p) (fst (snd p)) a) l (Imports m))).

    generalize H; clear.
    assert (LabelMap.MapsTo k v (LabelMap.add (fst a) (fst (snd a)) (Imports m))
      -> (k = fst a /\ v = fst (snd a))
      \/ LabelMap.MapsTo k v (Imports m)).
    intro.
    apply LabelFacts.add_mapsto_iff in H; intuition.
    generalize dependent (LabelMap.add (fst a) (fst (snd a)) (Imports m)).
    generalize (Imports m).
    induction l; simpl; intuition.
    simpl in *.
    eapply IHl; [ | eassumption ].
    intro.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst.
    right.
    apply LabelMap.add_1; auto.
    right.
    apply LabelMap.add_2; auto.


    intuition; subst.
    generalize (LabelMap.elements_3w (Blocks m')).
    apply LabelMap.elements_1 in H3.
    generalize H3; clear.
    destruct a; simpl.
    generalize (Imports m').
    induction (LabelMap.elements (Blocks m')); simpl; intuition.
    inversion H3.
    inversion H; clear H; intros; subst.
    inversion H3; clear H3; intros; subst.
    hnf in H0; intuition; subst; simpl in *; subst.
    simpl.
    assert (LabelMap.MapsTo a0 a (LabelMap.add a0 a t)) by (apply LabelMap.add_1; auto).
    clear IHl H4.
    generalize dependent (LabelMap.add a0 a t).
    induction l; simpl; intuition.
    apply H.
    apply LabelMap.add_2; auto.
    intro; subst.
    apply H2.
    constructor.
    red; reflexivity.
    
    eauto.
  Qed.
    
  Theorem linkOk : moduleOk link.
    red; intros.
    unfold link in *; simpl in *.
    unfold moduleOk in *.
    apply MapsTo_union in H; destruct H.

    apply m1Ok in H.
    eapply blockOk_impl; [ | eassumption ].
    intros; eapply link_allPreconditions; simpl; eauto.
    admit.
    admit.
    admit.

    apply m2Ok in H.
    eapply blockOk_impl; [ | eassumption ].
    intros; eapply link_allPreconditions; simpl; eauto.
    admit.
    admit.
    admit.
  Qed.
End link.
