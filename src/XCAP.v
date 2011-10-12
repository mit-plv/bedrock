(* An adaptation of Ni & Shao's XCAP program logic *)

Require Import Bool String.

Require Import Word IL LabelMap PropX.

Set Implicit Arguments.


(* The type of basic block preconditions (assertions) *)
Definition prop := PropX W (settings * state).
Definition assert := spec W (settings * state).


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
      /\ specs w = Some pre)
    -> forall st, interp specs (pre (stn, st)) -> exists st', evalBlock stn st bl = Some st'
      /\ exists pre', specs (fst st') = Some pre'
        /\ interp specs (pre' (stn, snd st')).

Section moduleOk.
  Variable m : module.

  Definition noSelfImport :=
    List.Forall (fun p => ~LabelMap.In (fst p) (Imports m)) (LabelMap.elements (Blocks m)).

  (* Calculate preconditions of all labels that are legal to mention. *)
  Definition allPreconditions := LabelMap.fold (fun l x m =>
    LabelMap.add l (fst x) m) (Blocks m) (Imports m).

  (* What must be verified for a full module? *)
  Record moduleOk := {
    NoSelfImport : noSelfImport;
    BlocksOk : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
      -> blockOk allPreconditions pre bl
  }.

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

  Definition specs : codeSpec W (settings * state) := fun w =>
    LabelMap.fold (fun l p pre =>
      match pre with
        | Some _ => pre
        | None => match Labels stn l with
                    | None => None
                    | Some w' => if weq w w'
                      then Some (fst p)
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
      /\ specs w = Some pre.
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

  Lemma specsOk' : forall w pre, specs w = Some pre
    -> exists l, Labels stn l = Some w
      /\ exists bl, LabelMap.MapsTo l (pre, bl) (Blocks m).
    unfold specs; intros.
    assert (exists l : label,
      Labels stn l = Some w /\
      (exists bl : block, SetoidList.InA (@LabelMap.eq_key_elt _) (l, (pre, bl)) (LabelMap.elements (Blocks m)))).
    rewrite LabelMap.fold_1 in H.
    generalize (fun l pre bl H => @agree l pre bl (LabelMap.elements_2 H)).
    generalize H; clear.
    induction (LabelMap.elements (Blocks m)); simpl; intuition.
    discriminate.

    assert (SetoidList.InA (@LabelMap.eq_key_elt _) (fst a, (fst (snd a), snd (snd a))) (a :: l)).
    constructor; hnf; simpl.
    destruct a as [ ? [ ] ]; auto.
    apply H0 in H1.
    destruct H1; intuition.
    rewrite H2 in H.
    destruct (weq w x); subst.
    assert (Labels stn (fst a) = Some x /\ fst (snd a) = pre).
    generalize H H2; clear.
    induction l; simpl; intuition eauto.
    congruence.
    intuition.
    destruct a as [ ? [ ] ]; simpl in *; subst.
    repeat esplit; eauto.
    constructor; hnf; simpl; eauto.
    intuition.
    match type of H1 with
      | ?P -> _ => assert P
    end.
    intros.
    eapply H0.
    eauto.
    intuition.
    destruct H5; intuition.
    destruct H6.
    eauto.

    destruct H0; intuition.
    destruct H2.
    repeat esplit; eauto.
    apply LabelMap.elements_2; eauto.
  Qed.

  Lemma safety' : forall st' st'', reachable stn prog st' st''
    -> forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
      -> forall st, interp specs (pre (stn, st))
        -> forall w, Labels stn l = Some w
          -> st' = (w, st)
        -> exists l', Labels stn l' = Some (fst st'')
          /\ exists pre', exists bl', LabelMap.MapsTo l' (pre', bl') (Blocks m)
            /\ interp specs (pre' (stn, snd st'')).
    induction 1; simpl; intuition; subst; simpl in *.
    eauto 6.

    destruct (agree H1); intuition.
    rewrite H3 in H5; injection H5; clear H5; intros; subst.
    unfold step in H; simpl in H.
    rewrite H6 in H.
    specialize (BlocksOk ok H1); clear ok; intro ok.
    red in ok.
    specialize (@ok stn _ specsOk _ H2).
    destruct ok; clear ok; intuition.
    destruct H6; intuition.
    destruct H7; intuition.
    destruct (specsOk' _ H6) as [? [? [ ] ] ].
    eapply IHreachable.
    apply H8.
    eauto.
    eauto.
    destruct x0; simpl in *.
    congruence.
  Qed.

  Theorem safety'' : forall st st', reachable stn prog st st'
    -> forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
      -> Some (fst st) = Labels stn l -> interp specs (pre (stn, snd st))
      -> step stn prog st' <> None.
    induction 1; simpl; intuition.

    unfold step in H2.
    destruct (agree H); intuition.
    rewrite <- H0 in H4; injection H4; clear H4; intros; subst.
    rewrite H5 in H2.
    specialize (BlocksOk ok H _ specsOk _ H1); clear ok; destruct 1; intuition.
    congruence.

    destruct (BlocksOk ok H1 _ specsOk _ H3); clear ok; intuition.
    destruct H7; intuition.
    destruct (agree H1); intuition.
    unfold step in H.
    rewrite <- H2 in H9; injection H9; clear H9; intros; subst.
    rewrite H10 in H.
    rewrite H in H6; injection H6; clear H6; intros; subst.
    destruct (specsOk' _ H7) as [? [? [ ] ] ].
    eauto.
  Qed.

  Theorem safety : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
    -> forall w, Labels stn l = Some w
      -> forall st, interp specs (pre (stn, st))
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

  (* The modules must agree on shared imports. *)
  Hypothesis ImportsAgree : LabelMap.fold (fun l pre P =>
    match LabelMap.find l (Imports m2) with
      | None => P
      | Some pre' => pre = pre' /\ P
    end) (Imports m1) True.
  
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
    apply H1 in H; clear H1; intuition.

    generalize dependent (Imports m').
    induction (LabelMap.elements (Blocks m')); simpl; intuition; simpl in *.
    inversion H2; clear H2; intros; subst; simpl in *.
    specialize (IHl _ H5 H0).
    
    assert (LabelMap.MapsTo k v t -> LabelMap.MapsTo k v (LabelMap.add a0 a t)).
    intros; apply LabelMap.add_2; auto.
    intro; subst.
    apply H4.
    hnf; eauto.
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
    apply H5; hnf; eauto.
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

  Theorem Forall_union : forall A (P : _ * A -> Prop) bls1 bls2,
    List.Forall P (LabelMap.elements bls1)
    -> List.Forall P (LabelMap.elements bls2)
    -> List.Forall P (LabelMap.elements (union bls1 bls2)).
    intros; unfold union.
    rewrite LabelMap.fold_1.
    generalize dependent bls2.
    induction (LabelMap.elements bls1); simpl in *; intuition.

    inversion H; clear H; intros; subst.
    apply IHl; auto.
    apply List.Forall_forall; intros.
    assert (SetoidList.InA (@LabelMap.eq_key_elt _) x (LabelMap.elements (LabelMap.add (fst a) (snd a) bls2))).
    apply SetoidList.InA_alt.
    repeat esplit; auto.
    destruct x.
    apply LabelMap.elements_2 in H1.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst.
    destruct a; assumption.
    eapply List.Forall_forall.
    apply H0.
    apply LabelMap.elements_1 in H5.
    apply SetoidList.InA_alt in H5.
    destruct H5; intuition.
    hnf in H6; simpl in H6; intuition; subst.
    destruct x; assumption.
  Qed.

  Theorem MapsTo_union1 : forall A k v (mp1 mp2 : LabelMap.t A),
    LabelMap.MapsTo k v mp1
    -> LabelMap.MapsTo k v (union mp1 mp2).
    unfold union; intros.
    rewrite LabelMap.fold_1.
    generalize (@LabelMap.elements_1 _ mp1 _ _ H); clear H.
    generalize (@LabelMap.elements_3w _ mp1).
    generalize dependent mp2.
    induction (LabelMap.elements mp1); simpl in *; intuition; simpl in *.
    inversion H0.
    inversion H; clear H; intros; subst.
    inversion H0; clear H0; intros; subst.
    hnf in H1; simpl in *; intuition; subst.
    generalize H3; clear.
    assert (LabelMap.MapsTo a0 b (LabelMap.add a0 b mp2)) by (apply LabelMap.add_1; auto).
    generalize dependent (LabelMap.add a0 b mp2).
    induction l; simpl; intuition; simpl.
    apply IHl; auto.
    apply LabelMap.add_2; auto.
    intro; subst; apply H3.
    constructor; hnf; reflexivity.

    eauto.
  Qed.

  Theorem MapsTo_union2 : forall A k v (mp1 mp2 : LabelMap.t A),
    LabelMap.MapsTo k v mp2
    -> (forall v', LabelMap.MapsTo k v' mp1 -> v' = v)
    -> LabelMap.MapsTo k v (union mp1 mp2).
    unfold union; intros.
    rewrite LabelMap.fold_1.
    generalize (@LabelMap.elements_3w _ mp1).
    generalize dependent mp2.
    generalize (fun v' (H : SetoidList.InA (@LabelMap.eq_key_elt _) (k, v') (LabelMap.elements mp1)) => H0 v' (LabelMap.elements_2 H)).
    clear.
    induction (LabelMap.elements mp1); simpl in *; intuition; simpl in *.
    inversion H1; clear H1; intros; subst; simpl in *.
    apply IHl; auto.
    destruct (LabelKey.eq_dec k (fst a)).
    hnf in e; subst.
    assert (snd a = v).
    apply H.
    destruct a; simpl.
    constructor; hnf; auto.
    subst.
    apply LabelMap.add_1; auto.
    apply LabelMap.add_2; auto.
  Qed.

  Hint Resolve MapsTo_union1 MapsTo_union2.

  Theorem NoDups_Forall : forall (bls1 bls2 : LabelMap.t (assert * block)) i,
    LabelMap.fold (fun k v b => b || LabelMap.mem k bls2) bls1 i = false
    -> List.Forall (fun p => ~LabelMap.In (fst p) bls2) (LabelMap.elements bls1).
    intros; rewrite LabelMap.fold_1 in *.
    generalize dependent bls2.
    generalize dependent i.
    induction (LabelMap.elements bls1); simpl in *; intuition; simpl in *.
    constructor; simpl.
    specialize (fold_mono1 _ _ _ H); intro Hmono.
    destruct i; try discriminate; simpl in *.
    intro.
    apply LabelMap.mem_1 in H0.
    congruence.

    eauto.
  Qed.

  Hint Resolve NoDups_Forall.

  Lemma MapsTo_diff' : forall A B k (v : A) (mp2 : LabelMap.t B) (mp1 mp' : LabelMap.t A),
    LabelMap.MapsTo k v
    (LabelMap.fold (fun k0 v0 mp => if LabelMap.mem k0 mp2 then mp else LabelMap.add k0 v0 mp)
      mp1 mp')
    -> (LabelMap.In k mp' -> ~LabelMap.In k mp2)
    -> (LabelMap.MapsTo k v mp1 \/ LabelMap.MapsTo k v mp') /\ ~LabelMap.In k mp2.
    intros; rewrite LabelMap.fold_1 in *.

    assert ((SetoidList.InA (@LabelMap.eq_key_elt _) (k, v) (LabelMap.elements mp1) \/ LabelMap.MapsTo k v mp') /\
      ~LabelMap.In k mp2); [ | generalize (@LabelMap.elements_2 _ mp1); intuition ].

    generalize dependent mp'; induction (LabelMap.elements mp1); simpl; intuition.
    unfold LabelMap.In, LabelMap.Raw.In0 in *; eauto.

    simpl in *.
    apply IHl in H; intuition.

    match goal with
      | [ _ : context[if ?E then _ else _] |- _ ] => case_eq E; intro Heq; rewrite Heq in *
    end; intuition.
    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    left; constructor; hnf; auto.

    match goal with
      | [ _ : context[if ?E then _ else _] |- _ ] => case_eq E; intro Heq; rewrite Heq in *
    end; intuition.
    destruct H1.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst.
    destruct H2.
    generalize (LabelMap.mem_1 (ex_intro (fun v => LabelMap.MapsTo _ v _) _ H1)); congruence.
    unfold LabelMap.In, LabelMap.Raw.In0 in *; eauto.

    simpl in *.
    apply IHl in H; intuition.
    match goal with
      | [ _ : context[if ?E then _ else _] |- _ ] => case_eq E; intro Heq; rewrite Heq in *
    end; intuition.
    destruct H2.
    apply LabelFacts.add_mapsto_iff in H2; intuition; subst.
    apply LabelMap.mem_1 in H3; congruence.
    unfold LabelMap.In, LabelMap.Raw.In0 in *; eauto.    
  Qed.

  Lemma MapsTo_diff : forall A B k v (mp1 : LabelMap.t A) (mp2 : LabelMap.t B),
    LabelMap.MapsTo k v (diff mp1 mp2)
    -> LabelMap.MapsTo k v mp1 /\ ~LabelMap.In k mp2.
    intros.
    apply MapsTo_diff' in H; intuition.
    apply LabelMap.empty_1 in H; tauto.
    destruct H0.
    apply LabelMap.empty_1 in H0; tauto.
  Qed.

  Lemma linkOk' : noSelfImport link.
    destruct m1Ok; clear m1Ok.
    destruct m2Ok; clear m2Ok.
    red; simpl.
    apply Forall_union; apply List.Forall_forall; intros; intro.

    destruct H0.
    apply MapsTo_union in H0; intuition.

    apply MapsTo_diff in H1; intuition.

    eapply (proj1 (List.Forall_forall _ _)) in NoSelfImport0.
    apply NoSelfImport0.
    hnf; eauto.
    auto.

    apply MapsTo_diff in H1; intuition.

    apply H2.
    exists (snd x).
    apply LabelMap.elements_2.
    apply SetoidList.InA_alt.
    destruct x; simpl in *; repeat esplit; auto.


    destruct H0.
    apply MapsTo_union in H0; intuition.

    apply MapsTo_diff in H1; intuition.
    apply H2.
    exists (snd x).
    apply LabelMap.elements_2.
    apply SetoidList.InA_alt.
    destruct x; simpl in *; repeat esplit; auto.

    apply MapsTo_diff in H1; intuition.

    eapply (proj1 (List.Forall_forall _ _)) in NoSelfImport1.
    apply NoSelfImport1.
    hnf; eauto.
    auto.
  Qed.

  Hint Resolve linkOk'.

  Lemma use_importsOk' : forall (bls : LabelMap.t (assert * block)) l P,
    List.fold_left (fun P p =>
      match LabelMap.find (fst p) bls with
        | None => P
        | Some (pre', _) => snd p = pre' /\ P
      end) l P
    -> P.
    induction l; simpl; intuition; simpl in *.
    
    destruct (LabelMap.find a0 bls).
    destruct p.
    apply IHl in H; tauto.
    apply IHl in H; tauto.
  Qed.

  Lemma use_importsOk : forall k v p imp bls,
    importsOk imp bls
    -> LabelMap.MapsTo k v imp
    -> LabelMap.find k bls = Some p
    -> v = fst p.
    clear ImportsAgree; unfold importsOk; intros.

    rewrite LabelMap.fold_1 in *.
    apply LabelMap.elements_1 in H0.
    generalize dependent True.
    induction (LabelMap.elements imp); simpl in *; intuition.
    inversion H0.

    inversion H0; clear H0; intuition; subst.
    hnf in H3; simpl in *; intuition; subst.
    unfold LabelMap.key in *.
    rewrite H1 in H.
    destruct p; simpl in *.
    apply use_importsOk' in H; tauto.

    eauto.
  Qed.

  Lemma MapsTo_diffr : forall A B k v (mp1 : LabelMap.t A) (mp2 : LabelMap.t B),
    LabelMap.MapsTo k v mp1
    -> ~LabelMap.In k mp2
    -> SetoidList.NoDupA (@LabelMap.eq_key _) (LabelMap.elements mp1)
    -> LabelMap.MapsTo k v (diff mp1 mp2).
    intros; unfold diff.
    rewrite LabelMap.fold_1.
    apply LabelMap.elements_1 in H.
    generalize (LabelMap.empty A).
    induction (LabelMap.elements mp1); simpl in *; intuition.
    inversion H.

    inversion H1; clear H1; intros; subst.
    inversion H; clear H; intros; subst.
    hnf in H2; simpl in *; intuition; subst.
    case_eq (LabelMap.mem (fst a) mp2); intro Heq.
    apply LabelMap.mem_2 in Heq; tauto.
    generalize H4; clear.
    assert (LabelMap.MapsTo (fst a) (snd a) (LabelMap.add (fst a) (snd a) t)) by (apply LabelMap.add_1; auto).
    generalize dependent (LabelMap.add (fst a) (snd a) t).
    induction l; simpl; intuition; simpl.
    destruct (LabelMap.mem a1 mp2); auto.
    apply IHl; auto.
    apply LabelMap.add_2; auto.
    intro; subst.
    apply H4.
    constructor; hnf; auto.

    auto.
  Qed.

  Lemma use_NoDups : forall k0 v,
    LabelMap.find k0 (Blocks m2) = Some v
    -> forall v', LabelMap.MapsTo k0 v' (Blocks m1) -> v' = v.
    intros.
    elimtype False.
    apply NoDups_Forall in NoDups.
    apply LabelMap.elements_1 in H0.
    apply SetoidList.InA_alt in H0.
    destruct H0; intuition.
    hnf in H1; simpl in *; intuition; subst.
    apply (proj1 (List.Forall_forall _ _) NoDups) in H2; auto.
    apply LabelMap.find_2 in H.
    hnf; eauto.
  Qed.

  Hint Resolve use_NoDups.

  Lemma ImportsAgree_mono : forall (imp1 : LabelMap.t assert) ls P,
    List.fold_left (fun P p =>
      match LabelMap.find (fst p) imp1 with
        | None => P
        | Some pre' => snd p = pre' /\ P
      end) ls P
    -> P.
    induction ls; simpl in *; intuition; simpl in *.
    destruct (LabelMap.find a0 imp1).
    apply IHls in H; tauto.
    apply IHls in H; tauto.
  Qed.
  
  Theorem linkOk : moduleOk link.
    destruct m1Ok; clear m1Ok.
    destruct m2Ok; clear m2Ok.

    constructor; auto.

    intros.
    simpl in H; apply MapsTo_union in H; destruct H.

    apply BlocksOk0 in H.
    eapply blockOk_impl; [ | eassumption ].
    intros; eapply link_allPreconditions; simpl; eauto.

    intros.
    case_eq (LabelMap.find k0 (Blocks m2)); intros.

    specialize (use_importsOk _ ImportsOk1 H1 H2); intro; subst.
    destruct p; simpl in *.
    right.
    eexists.
    apply MapsTo_union2.
    apply LabelMap.find_2; eauto.
    eauto.
    left.
    apply MapsTo_union1.


    apply MapsTo_diffr; auto.
    intro.
    destruct H3.
    apply LabelMap.find_1 in H3; congruence.
    apply LabelMap.elements_3w.


    apply BlocksOk1 in H.
    eapply blockOk_impl; [ | eassumption ].
    intros; eapply link_allPreconditions; simpl; eauto.

    intros.
    eapply MapsTo_union2; eauto.
    intros.
    eapply use_NoDups; eauto.
    apply LabelMap.find_1; auto.

    intros.
    case_eq (LabelMap.find k0 (Blocks m1)); intros.

    specialize (use_importsOk _ ImportsOk2 H1 H2); intro; subst.
    destruct p; simpl in *.
    right.
    eexists.
    apply MapsTo_union1.
    apply LabelMap.find_2; eauto.
    eauto.
    left.
    apply MapsTo_union2.


    apply MapsTo_diffr; auto.
    intro.
    destruct H3.
    apply LabelMap.find_1 in H3; congruence.
    apply LabelMap.elements_3w.

    intros.
    apply MapsTo_diff in H3; intuition.
    apply LabelMap.elements_1 in H4.
    generalize ImportsAgree H1 H4; clear.
    rewrite LabelMap.fold_1.
    generalize True.
    induction (LabelMap.elements (Imports m1)); simpl; intuition.
    inversion H4.
    inversion H4; clear H4; intros; subst.
    hnf in H0; simpl in *; intuition; subst.
    apply LabelMap.find_1 in H1.
    rewrite H1 in ImportsAgree.

    apply ImportsAgree_mono in ImportsAgree; tauto.
    eauto.
  Qed.
End link.
