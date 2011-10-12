(* Structured programming (module construction) *)

Require Import Bool NArith String List.

Require Import Nomega PropX PropXTac Word LabelMap IL XCAP Structured.

Set Implicit Arguments.

Local Open Scope N_scope.


Section module.
  Definition import := (string * string * assert)%type.

  Variable imports : list import.
  (* Which functions from outside this module do we need? *)

  Variable modName : string.
  (* New module name *)

  Definition function := (string * assert * forall imports, cmd imports modName)%type.

  Variable functions : list function.
  (* All functions in this module. *)

  (* Build the full list of imports for the commands, including both external and internal functions.
   * First, we build a version for only the external functions. *)

  Definition importsMap : LabelMap.t assert :=
    List.fold_left (fun m p => let '(mod, f, pre) := p in
      LabelMap.add (mod, Global f) pre m) imports (LabelMap.empty _).

  Definition fullImports : LabelMap.t assert :=
    List.fold_left (fun m p => let '(f, pre, _) := p in
      LabelMap.add (modName, Global f) pre m) functions importsMap.

  (* Now we are ready to generate a module out of the functions. *)

  Fixpoint blocks (fs : list function) (Base : N) : LabelMap.t (assert * block) :=
    match fs with
      | nil => LabelMap.empty _
      | (f, pre, c) :: fs' =>
        let cout := c fullImports pre in
        let cg := Generate cout Base 0 in
        let bls := LabelMap.add (modName, Global f) (pre, (nil, Uncond (RvLabel (modName, Local (Base + Entry cg)))))
          (blocks fs' (Base + N_of_nat (length (Blocks cg)))) in
          snd (List.fold_left (fun b_m p => let '(b, m) := b_m in
            (Nsucc b, LabelMap.add (modName, Local b) p m)) (Blocks cg) (Base, bls))
    end.

  Definition bmodule_ : module := {|
    Imports := importsMap;
    XCAP.Blocks := LabelMap.add (modName, Local 0) ((fun _ => [False])%PropX, (nil, Uncond (RvLabel (modName, Local 0))))
    (blocks functions 1)
  |}.

  Lemma Forall_MapsTo : forall A (P : _ * A -> Prop) m,
    (forall k v, LabelMap.MapsTo k v m -> P (k, v))
    -> List.Forall P (LabelMap.elements m).
    intros.
    generalize (fun k v H' => H k v (LabelMap.elements_2 H')); clear H; intro H.
    induction (LabelMap.elements m); simpl in *; intuition.
    constructor; auto.
    destruct a.
    apply H.
    constructor; hnf; auto.
  Qed.

  Lemma blocks_MapsTo : forall A k (v : A) bls Base bls',
    LabelMap.MapsTo k v
    (snd (fold_left (fun b_m p => let '(b, m) := b_m in
      (Nsucc b, LabelMap.add (modName, Local b) p m))
    bls (Base, bls')))
    -> (exists n, nth_error bls n = Some v
      /\ k = (modName, Local (Base + N_of_nat n)))
    \/ LabelMap.MapsTo k v bls'.
    induction bls; simpl; intuition.

    apply IHbls in H; clear IHbls; intuition.
    destruct H0; intuition; subst.

    left; exists (S x); intuition.
    replace (Nsucc Base + N_of_nat x) with (Base + N_of_nat (S x)) by (rewrite N_of_S; nomega); reflexivity.

    apply LabelFacts.add_mapsto_iff in H0; intuition; subst.
    left; exists O; intuition.
    replace (Base + N_of_nat 0) with Base by nomega; reflexivity.
  Qed.    

  Hypothesis NoSelfImport :
    List.fold_left (fun b p => let '(m, _, _) := p in
      b || if string_dec m modName then true else false) imports false = false.

  Theorem importsNotThis : forall l, LabelMap.In (elt:=assert) (modName, l) importsMap -> False.
    intros.
    assert (forall k v, LabelMap.MapsTo k v (LabelMap.empty assert) -> k <> (modName, l)).
    intros.
    apply LabelMap.empty_1 in H0; tauto.
    destruct H.
    unfold importsMap in *.
    generalize dependent (LabelMap.empty assert).
    generalize NoSelfImport; clear NoSelfImport.
    generalize false at 2.
    induction imports; simpl in *; intuition.
    apply H0 in H; auto.
    destruct a as [ [ ] ]; simpl in *.
    eapply IHl0 in NoSelfImport.
    auto.
    eauto.
    intros; subst.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst; [ | eauto ].
    destruct (string_dec s modName); subst; try congruence.
    replace (b || true) with true in NoSelfImport by (destruct b; auto).
    generalize NoSelfImport; clear.
    induction l0; simpl; intuition.
    destruct a as [ [ ] ]; intuition.
  Qed.

  Hint Immediate importsNotThis.

  Theorem importsNotThis' : forall l v, LabelMap.MapsTo (elt:=assert) (modName, l) v importsMap -> False.
    intros; eapply importsNotThis.
    hnf.
    eauto.
  Qed.

  Hint Resolve importsNotThis'.

  Lemma Forall_nth_error : forall A (P : A -> Prop) x ls,
    List.Forall P ls
    -> forall n, nth_error ls n = Some x
      -> P x.
    induction 1; destruct n; simpl; intuition; try discriminate.
    injection H1; congruence.
    eauto.
  Qed.

  Hypothesis BlocksGood : List.Forall (fun f : function => let '(_, pre, c) := f in
    (forall stn_st specs, ~interp specs (pre stn_st))
    /\ VerifCond (c fullImports pre)) functions.

  Theorem bmoduleOk : moduleOk bmodule_.
    constructor.

    clear BlocksGood.
    red; simpl.
    apply Forall_MapsTo.
    intros.
    simpl.
    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    eauto.
    generalize dependent 1.
    induction functions; simpl; intuition.
    apply LabelMap.empty_1 in H2; tauto.
    destruct a as [ [ ] ]; simpl in *.
    apply blocks_MapsTo in H2; intuition.
    destruct H1; intuition; subst; simpl in *.
    destruct H0.
    eauto.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst; congruence || eauto.


    red; simpl; unfold allPreconditions; simpl; intros.
    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    injection H3; clear H3; intros; subst; solve [ propxFo ].
    assert (0 < 1) by nomega.
    generalize dependent 1.
    induction functions; simpl; intuition.
    apply LabelMap.empty_1 in H3; tauto.
    inversion BlocksGood; clear BlocksGood; subst.
    destruct a as [ [  ] ]; simpl in *.
    apply blocks_MapsTo in H3; intuition.
    destruct H6; intuition; subst.

    clear H H3 H7.
    generalize (BlocksOk (Generate (c fullImports a) n 0)); intuition.
    apply (Forall_nth_error H) in H8.
    eapply H8; eauto.
    intros.
    apply H0.
    admit.

    apply LabelFacts.add_mapsto_iff in H6; intuition; subst.
    injection H9; clear H9; intros; subst; simpl in *.
    elimtype False; eauto.
    eapply H3; eauto; intros.
    apply H0.
    admit.
    nomega.
  Qed.
End module.
