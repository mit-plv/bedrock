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
        let cg := Generate cout (Nsucc Base) Base in
        let bls := LabelMap.add (modName, Global f) (pre, (nil, Uncond (RvLabel (modName, Local (Nsucc Base + Entry cg)))))
          (LabelMap.add (modName, Local Base) (Postcondition cout, (nil, Uncond (RvLabel (modName, Local Base))))
            (blocks fs' (Nsucc Base + N_of_nat (length (Blocks cg))))) in
          snd (List.fold_left (fun b_m p => let '(b, m) := b_m in
            (Nsucc b, LabelMap.add (modName, Local b) p m)) (Blocks cg) (Nsucc Base, bls))
    end.

  Definition bmodule_ : module := {|
    Imports := importsMap;
    XCAP.Blocks := blocks functions 1
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
    VerifCond (c fullImports pre)) functions.

  Theorem bmoduleOk : moduleOk bmodule_.
    constructor.

    clear BlocksGood.
    red; simpl.
    apply Forall_MapsTo.
    intros.
    simpl.
    generalize dependent 1.
    induction functions; simpl; intuition.
    apply LabelMap.empty_1 in H; tauto.
    destruct a as [ [ ] ]; simpl in *.
    apply blocks_MapsTo in H; intuition.
    destruct H1; intuition; subst; simpl in *.
    destruct H0.
    eauto.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst; congruence || eauto.
    apply LabelFacts.add_mapsto_iff in H2; intuition; subst; congruence || eauto.


    red; simpl; unfold allPreconditions; simpl; intros.
    assert (0 < 1) by nomega.
    generalize dependent 1.
    induction functions; simpl; intuition.
    apply LabelMap.empty_1 in H; tauto.
    inversion BlocksGood; clear BlocksGood; subst.
    destruct a as [ [  ] ]; simpl in *.
    apply blocks_MapsTo in H; intuition.
    destruct H3; intuition; subst.

    clear H6 H.
    generalize (BlocksOk (Generate (c fullImports a) (Nsucc n) n)); intuition.
    match type of H3 with
      | ?P -> _ => assert P by nomega
    end.
    intuition.
    apply (Forall_nth_error H6) in H4.
    eapply H4; eauto.
    intros.
    apply H0.

    generalize H3; clear.
    generalize (Blocks (Generate (c fullImports a) (Nsucc n) n)).
    unfold fullImports; simpl.
    generalize dependent n.
    induction l1; simpl; intuition.
    apply LabelFacts.add_mapsto_iff in H3; intuition; subst.

    Lemma skipImports : forall m l p bls,
      LabelMap.MapsTo (modName, Local l) (p, bls) m
      -> LabelMap.MapsTo (modName, Local l) p
      (LabelMap.fold
        (fun (l : LabelMap.key) (x : assert * block) (m : LabelMap.t assert) =>
          LabelMap.add l (fst x) m) m importsMap).
      clear BlocksGood.
      unfold importsMap.
      generalize NoSelfImport; clear NoSelfImport.
      generalize false at 2.
      intros; assert (forall v, ~LabelMap.MapsTo (modName, Local l) v (LabelMap.empty assert)).
      do 2 intro.
      apply LabelMap.empty_1 in H0; tauto.
      apply LabelMap.elements_1 in H.
      generalize (LabelMap.elements_3w m).
      generalize dependent (LabelMap.empty assert).
      induction imports; simpl in *; intuition.
      rewrite LabelMap.fold_1.
      generalize dependent t.
      induction (LabelMap.elements m); simpl; intuition.

      inversion H.
      inversion H1; clear H1; subst.
      inversion H; clear H; subst.
      hnf in H2; simpl in H2; intuition.
      destruct a; simpl in *; subst; simpl in *.
      generalize H4; clear.
      assert (LabelMap.MapsTo (modName, Local l) p (LabelMap.add (modName, Local l) p t)).
      apply LabelMap.add_1; auto.
      generalize dependent (LabelMap.add (modName, Local l) p t).
      induction l0; simpl; intuition; simpl.
      apply IHl0; auto.
      apply LabelMap.add_2.
      intro; subst.
      apply H4.
      constructor; hnf; auto.
      auto.

      intuition.
      apply H1; clear H1.
      intros.
      apply LabelFacts.add_mapsto_iff in H; intuition.
      destruct a as [ [ ] ]; simpl in *; subst; simpl in *.
      injection H; clear H; intros; subst.
      generalize H2 H4; clear.
      induction 1; simpl; intuition; eauto.
      apply H4.
      constructor.
      hnf in H; hnf; intuition.
      eauto.


      destruct a as [ [ ] ]; simpl in *.
      apply IHl0; auto.

      generalize NoSelfImport; clear.
      match goal with
        | [ |- context[?E || ?F] ] =>
          assert (E || F = false -> E = false) by (destruct b; auto);
            generalize dependent (E || F); generalize dependent E
      end.
      induction l0; simpl; intuition.
      destruct a as [ [ ] ]; simpl in *.
      eapply IHl0; [ | eassumption ].
      destruct b0; destruct b; simpl in *; intuition congruence.
      
      intros.
      apply LabelFacts.add_mapsto_iff in H2; intuition; subst.
      congruence.
      eauto.
    Qed.

    eapply skipImports.
    apply LabelMap.add_2.
    discriminate.
    apply LabelMap.add_1; auto.
    admit.
    admit.

    apply LabelFacts.add_mapsto_iff in H3; intuition; subst.
    injection H7; clear H7; intros; subst.
    simpl.
    destruct (PreconditionOk (Generate (c fullImports pre) (Nsucc n) n)).
    destruct (H0 (modName, Local (Nsucc n + Entry (Generate (c fullImports pre) (Nsucc n) n))) pre).
    eapply skipImports.

    clear H0 H6 H H2 H5 H1.
    generalize dependent (Generate (c fullImports pre) (Nsucc n) n).
    intro.
    generalize (Entry c0).
    intro.
    match goal with
      | [ |- context[fold_left _ _ (_, ?S)] ] => generalize S
    end.
    generalize dependent n0.
    generalize dependent (Nsucc n).
    do 2 intro.
    match goal with
      | [ |- context[fold_left _ ?L _] ] => generalize L; generalize n0; intros n' l; generalize n'; induction l
    end; simpl; intuition.

    match goal with
      | [ _ : nth_error nil ?N = Some _ |- _ ] => destruct N; discriminate
    end.

    case_eq (nat_of_N n1); intros.
    rewrite H in H3.
    injection H3; clear H3; intros; subst.
    replace (n'0 + n1) with n'0 by nomega.
    instantiate (1 := x).
    clear.
    assert (n'0 < Nsucc n'0) by nomega.
    generalize dependent (Nsucc n'0).
    generalize n'0.
    intros.
    assert (LabelMap.MapsTo (modName, Local n'1) (pre, x) (LabelMap.add (modName, Local n'1) (pre, x) t)) by (apply LabelMap.add_1; auto).
    generalize dependent (LabelMap.add (modName, Local n'1) (pre, x) t).
    generalize dependent n'1.
    generalize dependent n.
    induction l; simpl; intuition.
    apply IHl.
    nomega.
    apply LabelMap.add_2; auto.
    intro.
    injection H1; nomega.
    rewrite H in H3; simpl in H3.
    replace (n'0 + n1) with (Nsucc n'0 + (n1 - 1)) by (pre_nomega; rewrite nat_of_Nminus; nomega).
    apply IHl.
    replace (nat_of_N (n1 - 1)) with n2 by (rewrite nat_of_Nminus; nomega); auto.
    intuition.
    rewrite H7.
    eauto.


    admit.
  Qed.
End module.
