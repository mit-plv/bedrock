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

  Definition buildLocals (bls : list (assert * block)) Base := snd (List.fold_left (fun b_m p => let '(b, m) := b_m in
    (Nsucc b, LabelMap.add (modName, Local b) p m)) bls (Base, LabelMap.empty _)).

  Fixpoint blocks (fs : list function) (Base : N) : LabelMap.t (assert * block) :=
    match fs with
      | nil => LabelMap.empty _
      | (f, pre, c) :: fs' =>
        let cout := c fullImports pre in
        let cg := Generate cout (Nsucc Base) Base in
        LabelMap.add (modName, Global f) (pre, (nil, Uncond (RvLabel (modName, Local (Nsucc Base + Entry cg)))))
          (LabelMap.add (modName, Local Base) (Postcondition cout, (nil, Uncond (RvLabel (modName, Local Base))))
            (union (buildLocals (Blocks cg) (Nsucc Base))
              (blocks fs' (Nsucc Base + N_of_nat (length (Blocks cg))))))
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
    let cout := c fullImports pre in
    (forall stn_st specs, ~interp specs (Postcondition cout stn_st))
    /\ VerifCond cout) functions.

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
    apply LabelFacts.add_mapsto_iff in H; intuition; subst; eauto.
    apply LabelFacts.add_mapsto_iff in H2; intuition; subst; eauto.
    apply MapsTo_union in H3; intuition.

    Theorem buildLocals_notImport : forall k v bls Base,
      LabelMap.MapsTo k v (buildLocals bls Base)
      -> exists l, k = (modName, Local l).
      unfold buildLocals; intros.
      assert (LabelMap.MapsTo k v (LabelMap.empty (assert * block)) -> exists l, k = (modName, Local l))
        by (intro uhoh; destruct (LabelMap.empty_1 uhoh)).
      generalize dependent (LabelMap.empty (assert * block)).
      generalize Base; induction bls; simpl; intuition.
      destruct (IHbls _ _ H); intuition.
      apply LabelFacts.add_mapsto_iff in H1; intuition; subst; eauto.
      eauto.
    Qed.

    destruct (buildLocals_notImport _ _ H1); subst; eauto.
    eauto.


    red; simpl; unfold allPreconditions; simpl; intros.
    assert (0 < 1) by nomega.
    generalize dependent 1.
    induction functions; simpl; intuition.
    destruct (LabelMap.empty_1 H).
    destruct a as [ [ ] ]; simpl in *.
    inversion BlocksGood; clear BlocksGood; subst.
    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    injection H7; clear H7; intros; subst.
    simpl.
    destruct (H0 (modName, Local (Nsucc n + Entry (Generate (c fullImports pre) (Nsucc n) n))) pre).
    
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

    destruct (PreconditionOk (Generate (c fullImports pre) (Nsucc n) n)).

    eapply skipImports.
    apply LabelMap.add_2; [ congruence | ].
    apply LabelMap.add_2; [ intro Hd; injection Hd; nomega | ].
    apply MapsTo_union1.

    Lemma getLocal : forall v bls Base Entry,
      nth_error bls (nat_of_N Entry) = Some v
      -> LabelMap.MapsTo (modName, Local (Base + Entry)) v (buildLocals bls Base).
      unfold buildLocals; intros.
      generalize (LabelMap.empty (assert * block)).
      generalize dependent Base.
      generalize dependent Entry.
      induction bls; simpl; intuition.
      elimtype False.
      destruct (nat_of_N Entry); discriminate.
      destruct (N_eq_dec Entry 0); subst; simpl in *.
      injection H; clear H; intros; subst.
      replace (Base + 0) with Base by nomega.
      assert (LabelMap.MapsTo (modName, Local Base) (a0, b) (LabelMap.add (modName, Local Base) (a0, b) t))
        by (apply LabelMap.add_1; auto).
      generalize H; clear.
      generalize (LabelMap.add (modName, Local Base) (a0, b) t).
      assert (Base < Nsucc Base) by nomega.
      generalize dependent (Nsucc Base).
      induction bls; simpl; intuition; eauto.
      apply IHbls.
      nomega.
      apply LabelMap.add_2; eauto.
      intro Ho; injection Ho; nomega.

      replace (Base + Entry) with (Nsucc Base + (Entry - 1)) by nomega.
      apply IHbls.
      autorewrite with N; simpl.
      assert (nat_of_N Entry <> O).
      nomega.
      destruct (nat_of_N Entry); simpl in *.
      tauto.
      replace (n0 - 0)%nat with n0 by omega; auto.
    Qed.

    apply getLocal; eauto.
    intuition.
    rewrite H7.
    eauto.


    apply LabelFacts.add_mapsto_iff in H7; intuition; subst.
    injection H9; clear H9; intros; subst; simpl.
    elimtype False; eauto.

    apply MapsTo_union in H9; intuition.

    generalize (BlocksOk (Generate (c fullImports a) (Nsucc n) n)); intuition.
    assert (n < Nsucc n) by nomega; intuition.
    apply (proj1 (Forall_forall _ _) H11 (pre, bl)); clear H11; auto.
    admit.
    admit.


    eapply H5; eauto; try nomega.
    admit.
  Qed.

End module.
