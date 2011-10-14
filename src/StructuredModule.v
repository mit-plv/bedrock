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

  Hypothesis NoDupFunc :
    match (List.fold_left (fun mOpt p => let '(mod, _, _) := p in
      match mOpt with
        | None => None
        | Some m => let k := (mod, Local 0) in
          if LabelMap.mem k m then None
          else Some (LabelMap.add k tt m)
      end) functions (Some (LabelMap.empty unit))) with
      | None => False
      | Some _ => True
    end.

  Hypothesis BlocksGood : List.Forall (fun f : function => let '(_, pre, c) := f in
    let cout := c fullImports pre in
    (forall stn_st specs, ~interp specs (Postcondition cout stn_st))
    /\ VerifCond cout) functions.

  Theorem bmoduleOk : moduleOk bmodule_.
    constructor.

    clear NoDupFunc BlocksGood.
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

    Theorem buildLocals_notImport' : forall k v Base bls Base',
      LabelMap.MapsTo k v (buildLocals bls Base')
      -> Base' >= Base
      -> exists l, k = (modName, Local l) /\ l >= Base /\ l < Base' + N_of_nat (length bls).
      unfold buildLocals; intros.
      assert (LabelMap.MapsTo k v (LabelMap.empty (assert * block)) -> exists l, k = (modName, Local l) /\ l >= Base /\ l < Base' + N_of_nat (length bls))
        by (intro uhoh; destruct (LabelMap.empty_1 uhoh)).
      generalize dependent (LabelMap.empty (assert * block)).
      generalize dependent Base'; clear; induction bls; simpl; intuition.
      assert (Nsucc Base' >= Base) by nomega.
      destruct (IHbls _ H2 _ H); clear IHbls; intuition.
      apply LabelFacts.add_mapsto_iff in H3; intuition; subst; eauto.
      repeat esplit.
      auto.
      nomega.
      destruct H4; intuition.
      repeat esplit; eauto.
      nomega.
      repeat esplit; eauto.
      nomega.
    Qed.

    Theorem buildLocals_notImport : forall k v Base bls,
      LabelMap.MapsTo k v (buildLocals bls Base)
      -> exists l, k = (modName, Local l) /\ l >= Base /\ l < Base + N_of_nat (length bls).
      intros; eapply buildLocals_notImport'; eauto; nomega.
    Qed.

    destruct (buildLocals_notImport _ _ H1); intuition; subst; eauto.
    eauto.


    red; simpl; unfold allPreconditions; simpl; intros.
    assert (0 < 1) by nomega.
    generalize dependent 1.
    assert (Hfuncs : List.Forall (fun f => let '(name, _, _) := f in ~LabelMap.In (name, Local 0) (LabelMap.empty unit)) functions).
    apply Forall_forall; intros.
    destruct x as [ [ ] ]; intro.
    destruct H0.
    destruct (LabelMap.empty_1 H0).
    generalize dependent (LabelMap.empty unit); clear NoDupFunc.
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
      clear NoDupFunc BlocksGood.
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

    Lemma buildLocals_In : forall k (v : assert * block) bls Base bm,
      LabelMap.MapsTo k v (snd (List.fold_left (fun b_m p => let '(b, m) := b_m in
        (Nsucc b, LabelMap.add (modName, Local b) p m)) bls (Base, bm)))
      -> In v bls \/ LabelMap.MapsTo k v bm.
      induction bls; simpl; intuition.
      apply IHbls in H; intuition.
      apply LabelFacts.add_mapsto_iff in H0; intuition.
    Qed.

    apply buildLocals_In in H8; intuition.
    destruct (LabelMap.empty_1 H10).

    intros.
    apply H0.

    Lemma imps_cases : forall k v ims exit post bls base,
      LabelMap.MapsTo k v (imps ims modName bls base exit post)
      -> (k = (modName, Local exit) /\ v = post)
      \/ LabelMap.MapsTo k v ims
      \/ exists n, exists bl, nth_error bls n = Some (v, bl) /\ k = (modName, Local (base + N_of_nat n)).
      induction bls; simpl; intuition.

      apply LabelFacts.add_mapsto_iff in H; intuition.

      apply LabelFacts.add_mapsto_iff in H; intuition; subst.      

      do 2 right; exists O; exists b; intuition.
      do 2 f_equal; nomega.

      apply IHbls in H1; intuition.
      destruct H1 as [ ? [ ] ]; intuition.
      do 2 right; exists (S x); exists x0; intuition.
      rewrite H2; do 2 f_equal; nomega.
    Qed.

    apply imps_cases in H10; intuition; subst.

    eapply skipImports.
    apply LabelMap.add_2.
    congruence.
    apply LabelMap.add_1; eauto.

    admit.

    destruct H10 as [? [ ] ]; intuition; subst.
    eapply skipImports.
    apply LabelMap.add_2.
    congruence.
    apply LabelMap.add_2.
    intro Ho; injection Ho; nomega.
    apply MapsTo_union1.
    apply getLocal.
    autorewrite with N; eauto.


    inversion Hfuncs; clear Hfuncs; subst.
    case_eq (LabelMap.mem (s, Local 0) t); intro Heq; rewrite Heq in *.
    elimtype False; generalize NoDupFunc; clear.
    induction l0; simpl; intuition.
    destruct a as [ [ ] ]; auto.
    eapply H5; eauto; try nomega.
    apply Forall_forall; intros.
    destruct x as [ [ ] ]; intros.
    destruct H10.
    apply LabelFacts.add_mapsto_iff in H10; simpl in H10; intuition; subst.
    injection H10; clear H10; intros; subst.
    elimtype False; generalize H9 NoDupFunc; clear.
    assert (LabelMap.MapsTo (s0, Local 0) tt (LabelMap.add (s0, Local 0) tt t)) by (apply LabelMap.add_1; auto).
    generalize dependent (LabelMap.add (s0, Local 0) tt t).
    induction l0; simpl; intuition; subst.
    assert (LabelMap.In (s0, Local 0) t0) by (hnf; eauto).
    apply LabelMap.mem_1 in H0.
    rewrite H0 in *.
    generalize NoDupFunc; clear.
    induction l0; simpl; intuition.
    destruct a as [ [ ] ]; intuition.
    destruct a as [ [ ] ].
    case_eq (LabelMap.mem (s, Local 0) t0); intro Heq; rewrite Heq in *.
    generalize NoDupFunc; clear.
    induction l0; simpl; intuition.
    destruct a as [ [ ] ]; intuition.
    eapply IHl0; try eapply NoDupFunc; eauto.
    apply LabelMap.add_2; auto.
    intro Ho; injection Ho; clear Ho; intros; subst.
    assert (LabelMap.In (s0, Local 0) t0) by (hnf; eauto).
    apply LabelMap.mem_1 in H1.
    congruence.
    specialize (proj1 (Forall_forall _ _) H12); clear H12; intro H12.
    apply H12 in H9; clear H12.
    apply H9; hnf; eauto.


    Lemma fold_mono : forall k v bs1 bs2 im1 im2,
      (forall v, LabelMap.MapsTo k v bs1 -> LabelMap.MapsTo k v bs2)
      -> (forall v, LabelMap.MapsTo k v im1 -> LabelMap.MapsTo k v im2 \/ exists v', LabelMap.MapsTo k (v, v') bs2)
      -> (forall v, LabelMap.MapsTo k v im2 -> forall v', LabelMap.MapsTo k v' bs2 -> False)
      -> LabelMap.MapsTo k v
      (LabelMap.fold
        (fun (l : LabelMap.key) (x : assert * block)
          (m : LabelMap.t assert) => LabelMap.add l (fst x) m)
        bs1 im1)
      -> LabelMap.MapsTo k v
      (LabelMap.fold
        (fun (l2 : LabelMap.key) (x : assert * block) (m : LabelMap.t assert) =>
          LabelMap.add l2 (fst x) m)
        bs2 im2).
      intros; rewrite LabelMap.fold_1 in *.
      assert (Hbs1 : forall v, SetoidList.InA (@LabelMap.eq_key_elt _) (k, v) (LabelMap.elements bs1)
        -> SetoidList.InA (@LabelMap.eq_key_elt _) (k, v) (LabelMap.elements bs2)).
      intros.
      apply LabelMap.elements_1.
      apply H.
      apply LabelMap.elements_2.
      assumption.
      clear H.
      assert (Him1 : forall v, SetoidList.InA (@LabelMap.eq_key_elt _) (k, v) (LabelMap.elements im1)
        -> SetoidList.InA (@LabelMap.eq_key_elt _) (k, v) (LabelMap.elements im2)
        \/ exists v', SetoidList.InA (@LabelMap.eq_key_elt _) (k, (v, v')) (LabelMap.elements bs2)).
      intros.
      apply LabelMap.elements_2 in H.
      apply H0 in H; intuition.
      left; apply LabelMap.elements_1; assumption.
      destruct H3.
      right; exists x; apply LabelMap.elements_1; assumption.
      clear H0.
      assert (Hbs2 : forall v, SetoidList.InA (@LabelMap.eq_key_elt _) (k, v) (LabelMap.elements im2)
        -> forall v', SetoidList.InA (@LabelMap.eq_key_elt _) (k, v') (LabelMap.elements bs2)
          -> False).
      intros.
      apply LabelMap.elements_2 in H.
      apply LabelMap.elements_2 in H0.
      eauto.
      clear H1.

      generalize dependent im1.
      induction (LabelMap.elements bs1); simpl in *; intuition.
      clear Hbs1.
      apply LabelMap.elements_1 in H2.
      apply Him1 in H2; clear Him1; intuition.
      specialize (Hbs2 _ H).
      generalize dependent im2.
      induction (LabelMap.elements bs2); simpl in *; intuition.
      
      apply LabelMap.elements_2; auto.

      apply IHl; eauto.
      apply LabelMap.elements_1.
      apply LabelMap.add_2.
      intro; subst.
      apply Hbs2 with (snd a); destruct a; constructor; hnf; auto.
      apply LabelMap.elements_2; assumption.


      destruct H.
      specialize (fun v H' => Hbs2 v H' _ H).
      generalize (LabelMap.elements_3w bs2).
      generalize dependent im2.
      induction (LabelMap.elements bs2); simpl in *; intuition.
      inversion H.
      inversion H0; clear H0; subst.
      destruct (LabelKey.eq_dec k (fst a)).
      hnf in e; subst.
      inversion H; clear H; subst.
      hnf in H1; simpl in H1; intuition; subst.
      clear H.
      destruct a; simpl in *; subst; simpl.

      generalize H3; clear.
      assert (LabelMap.MapsTo k v (LabelMap.add k v im2)) by (apply LabelMap.add_1; auto).
      generalize dependent (LabelMap.add k v im2).
      induction l; simpl; intuition; simpl.
      apply IHl; auto.
      apply LabelMap.add_2; auto.
      intro; subst.
      apply H3; constructor; hnf; auto.

      apply IHl; clear IHl; auto.
      intros.
      apply Hbs2 with v0.
      apply LabelMap.elements_2 in H'.
      apply LabelFacts.add_mapsto_iff in H'; intuition; subst.
      
      elimtype False.
      apply H3.
      eapply InA_weaken; [ eassumption | ].
      intros.
      hnf.
      hnf in H.
      tauto.
      inversion H; clear H; subst; intuition.
      hnf in H1; simpl in H1; intuition.
      
      apply H; auto.
      intros.
      eapply Hbs2.
      apply LabelMap.elements_2 in H'.
      apply LabelFacts.add_mapsto_iff in H'; intuition; subst.
      elimtype False; apply n; hnf; auto.
      apply LabelMap.elements_1; eauto.


      eapply IHl; clear IHl; eauto.
      intros.
      apply LabelMap.elements_2 in H.
      apply LabelFacts.add_mapsto_iff in H; intuition; subst.
      right; exists (snd (snd a)).
      apply Hbs1.
      destruct a as [ ? [ ] ]; simpl.
      constructor; hnf; auto.
      
      apply LabelMap.elements_1 in H1.
      intuition.
    Qed.

    intros.
    apply H0.
    eapply fold_mono; [ | | | eassumption ]; intuition.
    apply LabelMap.add_2.
    intro; subst.

    generalize NoDupFunc H10; clear.
    generalize (Nsucc n + N_of_nat (Datatypes.length (Blocks (Generate (c fullImports a) (Nsucc n) n)))).
    assert (LabelMap.MapsTo (s, Local 0) tt (LabelMap.add (s, Local 0) tt t)) by (apply LabelMap.add_1; auto).
    generalize dependent (LabelMap.add (s, Local 0) tt t).
    induction l0; simpl; intuition.
    destruct (LabelMap.empty_1 H10).
    destruct a0 as [ [ ] ].
    case_eq (LabelMap.mem (s0, Local 0) t0); intro Heq; rewrite Heq in *.
    generalize NoDupFunc; clear.
    induction l0 as [ | [ [ ] ] ]; simpl; intuition.
    apply LabelFacts.add_mapsto_iff in H10; intuition; subst.
    injection H1; clear H1; intros; subst.
    assert (LabelMap.In (s, Local 0) t0) by (hnf; eauto).
    apply LabelMap.mem_1 in H0; congruence.
    apply LabelFacts.add_mapsto_iff in H2; intuition; subst.
    congruence.
    apply MapsTo_union in H3; intuition.
    apply buildLocals_notImport in H0; destruct H0; intuition; congruence.
    eapply IHl0; try eapply NoDupFunc; eauto.
    apply LabelMap.add_2; auto.
    intro Ho; injection Ho; clear Ho; intros; subst.
    assert (LabelMap.In (s, Local 0) t0) by (hnf; eauto).
    apply LabelMap.mem_1 in H3; congruence.

    apply LabelMap.add_2.
    intro; subst.
    generalize H10; clear.
    match goal with
      | [ |- context[blocks _ ?N] ] => assert (n < N) by nomega; generalize dependent N
    end.
    induction l0 as [ | [ [ ] ] ]; simpl; intuition.
    destruct (LabelMap.empty_1 H10).
    apply LabelFacts.add_mapsto_iff in H10; intuition; subst.
    congruence.
    apply LabelFacts.add_mapsto_iff in H2; intuition; subst.
    injection H2; nomega.
    apply MapsTo_union in H3; intuition.
    assert (n < Nsucc n0) by nomega.
    generalize dependent (Blocks (Generate (c0 fullImports a0) (Nsucc n0) n0)).
    intro.
    generalize dependent (Nsucc n0); clear.
    unfold buildLocals.
    assert (forall v, ~LabelMap.MapsTo (modName, Local n) v (LabelMap.empty (assert * block))).
    red; intros.
    destruct (LabelMap.empty_1 H).
    generalize dependent (LabelMap.empty (assert * block)).
    induction l; simpl; intuition eauto.
    eapply IHl; [ | | eassumption ]; intros.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst.  
    injection H1; nomega.
    eauto.
    nomega.
    eapply IHl0; [ | eassumption ].
    nomega.

    apply MapsTo_union2; auto.
    intros.
    elimtype False.
    generalize H10 H13; clear.
    generalize (Blocks (Generate (c fullImports a) (Nsucc n) n)).
    intros.
    apply buildLocals_notImport in H13; destruct H13; intuition; subst.
    clear H.
    generalize dependent (Nsucc n + N_of_nat (Datatypes.length l)).
    induction l0 as [ | [ [ ] ] ]; simpl; intuition.
    destruct (LabelMap.empty_1 H10).
    apply LabelFacts.add_mapsto_iff in H10; intuition; subst.
    congruence.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst.
    injection H1; nomega.
    apply MapsTo_union in H3; intuition.
    apply buildLocals_notImport in H; destruct H; intuition.
    injection H3; nomega.
    eapply IHl0; [ | eassumption ].
    nomega.

    apply LabelFacts.add_mapsto_iff in H13; intuition; subst.

    eapply importsNotThis; hnf; eauto.

    apply LabelFacts.add_mapsto_iff in H15; intuition; subst.

    eapply importsNotThis; hnf; eauto.

    apply MapsTo_union in H16; intuition.

    apply buildLocals_notImport in H14; destruct H14; intuition; subst.
    eapply importsNotThis; hnf; eauto.

    Lemma blocksMod : forall k v fs Base,
      LabelMap.MapsTo k v (blocks fs Base)
      -> exists l, k = (modName, l).
      clear; induction fs as [ | [ ] ]; simpl; intuition.
      destruct (LabelMap.empty_1 H).
      apply LabelFacts.add_mapsto_iff in H; intuition; subst.
      eauto.
      apply LabelFacts.add_mapsto_iff in H1; intuition; subst.
      eauto.
      apply MapsTo_union in H2; intuition.
      apply buildLocals_notImport in H0; destruct H0; intuition; subst; eauto.
      eauto.
    Qed.

    destruct (blocksMod _ _ H14); subst.
    eapply importsNotThis; hnf; eauto.
  Qed.

End module.
