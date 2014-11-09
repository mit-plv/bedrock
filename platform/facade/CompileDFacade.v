Set Implicit Arguments.

Require Import FacadeFacts.
Require Import DFacadeFacts.
Require Import Facade.
Require Import DFacade.

Require Import Facade.NameDecoration.
Require Import SyntaxExpr.
Require Import String.
Local Open Scope string_scope.

Require Import Option.
Require Import Bool.

Local Notation PRE := tmp_prefix.
Definition fun_ptr_varname := PRE ++ "fptr".

Fixpoint compile (s : Stmt) : Facade.Stmt :=
  match s with
    | Skip => Facade.Skip
    | Seq a b => Facade.Seq (compile a) (compile b)
    | If e t f => Facade.If e (compile t) (compile f)
    | While e c => Facade.While e (compile c)
    | Assign x e => Facade.Assign x e
    | Call x f args => 
      Facade.Seq 
        (Facade.Label fun_ptr_varname f)
        (Facade.Call x (Var fun_ptr_varname) args)
  end.

Lemma compile_no_assign_to_args (spec : OperationalSpec) : is_disjoint (Facade.assigned (compile (Body spec))) (ArgVars spec) = true.
  admit.
Qed.

Definition compile_op (spec : OperationalSpec) : Facade.OperationalSpec.
  refine
    (Facade.Build_OperationalSpec (ArgVars spec) (RetVar spec) (compile (Body spec)) (args_no_dup spec) (ret_not_in_args spec) _).
  eapply compile_no_assign_to_args.
Defined.

Require Import StringSet.

Lemma is_syntax_ok_seq_elim a b : is_syntax_ok (Seq a b) = true -> is_syntax_ok a = true /\ is_syntax_ok b = true.
  admit.
Qed.

Definition is_syntax_ok_e e := StringSet.for_all is_good_varname (FreeVarsExpr.free_vars e).

Lemma is_syntax_ok_if_elim e a b : is_syntax_ok (If e a b) = true -> is_syntax_ok_e e = true /\ is_syntax_ok a = true /\ is_syntax_ok b = true.
  admit.
Qed.

Lemma is_syntax_ok_while_elim e b : is_syntax_ok (While e b) = true -> is_syntax_ok_e e = true /\ is_syntax_ok b = true.
  admit.
Qed.

Lemma is_syntax_ok_assign_elim x e : is_syntax_ok (Assign x e) = true -> is_good_varname x = true /\ is_syntax_ok_e e = true.
  admit.
Qed.

Lemma is_syntax_ok_call_elim x f args : is_syntax_ok (Call x f args) = true -> is_good_varname x = true /\ List.forallb is_good_varname args = true.
  admit.
Qed.

Lemma is_syntax_ok_e_var_elim x : is_syntax_ok_e (Var x) = true -> is_good_varname x = true.
  admit.
Qed.

Lemma is_syntax_ok_e_binop_elim op a b : is_syntax_ok_e (Binop op a b) = true -> is_syntax_ok_e a = true /\ is_syntax_ok_e b = true.
  admit.
Qed.

Lemma is_syntax_ok_e_test_elim op a b : is_syntax_ok_e (TestE op a b) = true -> is_syntax_ok_e a = true /\ is_syntax_ok_e b = true.
  admit.
Qed.

Lemma syntax_ok_fptr_not_fv s : is_syntax_ok s = true -> ~ StringSet.In fun_ptr_varname (free_vars s).
  admit.
Qed.

Lemma iff_not_iff P Q : (P <-> Q) -> (~ P <-> ~ Q).
Proof.
  split; intros; intuition.
Qed.

Lemma singleton_not_iff x x' : ~ StringSet.In x' (StringSet.singleton x) <-> x' <> x.
Proof.
  eapply iff_not_iff.
  split; intros H.
  - eapply StringSetFacts.singleton_iff in H; eauto.
  - eapply StringSetFacts.singleton_iff; eauto.
Qed.

Section ADTValue.

  Variable ADTValue : Type.

  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation Value := (@Value ADTValue).
  Notation FuncSpec := (@FuncSpec ADTValue).
  Notation RunsTo := (@RunsTo ADTValue).
  Notation Safe := (@Safe ADTValue).

  Require Import Memory.
  Require Import GLabel.

  Notation FEnv := (@Facade.Env ADTValue).
  Notation FFuncSpec := (@Facade.FuncSpec ADTValue).
  Notation FRunsTo := (@Facade.RunsTo ADTValue).
  Notation FSafe := (@Facade.Safe ADTValue).

  Require Import GLabelMap.
  Import GLabelMap.

  Arguments Facade.Operational {ADTValue} _.

  Definition compile_spec (spec : FuncSpec) : FFuncSpec :=
    match spec with
      | Axiomatic s => Facade.Axiomatic s
      | Operational s => Facade.Operational (compile_op s)
    end.

  Definition fenv_impls_env (fenv : FEnv) (env : Env) :=
    forall lbl spec,
      find lbl env = Some spec ->
      exists w,
        Label2Word fenv lbl = Some w /\
        Word2Spec fenv w = Some (compile_spec spec).
    
  Require Import GeneralTactics.
  Require Import GeneralTactics3.
  Require Import GeneralTactics4.
  Require Import GeneralTactics5.

  Require Import List.
  Require Import ListFacts3.
  Require Import ListFacts4.

  Require Import Setoid.

  Require Import StringMap.
  Import StringMap.
  Require Import StringMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Hint Extern 0 (_ == _) => reflexivity.

  Arguments SCA {ADTValue} _.
  Arguments ADT {ADTValue} _.

  Lemma find_none_not_mapsto_adt x (st : State) : find x st = None -> not_mapsto_adt x st = true.
  Proof.
    intros Hf.
    unfold not_mapsto_adt, is_mapsto_adt.
    rewrite Hf.
    eauto.
  Qed.

  Lemma add_eq_elim elt k (v1 v2 : elt) m1 m2 : add k v1 m1 == add k v2 m2 -> v1 = v2 /\ remove k m1 == remove k m2.
  Proof.
    intros Heq.
    unfold Equal in *.
    split.
    - specialize (Heq k).
      rewrite add_eq_o in * by eauto.
      rewrite add_eq_o in * by eauto.
      inject Heq; eauto.
    - intros k'.
      destruct (string_dec k' k).
      + subst.
        repeat rewrite remove_eq_o by eauto.
        eauto.
      + repeat rewrite remove_neq_o by eauto.
        specialize (Heq k').
        rewrite add_neq_o in * by eauto.
        rewrite add_neq_o in * by eauto.
        eauto.
  Qed.

  Lemma add_add_comm elt k k' (v v' : elt) m : k <> k' -> add k v (add k' v' m) == add k' v' (add k v m).
  Proof.
    intros Hne.
    unfold Equal.
    intros k''.
    destruct (string_dec k'' k).
    - subst.
      rewrite add_eq_o by eauto.
      destruct (string_dec k k').
      + subst.
        intuition.
      + rewrite add_neq_o by eauto.
        rewrite add_eq_o by eauto.
        eauto.
    - rewrite add_neq_o by eauto.
      destruct (string_dec k'' k').
      + subst.
        rewrite add_eq_o by eauto.
        rewrite add_eq_o by eauto.
        eauto.
      + rewrite add_neq_o by eauto.
        rewrite add_neq_o by eauto.
        rewrite add_neq_o by eauto.
        eauto.
  Qed.
  Arguments add_add_comm [elt] k k' _ _ _ _ _.

  Lemma remove_add_comm elt k k' (v' : elt) m : k <> k' -> remove k (add k' v' m) == add k' v' (remove k m).
  Proof.
    intros Hne.
    unfold Equal.
    intros k''.
    destruct (string_dec k'' k).
    - subst.
      rewrite remove_eq_o by eauto.
      destruct (string_dec k k').
      + subst.
        intuition.
      + rewrite add_neq_o by eauto.
        rewrite remove_eq_o by eauto.
        eauto.
    - rewrite remove_neq_o by eauto.
      destruct (string_dec k'' k').
      + subst.
        rewrite add_eq_o by eauto.
        rewrite add_eq_o by eauto.
        eauto.
      + rewrite add_neq_o by eauto.
        rewrite add_neq_o by eauto.
        rewrite remove_neq_o by eauto.
        eauto.
  Qed.

  Lemma add_remove_comm elt k k' (v : elt) m : k <> k' -> add k v (remove k' m) == remove k' (add k v m).
  Proof.
    intros Hne.
    unfold Equal.
    intros k''.
    destruct (string_dec k'' k).
    - subst.
      rewrite add_eq_o by eauto.
      destruct (string_dec k k').
      + subst.
        intuition.
      + rewrite remove_neq_o by eauto.
        rewrite add_eq_o by eauto.
        eauto.
    - rewrite add_neq_o by eauto.
      destruct (string_dec k'' k').
      + subst.
        rewrite remove_eq_o by eauto.
        rewrite remove_eq_o by eauto.
        eauto.
      + rewrite remove_neq_o by eauto.
        rewrite remove_neq_o by eauto.
        rewrite add_neq_o by eauto.
        eauto.
  Qed.

  Lemma remove_remove_comm elt k k' (m : t elt) : k <> k' -> remove k (remove k' m) == remove k' (remove k m).
  Proof.
    intros Hne.
    unfold Equal.
    intros k''.
    destruct (string_dec k'' k).
    - subst.
      rewrite remove_eq_o by eauto.
      destruct (string_dec k k').
      + subst.
        intuition.
      + rewrite remove_neq_o by eauto.
        rewrite remove_eq_o by eauto.
        eauto.
    - rewrite remove_neq_o by eauto.
      destruct (string_dec k'' k').
      + subst.
        rewrite remove_eq_o by eauto.
        rewrite remove_eq_o by eauto.
        eauto.
      + rewrite remove_neq_o by eauto.
        rewrite remove_neq_o by eauto.
        rewrite remove_neq_o by eauto.
        eauto.
  Qed.
  Arguments remove_remove_comm [elt] k k' _ _ _.

  Lemma add_remove_eq_false elt k (v : elt) m1 m2 : ~ add k v m1 == remove k m2.
  Proof.
    intro H.
    unfold Equal in *.
    specialize (H k).
    rewrite add_eq_o in * by eauto.
    rewrite remove_eq_o in * by eauto.
    discriminate.
  Qed.

  Lemma add_remove_many_Equal ks : forall types vs st1 st2, st1 == st2 -> @add_remove_many ADTValue ks types vs st1 == add_remove_many ks types vs st2.
  Proof.
    induction ks; destruct types; destruct vs; simpl; try solve [intuition].
    intros st1 st2 Heq.
    rename a into k.
    destruct v as [w | a].
    - eauto.
    - destruct o as [o|].
      + eapply IHks; eauto.
        rewrite Heq; eauto.
      + eapply IHks; eauto.
        rewrite Heq; eauto.
  Qed.

  Global Add Morphism (@add_remove_many ADTValue)
      with signature eq ==> eq ==> eq ==> Equal ==> Equal as add_remove_many_m.
  Proof.
    intros; eapply add_remove_many_Equal; eauto.
  Qed.

  Lemma add_remove_many_add_comm ks : forall vs types k v (st : State), ~ List.In k ks -> add_remove_many ks types vs (add k v st) == add k v (add_remove_many ks types vs st).
  Proof.
    induction ks; destruct vs; destruct types; simpl; try solve [intuition].
    intros k' v' st Hnin .
    intuition.
    rename a into k.
    destruct v as [w | a].
    - eauto.
    - destruct o as [o |].
      + rewrite add_add_comm by eauto.
        eauto.
      + rewrite remove_add_comm by eauto.
        eauto.
  Qed.

  Lemma add_remove_many_remove_comm ks : forall vs types k (st : State), ~ List.In k ks -> add_remove_many ks types vs (remove k st) == remove k (add_remove_many ks types vs st).
  Proof.
    induction ks; destruct vs; destruct types; simpl; try solve [intuition].
    intros k' st Hnin .
    intuition.
    rename a into k.
    destruct v as [w | a].
    - eauto.
    - destruct o as [o |].
      + rewrite add_remove_comm by eauto.
        eauto.
      + rewrite remove_remove_comm by eauto.
        eauto.
  Qed.

  Section EqualOn.

    Variable Domain : key -> Prop.

    Variable elt : Type.

    Definition EqualOn (m1 m2 : t elt) := forall k, Domain k -> find k m1 = find k m2.

    Infix "===" := EqualOn (at level 70).

    Lemma EqualOn_refl a : a === a.
    Proof.
      unfold EqualOn.
      eauto.
    Qed.

    Lemma EqualOn_sym a b : a === b -> b === a.
    Proof.
      intros H.
      unfold EqualOn in *; intros.
      symmetry; eauto.
    Qed.

    Lemma EqualOn_trans a b c : a === b -> b === c -> a === c.
    Proof.
      intros H1 H2.
      unfold EqualOn in *; intros.
      etransitivity. 
      - eapply H1; eauto.
      - eauto.
    Qed.

    Global Add Relation (t elt) EqualOn
        reflexivity proved by EqualOn_refl
        symmetry proved by EqualOn_sym
        transitivity proved by EqualOn_trans
          as EqualOn_rel.

    Lemma Equal_EqualOn a a' b b' : a == a' -> b == b' -> (a === b <-> a' === b').
    Proof.
      intros Ha Hb.
      split; intros H.
      - unfold EqualOn in *.
        intros k Hk.
        rewrite <- Ha.
        rewrite <- Hb.
        eapply H; eauto.
      - unfold EqualOn in *.
        intros k Hk.
        rewrite Ha.
        rewrite Hb.
        eapply H; eauto.
    Qed.

    Global Add Morphism EqualOn
        with signature Equal ==> Equal ==> iff as Equal_EqualOn_m.
    Proof.
      intros; eapply Equal_EqualOn; eauto.
    Qed.

    Lemma add_EqualOn k v m1 m2 : m1 === m2 -> add k v m1 === add k v m2.
    Proof.
      intros Heq.
      unfold EqualOn in *.
      intros k' Hk'.
      destruct (string_dec k' k) as [Heqk | Hnek].
      - subst.
        repeat rewrite add_eq_o by eauto.
        eauto.
      - repeat rewrite add_neq_o by eauto.
        eauto.
    Qed.

    Lemma remove_EqualOn k m1 m2 : m1 === m2 -> remove k m1 === remove k m2.
    Proof.
      intros Heq.
      unfold EqualOn in *.
      intros k' Hk'.
      destruct (string_dec k' k) as [Heqk | Hnek].
      - subst.
        repeat rewrite remove_eq_o by eauto.
        eauto.
      - repeat rewrite remove_neq_o by eauto.
        eauto.
    Qed.

    Global Add Morphism (@add elt) with signature eq ==> eq ==> EqualOn ==> EqualOn as add_EqualOn_m.
    Proof.
      intros; eapply add_EqualOn; eauto.
    Qed.

    Global Add Morphism (@remove elt) with signature eq ==> EqualOn ==> EqualOn as remove_EqualOn_m.
    Proof.
      intros; eapply remove_EqualOn; eauto.
    Qed.

    Lemma out_add_EqualOn a b k v : a === b -> ~ Domain k -> add k v a === b.
    Proof.
      intros Heq Hk.
      unfold EqualOn in *.
      intros k' Hk'.
      destruct (string_dec k' k) as [? | Hne].
      - subst.
        contradiction.
      - rewrite add_neq_o by eauto.
        eapply Heq; eauto.
    Qed.

  End EqualOn.

  Existing Instance EqualOn_rel_Reflexive.
  Existing Instance EqualOn_rel_Symmetric.
  Existing Instance EqualOn_rel_Transitive.

  Section equiv.

    Variable s : StringSet.t.

    Definition no_adt_in (m : State) := forall k, StringSet.In k s -> not_mapsto_adt k m = true.

    Definition equiv a b := EqualOn (fun k => ~ StringSet.In k s) a b /\ no_adt_in a /\ no_adt_in b.

    Infix "===" := equiv (at level 70).

    Lemma equiv_sym a b : a === b -> b === a.
    Proof.
      intros H; unfold equiv in *.
      openhyp.
      repeat try_split; eauto.
      symmetry; eauto.
    Qed.

    Lemma equiv_trans a b c : a === b -> b === c -> a === c.
    Proof.
      intros H1 H2.
      unfold equiv in *.
      openhyp.
      repeat try_split; eauto.
      etransitivity; eauto.
    Qed.

    Global Add Relation State equiv
        symmetry proved by equiv_sym
        transitivity proved by equiv_trans
          as equiv_rel.

    Lemma Equal_not_mapsto_adt (st st' : State) k : st == st' -> not_mapsto_adt k st = not_mapsto_adt k st'.
    Proof.
      intros Heq.
      unfold not_mapsto_adt, is_mapsto_adt.
      rewrite Heq.
      eauto.
    Qed.
    
    Global Add Morphism (@not_mapsto_adt ADTValue) with signature eq ==> Equal ==> eq as Equal_not_mapsto_adt_m.
    Proof.
      intros; eapply Equal_not_mapsto_adt; eauto.
    Qed.

    Lemma Equal_no_adt_in st st' : st == st' -> (no_adt_in st <-> no_adt_in st').
    Proof.
      intros Heq.
      unfold no_adt_in in *.
      split; intros H.
      - intros k Hk.
        rewrite <- Heq; eauto.
      - intros k Hk.
        rewrite Heq; eauto.
    Qed.

    Global Add Morphism no_adt_in with signature Equal ==> iff as Equal_no_adt_in_m.
    Proof.
      intros; eapply Equal_no_adt_in; eauto.
    Qed.

    Lemma Equal_equiv a a' b b' : a == a' -> b == b' -> (a === b <-> a' === b').
    Proof.
      intros Ha Hb.
      unfold equiv in *.
      split; intro H.
      - rewrite <- Ha.
        rewrite <- Hb.
        eauto.
      - rewrite Ha.
        rewrite Hb.
        eauto.
    Qed.

    Global Add Morphism equiv 
        with signature Equal ==> Equal ==> iff as Equal_equiv_m.
    Proof.
      intros; eapply Equal_equiv; eauto.
    Qed.

    Lemma find_adt_equiv st1 st2 k a : find k st1 = Some (ADT a) -> st1 === st2 -> find k st2 = Some (ADT a).
    Proof.
      intros Hf Heqv.
      unfold equiv in *.
      destruct Heqv as [Heqon [Hnadt1 Hnadt2]].
      destruct (StringSetFacts.In_dec k s) as [Hin | Hnin].
      - eapply Hnadt1 in Hin.
        eapply not_mapsto_adt_iff in Hin.
        contradict Hin.
        eexists; eauto.
      - rewrite <- Heqon by eauto.
        eauto.
    Qed.

  End equiv.

  Existing Instance equiv_rel_Symmetric.
  Existing Instance equiv_rel_Transitive.

  Lemma not_in_no_adt_in_add s k v st : no_adt_in s st -> ~ StringSet.In k s -> no_adt_in s (add k v st).
  Proof.
    intros H Hnin.
    unfold no_adt_in in *.
    intros k' Hk'.
    unfold not_mapsto_adt in *.
    unfold is_mapsto_adt in *.
    destruct (string_dec k k') as [Heqk | Hnek].
    - subst.
      contradiction.
    - rewrite add_neq_o by eauto.
      eauto.
  Qed.

  Lemma no_adt_in_remove s k st : no_adt_in s st -> no_adt_in s (remove k st).
  Proof.
    intros H.
    unfold no_adt_in in *.
    intros k' Hk'.
    unfold not_mapsto_adt in *.
    unfold is_mapsto_adt in *.
    destruct (string_dec k k') as [Heqk | Hnek].
    - subst.
      rewrite remove_eq_o by eauto.
      eauto.
    - rewrite remove_neq_o by eauto.
      eauto.
  Qed.

  Coercion StringSet.singleton : StringSet.elt >-> StringSet.t.

  Notation equivf := (equiv (StringSet.singleton fun_ptr_varname)).
  Infix "===" := equivf (at level 70).

  Lemma not_mapsto_adt_no_adt_in x st : not_mapsto_adt x st = true -> no_adt_in (StringSet.singleton x) st.
  Proof.
    intros Hnadt.
    unfold no_adt_in.
    intros k Hk.
    eapply StringSetFacts.singleton_iff in Hk.
    subst.
    eauto.
  Qed.

  Lemma equiv_refl st : not_mapsto_adt fun_ptr_varname st = true -> st === st.
  Proof.
    intros Hnadt.
    unfold equiv.
    repeat try_split.
    - reflexivity.
    - eapply not_mapsto_adt_no_adt_in; eauto.
    - eapply not_mapsto_adt_no_adt_in; eauto.
  Qed.

  Lemma no_adt_in_add_sca k w st : no_adt_in (StringSet.singleton k) (add k (SCA w) st).
  Proof.
    unfold no_adt_in.
    intros k' Hk'.
    eapply StringSetFacts.singleton_iff in Hk'.
    subst.
    unfold not_mapsto_adt, is_mapsto_adt.
    rewrite add_eq_o by eauto.
    eauto.
  Qed.

  Lemma equiv_intro st1 st2 w st1' : st1' === st2 -> st1 == add fun_ptr_varname (SCA w) st2 -> st1 === st2.
  Proof.
    intros Heqv Heq.
    unfold equiv in *.
    destruct Heqv as [Heqon [Hnadt1 Hnadt2]].
    rewrite Heq.
    repeat try_split.
    - eapply out_add_EqualOn.
      + reflexivity.
      + intros Hnot; eapply Hnot.
        eapply StringSetFacts.singleton_iff; eauto.
    - eapply no_adt_in_add_sca; eauto.
    - eauto.
  Qed.

  Lemma fun_ptr_varname_not_good_varname : is_good_varname fun_ptr_varname = false.
  Proof.
    intuition.
  Qed.

  Lemma find_equiv st1 st2 x : st1 === st2 -> is_good_varname x = true -> find x st1 = find x st2.
  Proof.
    intros Heq Hgn.
    unfold equiv in *.
    simpl in *.
    destruct Heq as [Heq [Hnadt1 Hnadt2]].
    destruct (string_dec x fun_ptr_varname) as [Heqx | Hnex].
    - subst.
      rewrite fun_ptr_varname_not_good_varname in Hgn.
      discriminate.
    - eapply Heq.
      eapply singleton_not_iff; eauto.
  Qed.
  Arguments find_equiv st1 st2 [_] _ _.

  Section good_varname_x.

    Variable x : string.
    Hypothesis Hgn : is_good_varname x = true.

    Global Add Morphism (find x) with signature equivf ==> eq as find_equiv_m.
    Proof.
      intros; eapply find_equiv; eauto.
    Qed.

    Lemma not_mapsto_adt_equiv st1 st2 : st1 === st2 -> not_mapsto_adt x st1 = not_mapsto_adt x st2.
    Proof.
      intros Heq.
      unfold not_mapsto_adt, is_mapsto_adt.
      rewrite Heq.
      eauto.
    Qed.

    Lemma add_equiv st1 st2 v : st1 === st2 -> add x v st1 === add x v st2.
    Proof.
      intros Heq.
      unfold equiv in *.
      destruct Heq as [Heqon [Hnadt1 Hnadt2]].
      repeat try_split.
      - eapply add_EqualOn; eauto.
      - destruct (string_dec fun_ptr_varname x) as [Heqx | Hnex].
        + subst.
          discriminate Hgn.
        + eapply not_in_no_adt_in_add; eauto.
          eapply singleton_not_iff; eauto.
      - destruct (string_dec fun_ptr_varname x) as [Heqx | Hnex].
        + subst.
          discriminate Hgn.
        + eapply not_in_no_adt_in_add; eauto.
          eapply singleton_not_iff; eauto.
    Qed.

    Lemma remove_equiv st1 st2 : st1 === st2 -> remove x st1 === remove x st2.
    Proof.
      intros Heq.
      unfold equiv in *.
      destruct Heq as [Heqon [Hnadt1 Hnadt2]].
      repeat try_split.
      - eapply remove_EqualOn; eauto.
      - destruct (string_dec fun_ptr_varname x) as [Heqx | Hnex].
        + subst.
          discriminate Hgn.
        + eapply no_adt_in_remove; eauto.
      - destruct (string_dec fun_ptr_varname x) as [Heqx | Hnex].
        + subst.
          discriminate Hgn.
        + eapply no_adt_in_remove; eauto.
    Qed.

  End good_varname_x.
    
  Lemma mapM_find_equiv st1 st2 ls : st1 === st2 -> List.forallb is_good_varname ls = true -> mapM (sel st1) ls = mapM (sel st2) ls.
  Proof.
    induction ls; simpl; intros Heqv Hgn.
    - eauto.
    - rename a into k.
      eapply andb_true_iff in Hgn.
      destruct Hgn as [Hgnk Hgn].
      unfold sel in *.
      rewrite (find_equiv st1 st2) by eauto.
      destruct (option_dec (find k st2)) as [ [v Heq] | Hneq]; [rewrite Heq | rewrite Hneq]; try discriminate; try reflexivity.
      rewrite IHls by eauto.
      eauto.
  Qed.
  Arguments mapM_find_equiv st1 st2 [_] _ _.

  Lemma map_find_equiv st1 st2 ls : st1 === st2 -> List.forallb is_good_varname ls = true -> List.map (sel st1) ls = List.map (sel st2) ls.
  Proof.
    induction ls; simpl; intros Heqv Hgn.
    - eauto.
    - rename a into x.
      eapply andb_true_iff in Hgn.
      destruct Hgn as [Hgnx Hgn].
      f_equal.
      + eapply find_equiv; eauto.
      + eauto.
  Qed.
  Arguments map_find_equiv st1 st2 [_] _ _.

  Lemma eval_equiv st1 st2 e : st1 === st2 -> is_syntax_ok_e e = true -> eval st1 e = eval st2 e.
  Proof.
    induction e; simpl; intros Heqv Hsyn.
    - eapply is_syntax_ok_e_var_elim in Hsyn.
      eapply find_equiv; eauto.
    - eauto.
    - eapply is_syntax_ok_e_binop_elim in Hsyn.
      openhyp.
      rewrite IHe1; eauto.
      rewrite IHe2; eauto.
    - eapply is_syntax_ok_e_test_elim in Hsyn.
      openhyp.
      rewrite IHe1; eauto.
      rewrite IHe2; eauto.
  Qed.
  Arguments eval_equiv st1 st2 [_] _ _.

  Lemma eval_bool_equiv st1 st2 e : st1 === st2 -> is_syntax_ok_e e = true -> eval_bool st1 e = eval_bool st2 e.
  Proof.
    intros Heq Hsyn.
    unfold eval_bool in *.
    rewrite (eval_equiv st1 st2) by eauto; eauto.
  Qed.
  Arguments eval_bool_equiv st1 st2 [_] _ _.

  Lemma is_false_equiv st1 st2 e : is_false st1 e -> st1 === st2 -> is_syntax_ok_e e = true -> is_false st2 e.
  Proof.
    intros H Heq Hsyn.
    unfold is_false in *.
    rewrite (eval_bool_equiv st1 st2) in H by eauto; eauto.
  Qed.

  Lemma is_true_equiv st1 st2 e : is_true st1 e -> st1 === st2 -> is_syntax_ok_e e = true -> is_true st2 e.
  Proof.
    intros H Heq Hsyn.
    unfold is_true in *.
    rewrite (eval_bool_equiv st1 st2) in H by eauto; eauto.
  Qed.

  Lemma no_adt_leak_equiv st1 st2 input avars rvar : no_adt_leak input avars rvar st2 -> st1 === st2 -> no_adt_leak input avars rvar st1.
  Proof.
    intros H Heq.
    unfold no_adt_leak in *.
    intros; eapply H; eauto.
    eapply find_adt_equiv; eauto.
  Qed.

  Fixpoint output_eqv A (types : list Value) (output1 output2 : list A) := 
    match types, output1, output2 with
      | i :: types', o1 :: output1', o2 :: output2' => 
        match i with
          | ADT _ => o1 = o2 
          | _ => True
        end /\ output_eqv types' output1' output2'
      | nil, nil, nil => True
      | _, _, _ => False
    end.

  Lemma output_eqv_refl A types : forall (output : list A), length types = length output -> output_eqv types output output.
  Proof.
    induction types; destruct output; simpl; intuition.
    destruct a; eauto.
  Qed.

  Lemma add_remove_many_equiv args : forall types output1 output2 st1 st2, st1 === st2 -> List.forallb is_good_varname args = true -> output_eqv types output1 output2 -> length args = length types -> add_remove_many args types output1 st1 === add_remove_many args types output2 st2.
  Proof.
    induction args; destruct types; destruct output1; destruct output2; simpl; try solve [intros; try discriminate; intuition eauto].
    intros st1 st2 Heqv Hgn Hoeqv Hlen.
    inject Hlen.
    rename H into Hlen.
    rename a into k.
    eapply andb_true_iff in Hgn.
    destruct Hgn as [Hgnk Hgn].
    destruct Hoeqv as [Hv Hoeqv].
    destruct v as [w | a].
    - eauto.
    - subst.
      eapply IHargs; eauto.
      destruct o0 as [o|].
      + eapply add_equiv; eauto.
      + eapply remove_equiv; eauto.
  Qed.

  Definition not_mapsto_adt_types (k : string) ks types := forall i, nth_error ks i = Some k -> ~ exists a : ADTValue, nth_error types i = Some (ADT a).

  Lemma not_in_not_mapsto_adt_types k ks types : ~ List.In k ks -> not_mapsto_adt_types k ks types.
  Proof.
    intros Hnin.
    unfold not_mapsto_adt_types in *.
    intros i Hnth Hex.
    contradict Hnin.
    eapply Locals.nth_error_In; eauto.
  Qed.

  Lemma not_mapsto_adt_types_cons_neq_elim ks types k k' type : not_mapsto_adt_types k (k' :: ks) (type :: types) -> k <> k' -> not_mapsto_adt_types k ks types.
  Proof.
    intros H Hne.
    unfold not_mapsto_adt_types in *.
    intros i Hnth Hex.
    eapply (H (S i)); simpl in *; eauto.
  Qed.

  Lemma not_mapsto_adt_types_cons_neq_intro ks types k k' type : not_mapsto_adt_types k ks types -> k <> k' -> not_mapsto_adt_types k (k' :: ks) (type :: types).
  Proof.
    intros H Hne.
    unfold not_mapsto_adt_types in *.
    intros i Hnth [a Ha].
    destruct i as [|i]; simpl in *.
    - inject Hnth.
      intuition.
    - eapply H; eauto.
  Qed.

  Lemma not_mapsto_adt_types_adt k ks a types : ~ not_mapsto_adt_types k (k :: ks) (ADT a :: types).
  Proof.
    unfold not_mapsto_adt_types.
    intros H.
    eapply (H 0); simpl in *; eauto.
  Qed.

  Lemma not_mapsto_adt_types_sca k ks w types : not_mapsto_adt_types k ks types -> not_mapsto_adt_types k (k :: ks) (SCA w :: types).
  Proof.
    intros H.
    unfold not_mapsto_adt_types in *.
    intros i Hnth [a Ha].
    destruct i as [|i]; simpl in *.
    - discriminate.
    - eapply H; eauto.
  Qed.

  Lemma not_mapsto_adt_types_nil k types : not_mapsto_adt_types k nil types.
  Proof.
    unfold not_mapsto_adt_types; intros.
    rewrite nth_error_nil in *.
    discriminate.
  Qed.

  Lemma mapM_not_mapsto_adt_types ks : forall types k st, not_mapsto_adt k st = true -> mapM (sel st) ks = Some types -> not_mapsto_adt_types k ks types.
  Proof.
    induction ks; destruct types; simpl; try discriminate; intros k st Hnadt Hmm.
    - eapply not_mapsto_adt_types_nil.
    - rename k into k'.
      rename a into k.
      destruct (option_dec (sel st k)) as [ [v Heq] | Hneq]; [rewrite Heq in Hmm | rewrite Hneq in Hmm]; try discriminate.
      destruct (option_dec (mapM (sel st) ks)) as [ [vs Heqs] | Hneq]; [rewrite Heqs in Hmm | rewrite Hneq in Hmm]; try discriminate.
    - rename k into k'.
      rename a into k.
      destruct (option_dec (sel st k)) as [ [ty Heq] | Hneq]; [rewrite Heq in Hmm | rewrite Hneq in Hmm]; try discriminate.
      destruct (option_dec (mapM (sel st) ks)) as [ [tys Heqs] | Hneq]; [rewrite Heqs in Hmm | rewrite Hneq in Hmm]; try discriminate.
      inject Hmm.
      destruct (string_dec k' k) as [Heqk | Hnek].
      + subst.
        destruct v as [w | a].
        * eapply not_mapsto_adt_types_sca; eauto.
        * eapply not_mapsto_adt_iff in Hnadt.
          contradict Hnadt; eexists; eauto.
      + eapply not_mapsto_adt_types_cons_neq_intro; eauto.
  Qed.

  Lemma add_remove_many_eq_output_eqv ks : forall types st1 st2 vs1 vs2 k, remove k (add_remove_many ks types vs1 st1) == remove k (add_remove_many ks types vs2 st2) -> not_mapsto_adt_types k ks types -> length ks = length types -> length ks = length vs1 -> length ks = length vs2 -> NoDup ks -> output_eqv types vs1 vs2.
  Proof.
    induction ks; destruct types; destruct vs1; destruct vs2; simpl; try solve [intros; try discriminate; intuition eauto]; intros k Heq Hnadt Hlent Hlen1 Hlen2 Hnd.
    {
      inject Hlent.
      rename H into Hlent.
      inject Hlen1.
      rename H into Hlen1.
      inject Hlen2.
      rename H into Hlen2.
      rename a into k0.
      inversion Hnd; subst.
      rename H1 into Hnin.
      rename H2 into Hnd'.
      destruct v as [w | a].
      {
        destruct (string_dec k k0) as [Hkeq | Hkne].
        - subst.
          split; eauto.
          eapply IHks; eauto.
          eapply not_in_not_mapsto_adt_types; eauto.
        - eapply not_mapsto_adt_types_cons_neq_elim in Hnadt; eauto.
      }
      {
        destruct (string_dec k k0) as [Hkeq | Hkne].
        {
          subst.
          eapply not_mapsto_adt_types_adt in Hnadt; intuition.
        }
        {
          eapply not_mapsto_adt_types_cons_neq_elim in Hnadt; eauto.
          destruct o as [o1|]; destruct o0 as [o2|].
          {
            split.
            - repeat rewrite add_remove_many_add_comm in Heq by eauto.
              repeat rewrite remove_add_comm in Heq by eauto.
              eapply add_eq_elim in Heq.
              openhyp; subst; eauto.
            - eauto.
          }
          {
            repeat rewrite add_remove_many_add_comm in Heq by eauto.
            repeat rewrite add_remove_many_remove_comm in Heq by eauto.
            repeat rewrite remove_add_comm in Heq by eauto.
            rewrite remove_remove_comm in Heq by eauto.
            eapply add_remove_eq_false in Heq; intuition.
          }
          {
            repeat rewrite add_remove_many_add_comm in Heq by eauto.
            repeat rewrite add_remove_many_remove_comm in Heq by eauto.
            repeat rewrite remove_add_comm in Heq by eauto.
            rewrite remove_remove_comm in Heq by eauto.
            symmetry in Heq.
            eapply add_remove_eq_false in Heq; intuition.
          }
          {
            eauto.
          }            
        }
      }
    }
  Qed.

  Lemma add_add_remove_many_eq_elim types k ks v1 vs1 v2 vs2 (st : State) : not_mapsto_adt k st = true -> List.NoDup ks -> add k v1 (add_remove_many ks types vs1 st) == add k v2 (add_remove_many ks types vs2 st) -> mapM (sel st) ks = Some types -> length ks = length vs1 -> length ks = length vs2 -> v1 = v2 /\ output_eqv types vs1 vs2.
  Proof.
    intros Hnadt Hnd Heq Hlen1 Hlen2.
    eapply add_eq_elim in Heq.
    destruct Heq as [Hveq Hmeq].
    split; eauto.
    eapply add_remove_many_eq_output_eqv; eauto.
    - eapply mapM_not_mapsto_adt_types; eauto.
    - eapply mapM_length; eauto.
  Qed.

  Lemma args_name_ok_make_map avars input : forallb is_good_varname avars = true -> @not_mapsto_adt ADTValue fun_ptr_varname (make_map avars input) = true.
  Proof.
    intros Hgn.
    eapply find_none_not_mapsto_adt.
    eapply not_find_in_iff.
    eapply make_map_not_in.
    intros Hin.
    eapply forallb_forall in Hgn; eauto.
    rewrite fun_ptr_varname_not_good_varname in Hgn; discriminate.
  Qed.

  (* need some clever induction hypothesis strengthening to utilize induction hypothesis generated from the call case of FRunsTo *)
  Theorem compile_runsto' t t_env t_st t_st' :
    FRunsTo t_env t t_st t_st' -> 
    forall s_env, 
      fenv_impls_env t_env s_env -> 
      (forall s, 
         t = compile s -> 
         is_syntax_ok s = true -> 
         forall s_st,
           Safe s_env s s_st -> 
           s_st === t_st ->
           exists s_st',
             RunsTo s_env s s_st s_st' /\
             s_st' === t_st') /\
      (forall x f args f_w spec input t_callee_st' ret,
         t = Facade.Call x f args ->
         eval t_st f = Some (SCA f_w) ->
         Word2Spec t_env f_w = Some (Facade.Operational (compile_op spec)) ->
         mapM (sel t_st) args = Some input ->
         let body := Body spec in
         let avars := ArgVars spec in 
         let retvar := RetVar spec in
         let callee_st := make_map avars input in
         Safe s_env body callee_st ->
         FRunsTo t_env (compile body) callee_st t_callee_st' ->
         sel t_callee_st' retvar = Some ret ->
         no_adt_leak input avars retvar t_callee_st' ->
         let output := List.map (sel t_callee_st') avars in
         t_st' == add x ret (add_remove_many args input output t_st) ->
         exists s_callee_st',
           RunsTo s_env body callee_st s_callee_st' /\
           output_eqv input (List.map (sel s_callee_st') avars) (List.map (sel t_callee_st') avars) /\
           sel s_callee_st' retvar = sel t_callee_st' retvar /\
           no_adt_leak input avars retvar s_callee_st').
  Proof.
    induction 1; simpl; intros s_env Henv; (split; [destruct s; unfold_all; simpl in *; try solve [intros; try discriminate]; intros Hcomp Hsyn s_st Hsf Heqv | try solve [intros; try discriminate]]).
    {
      (* skip *)
      exists s_st; split.
      - eapply RunsToSkip; eauto.
      - eauto.
    }
    {
      (* seq *)
      inject Hcomp.
      inversion Hsf; subst.
      destruct H4 as [Hsf1 Hsf2].
      rename H into Hrt1.
      rename H0 into Hrt2.
      eapply is_syntax_ok_seq_elim in Hsyn.
      destruct Hsyn as [Hsyn1 Hsyn2].
      edestruct IHRunsTo1 as [IHRunsTo1' ?]; eauto.
      edestruct IHRunsTo1' as [s_st' [Hsst' Heq']]; eauto.
      edestruct IHRunsTo2 as [IHRunsTo2' ?]; eauto.
      edestruct IHRunsTo2' as [s_st'' [Hsst'' Heq'']]; eauto.
      exists s_st''; split.
      - eapply RunsToSeq; eauto.
      - eauto.
    }
    {
      (* dfacade - call *)
      inject Hcomp.
      rename s into x.
      rename g into lbl.
      rename l into args.
      rename H into Hrtlbl.
      rename H0 into Hrtcall.
      inversion Hrtlbl; subst.
      rename H1 into Hlw.
      rename H2 into Hnadt.
      rename H5 into Hst'.
      copy_as Hst' Hst'2.
      eapply equiv_intro in Hst'; eauto.
      assert (Heqv' : st' === s_st).
      {
        etransitivity; eauto; symmetry; eauto.
      }
      eapply is_syntax_ok_call_elim in Hsyn.
      destruct Hsyn as [Hsynx Hsynargs].
      inversion Hrtcall; unfold_all; subst.
      {
        (* axiomatic *)
        rename H3 into Hfw.
        rename H4 into Hspec.
        rename H5 into Hmm.
        rename H6 into Hnadt2.
        rename H7 into Hpre.
        rename H8 into Hlen.
        rename H11 into Hpost.
        rename H12 into Hst''.
        simpl in *.
        rewrite Hst'2 in Hfw.
        rewrite add_eq_o in Hfw by eauto.
        inject Hfw.
        inversion Hsf; subst.
        {
          rename H3 into Hflbl.
          rename H4 into Hmm'.
          rename H6 into Hxnadt.
          rename H7 into Hpre'.
          copy_as Hflbl Hflbl'; eapply Henv in Hflbl.
          destruct Hflbl as [f_w' [Hfw' Hspec']]; simpl in *.
          unif f_w'.
          unif (Facade.Axiomatic spec0).
          rewrite (mapM_find_equiv st' s_st) in Hmm by eauto.
          unif input0.
          exists (add x ret (add_remove_many args input (wrap_output output) s_st)).
          split.
          {
            eapply RunsToCallAx; eauto.
          }
          {
            rewrite Hst''.
            eapply add_equiv; eauto.
            copy_as Hmm Hmm'; eapply mapM_length in Hmm'.
            eapply add_remove_many_equiv; eauto.
            - symmetry; eauto.
            - eapply output_eqv_refl.
              unfold wrap_output.
              rewrite map_length.
              congruence.
          }
        }
        {
          rename H3 into Hflbl.
          copy_as Hflbl Hflbl'; eapply Henv in Hflbl.
          destruct Hflbl as [f_w' [Hfw' Hspec']]; simpl in *.
          unif f_w'.
          rewrite Hspec' in Hspec; discriminate.
        }
      }
      {
        (* operational *)
        rename H3 into Hfw.
        rename H4 into Hspec.
        rename H5 into Hlen.
        rename H6 into Hmm.
        rename H7 into Hnadt2.
        rename H8 into Hrtb.
        rename H9 into Hret.
        rename H12 into Hnleak.
        rename H13 into Hst''.
        simpl in *.
        rewrite Hst'2 in Hfw.
        rewrite add_eq_o in Hfw by eauto.
        inject Hfw.
        inversion Hsf; unfold_all; subst.
        {
          rename H3 into Hflbl.
          copy_as Hflbl Hflbl'; eapply Henv in Hflbl.
          destruct Hflbl as [f_w' [Hfw' Hspec']]; simpl in *.
          unif f_w'.
          rewrite Hspec' in Hspec; discriminate.
        }
        {
          rename H3 into Hflbl.
          rename H4 into Hlen'.
          rename H5 into Hmm'.
          rename H6 into Hnadt'.
          rename H8 into Hsfb.
          rename H9 into Hbodyok.
          copy_as Hflbl Hflbl'; eapply Henv in Hflbl.
          destruct Hflbl as [f_w' [Hfw' Hspec']]; simpl in *.
          unif f_w'.
          unif (@Facade.Operational ADTValue spec).
          destruct spec0; simpl in *.
          copy_as Hmm Hmm'2.
          rewrite (mapM_find_equiv st' s_st) in Hmm by eauto.
          unif input0.
          edestruct IHRunsTo2 as [trash IHRunsTo2']; eauto.
          edestruct IHRunsTo2' as [s_callee_st' Hscst']; eauto; simpl in *.
          {
            simpl in *.
            rewrite Hst'2.
            rewrite add_eq_o by eauto.
            eauto.
          }          
          destruct Hscst' as [Hrtbs [Hmcst [Hcstr Hnadts]]].
          exists (add x ret (add_remove_many args input (List.map (sel s_callee_st') ArgVars) s_st)).
          split.
          {
            eapply RunsToCallOp; eauto.
            simpl.
            congruence.
          }
          {
            rewrite Hst''.
            eapply add_equiv; eauto.
            eapply add_remove_many_equiv; eauto.
            - symmetry; eauto.
            - eapply mapM_length; eauto.
          }
        }
      }
    }
    {
      (* if-true *)
      inject Hcomp.
      eapply is_syntax_ok_if_elim in Hsyn.
      destruct Hsyn as [Hsyne [Hsyn1 Hsyn2]].
      inversion Hsf; subst; rename H5 into He; rename H6 into Hsfbr.
      - edestruct IHRunsTo as [IHRunsTo' ?]; eauto.
        edestruct IHRunsTo' as [s_st' [Hsst' Heq']]; eauto.
        exists s_st'; split.
        + eapply RunsToIfTrue; eauto.
        + eauto.
      - eapply is_false_equiv in He; eauto.
        exfalso; eapply is_true_is_false; eauto.
    }
    {
      (* if-false *)
      inject Hcomp.
      eapply is_syntax_ok_if_elim in Hsyn.
      destruct Hsyn as [Hsyne [Hsyn1 Hsyn2]].
      inversion Hsf; subst; rename H5 into He; rename H6 into Hsfbr.
      - eapply is_true_equiv in He; eauto.
        exfalso; eapply is_true_is_false; eauto.
      - edestruct IHRunsTo as [IHRunsTo' ?]; eauto.
        edestruct IHRunsTo' as [s_st' [Hsst' Heq']]; eauto.
        exists s_st'; split.
        + eapply RunsToIfFalse; eauto.
        + eauto.
    }
    {
      (* while-true *)
      inject Hcomp.
      copy_as Hsyn Hsyn'.
      eapply is_syntax_ok_while_elim in Hsyn.
      destruct Hsyn as [Hsyne Hsynb].
      inversion Hsf; unfold_all; subst.
      - edestruct IHRunsTo1 as [IHRunsTo1' ?]; eauto.
        edestruct IHRunsTo1' as [s_st' [Hsst' Heq']]; eauto.
        edestruct IHRunsTo2 as [IHRunsTo2' ?]; eauto.
        edestruct (IHRunsTo2' (While e s)) as [s_st'' [Hsst'' Heq'']]; try eapply Heq'; eauto.
        exists s_st''; split.
        + eapply RunsToWhileTrue; eauto.
        + eauto.
      - rename H5 into He.
        eapply is_false_equiv in He; eauto.
        exfalso; eapply is_true_is_false; eauto.
    }
    {
      (* while-false *)
      inject Hcomp.
      eapply is_syntax_ok_while_elim in Hsyn.
      destruct Hsyn as [Hsyne Hsynb].
      inversion Hsf; unfold_all; subst.
      - rename H2 into He.
        eapply is_true_equiv in He; eauto.
        exfalso; eapply is_true_is_false; eauto.
      - exists s_st; split.
        + eapply RunsToWhileFalse; eauto.
        + eauto.
    }
    {
      (* assign *)
      inject Hcomp.
      rename s into x.
      rename H into He.
      rename H0 into Hnadt.
      rename H1 into Hst'.
      eapply is_syntax_ok_assign_elim in Hsyn.
      destruct Hsyn as [Hsynx Hsyne].
      erewrite <- eval_equiv in He by eauto.
      erewrite <- not_mapsto_adt_equiv in Hnadt by eauto.
      exists (add x (SCA w) s_st); split.
      - eapply RunsToAssign; eauto.
      - rewrite Hst'.
        eapply add_equiv; eauto.
    }
    {
      (* facade call - axiomatic *)
      unfold_all.
      intros x' f' args' f_w' spec' input' t_callee_st' ret' Heq Hfw Hspec Hmm Hsfb Hrtb Hret Hnadt Hst''2.
      inject Heq.
      unif (@SCA ADTValue f_w').
      rename H1 into Hspec'.
      rewrite Hspec' in Hspec.
      discriminate.
    }
    {
      (* facade call - operation *)
      unfold_all.
      intros x' f' args' f_w' spec' input' t_callee_st' ret' Heq Hfw Hspec Hmm Hsfb Hrtb Hret' Hnadt Hst''2.
      inject Heq.
      unif (@SCA ADTValue f_w').
      rename H1 into Hspec'.
      rewrite Hspec in Hspec'.
      rename H6 into Hret.
      inject Hspec'.
      unif input'.
      destruct spec'; simpl in *.
      edestruct IHRunsTo as [IHRunsTo' trash]; eauto.
      edestruct IHRunsTo' as [s_callee_st' [Hstb Hscst']]; eauto.
      {
        eapply equiv_refl.
        eapply args_name_ok_make_map; eauto.
      }
      rename H8 into Hst''.
      rewrite Hst'' in Hst''2.
      eapply add_add_remove_many_eq_elim in Hst''2; eauto; try (rewrite map_length; eauto).
      destruct Hst''2 as [Hreteq Houteq].
      exists s_callee_st'.
      repeat try_split; eauto.
      {
        rewrite (map_find_equiv s_callee_st' callee_st') by eauto.
        eauto.
      }
      {
        unfold sel in *. 
        rewrite (find_equiv s_callee_st' callee_st') by eauto.
        rewrite Hret.
        rewrite Hret'.
        rewrite Hreteq.
        eauto.
      }
      {
        Arguments no_adt_leak_equiv st1 st2 [_] _ _ _ _ _ _ _.
        eapply (no_adt_leak_equiv _ callee_st'); eauto.
      }
    }
  Qed.

  Theorem compile_runsto t t_env t_st t_st' :
    FRunsTo t_env t t_st t_st' -> 
    forall s_env, 
      fenv_impls_env t_env s_env -> 
      (forall s, 
         t = compile s -> 
         is_syntax_ok s = true -> 
         forall s_st,
           Safe s_env s s_st -> 
           s_st === t_st ->
           exists s_st',
             RunsTo s_env s s_st s_st' /\
             s_st' === t_st').
  Proof.
    intros; eapply compile_runsto'; eauto.
  Qed.

  Lemma not_free_vars_no_change env s st st' x : RunsTo env s st st' -> ~ StringSet.In x (free_vars s) -> find x st' = find x st.
    admit.
  Qed.

End ADTValue.