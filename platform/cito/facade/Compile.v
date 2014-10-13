Set Implicit Arguments.

Require Import Memory IL.
Require Import Facade.
Require Syntax.
Require Import String.
Open Scope string.
Require Import SyntaxExpr.
Require Import StringMap.
Import StringMap.
Require Import GLabel.
Require Import StringMapFacts.
Import FMapNotations.
Open Scope fmap.

Coercion Var : string >-> Expr.

Fixpoint compile (s : Stmt) : Syntax.Stmt :=
  match s with
    | Skip => Syntax.Skip
    | Seq a b => Syntax.Seq (compile a) (compile b)
    | If e t f => Syntax.If e (compile t) (compile f)
    | While e c => Syntax.While e (compile c)
    | Assign x e => Syntax.Assign x e
    | Label x lbl => Syntax.Label x lbl
    | Call x f args => Syntax.Call (Some x) f (List.map Var args)
  end.

Require Import ADT.

Module Make (Import A : ADT).

  Require Semantics.
  Module Cito := Semantics.Make A.

  Definition RunsTo := @RunsTo ADTValue.
  Definition State := @State ADTValue.
  Definition Env := @Env ADTValue.
  Definition AxiomaticSpec := @AxiomaticSpec ADTValue.
  Definition Value := @Value ADTValue.
  Definition Sca := @SCA ADTValue.
  Definition Adt := @ADT ADTValue.

  Definition represent p (o : option ADTValue) v :=
    match v with
      | SCA w => p = w
      | ADT a => o = Some a
    end.

  Require Import WordMap.

  Definition related (s_st : State) (t_st : Cito.State) := 
    (forall x v, 
       find x s_st = Some v -> let p := Locals.sel (fst t_st) x in represent p (WordMap.find p (snd t_st)) v) /\
    (forall p a,
       WordMap.find p (snd t_st) = Some a ->
       exists! x,
         Locals.sel (fst t_st)  x = p /\
         find x s_st = Some (ADT a)).
                
  Definition CitoEnv := ((glabel -> option W) * (W -> option Cito.Callee))%type.

  Coercion Semantics.Fun : Semantics.InternalFuncSpec >-> FuncCore.FuncCore.

  Definition CitoIn_FacadeIn (argin : Cito.ArgIn) : Value :=
    match argin with
      | inl w => SCA _ w
      | inr a => ADT a
    end.

  Definition CitoInOut_FacadeInOut (in_out : Cito.ArgIn * Cito.ArgOut) : Value * option ADTValue := (CitoIn_FacadeIn (fst in_out), snd in_out).

  Definition compile_ax (spec : AxiomaticSpec) :=
    {|
      Semantics.PreCond args := PreCond spec (List.map CitoIn_FacadeIn args) ;
      Semantics.PostCond pairs ret := PostCond spec (List.map CitoInOut_FacadeInOut pairs) (CitoIn_FacadeIn ret)
    |}.

  Require Import ListFacts1 ListFacts2 ListFacts3 ListFactsNew.

  Definition compile_op (spec : OperationalSpec) :=
    {|
      Semantics.Fun :=
        {|
          FuncCore.ArgVars := ArgVars spec;
          FuncCore.RetVar := RetVar spec;
          FuncCore.Body := compile (Body spec)
        |};
      Semantics.NoDupArgVars := NoDup_bool_string_eq_sound _ (args_no_dup spec)
    |}.

  Definition FuncSpec := @FuncSpec ADTValue.

  Definition compile_spec (spec : FuncSpec) : Cito.Callee :=
    match spec with
      | Axiomatic s => Semantics.Foreign (compile_ax s)
      | Operational s => Cito.Internal (compile_op s)
    end.

  Definition compile_env (env : Env) : CitoEnv :=
    (Label2Word env, 
     fun w => option_map compile_spec (Word2Spec env w)).
    
  Require Import GeneralTactics.
  Require Import GeneralTactics3.

  Ltac inject h := injection h; intros; subst; clear h.

  Notation ceval := SemanticsExpr.eval.
  Notation cRunsTo := Semantics.RunsTo.
  Lemma is_true_is_false : forall (st : State) e, is_true st e -> is_false st e -> False.
  Proof.
    intros.
    unfold is_true, is_false in *.
    rewrite H in *; discriminate.
  Qed.
  Lemma safe_if_true : forall (env : Env) e t f st, Safe env (If e t f) st -> is_true st e -> Safe env t st.
  Proof.
    intros.
    inversion H; subst.
    eauto.
    exfalso; eapply is_true_is_false; eauto.
  Qed.
  Definition is_bool (st : State) e := eval_bool st e <> None.
  Definition value_dec (v : Value) : {w | v = SCA _ w} + {a | v = ADT a}.
    destruct v.
    left; exists w; eauto.
    right; exists a; eauto.
  Defined.
  Definition option_value_dec (v : option Value) : {w | v = Some (SCA _ w)} + {a | v = Some (ADT a)} + {v = None}.
    destruct (option_dec v).
    destruct s; subst.
    destruct (value_dec  x).
    destruct s; subst.
    left; left; eexists; eauto.
    destruct s; subst.
    left; right; eexists; eauto.
    subst.
    right; eauto.
  Qed.
  Lemma eval_ceval : forall s_st vs h e w, eval s_st e = Some (SCA _ w) -> related s_st (vs, h) -> ceval vs e = w.
  Proof.
    induction e; simpl; intuition.
    unfold related in *.
    openhyp.
    eapply H0 in H.
    eauto.

    unfold eval_binop_m in *.
    destruct (option_value_dec (eval s_st e1)).
    destruct s.
    destruct s.
    rewrite e in *.
    destruct (option_value_dec (eval s_st e2)).
    destruct s.
    destruct s.
    rewrite e0 in *.
    inject H.
    erewrite IHe1; [ | eauto .. ].
    erewrite IHe2; [ | eauto .. ].
    eauto.
    destruct s.
    rewrite e0 in *; discriminate.
    rewrite e0 in *; discriminate.
    destruct s.
    rewrite e in *; discriminate.
    rewrite e in *; discriminate.
    
    unfold eval_binop_m in *.
    destruct (option_value_dec (eval s_st e1)).
    destruct s.
    destruct s.
    rewrite e in *.
    destruct (option_value_dec (eval s_st e2)).
    destruct s.
    destruct s.
    rewrite e0 in *.
    inject H.
    erewrite IHe1; [ | eauto .. ].
    erewrite IHe2; [ | eauto .. ].
    eauto.
    destruct s.
    rewrite e0 in *; discriminate.
    rewrite e0 in *; discriminate.
    destruct s.
    rewrite e in *; discriminate.
    rewrite e in *; discriminate.
  Qed.
  Lemma eval_bool_wneb : forall (s_st : State) vs h e b, eval_bool s_st e = Some b -> related s_st (vs, h) -> wneb (ceval vs e) $0 = b.
  Proof.
    intros.
    unfold eval_bool in *.
    destruct (option_value_dec (eval s_st e)).
    destruct s.
    destruct s.
    rewrite e0 in *.
    inject H.
    eapply eval_ceval in e0; [ | eauto].
    rewrite e0 in *; eauto.
    destruct s.
    rewrite e0 in *; discriminate.
    rewrite e0 in *; discriminate.
  Qed.
  Notation boolcase := Sumbool.sumbool_of_bool.
  Lemma wneb_is_true : forall s_st vs h e, wneb (ceval vs e) $0 = true -> related s_st (vs, h) -> is_bool s_st e -> is_true s_st e.
  Proof.
    intros.
    unfold is_true.
    unfold is_bool in *.
    eapply ex_up in H1.
    openhyp.
    destruct (boolcase x); subst.
    eauto.
    eapply eval_bool_wneb in H1; eauto.
    set (ceval _ _) in *.
    rewrite H in *; discriminate.
  Qed.
  Lemma is_true_is_bool : forall st e, is_true st e -> is_bool st e.
  Proof.
    intros.
    unfold is_true, is_bool in *.
    rewrite H in *.
    discriminate.
  Qed.
  Lemma is_false_is_bool : forall st e, is_false st e -> is_bool st e.
  Proof.
    intros.
    unfold is_false, is_bool in *.
    rewrite H in *.
    discriminate.
  Qed.
  Lemma safe_if_is_bool : forall (env : Env) e t f st, Safe env (If e t f) st -> is_bool st e.
  Proof.
    intros.
    inversion H; subst.
    eapply is_true_is_bool; eauto.
    eapply is_false_is_bool; eauto.
  Qed.
  Lemma safe_if_false : forall (env : Env) e t f st, Safe env (If e t f) st -> is_false st e -> Safe env f st.
  Proof.
    intros.
    inversion H; subst.
    exfalso; eapply is_true_is_false; eauto.
    eauto.
  Qed.
  Lemma wneb_is_false : forall s_st vs h e, wneb (ceval vs e) $0 = false -> related s_st (vs, h) -> is_bool s_st e -> is_false s_st e.
  Proof.
    intros.
    unfold is_false.
    unfold is_bool in *.
    eapply ex_up in H1.
    openhyp.
    destruct (boolcase x); subst.
    eapply eval_bool_wneb in H1; eauto.
    set (ceval _ _) in *.
    rewrite H in *; discriminate.
    eauto.
  Qed.

  (* test boolean deciders *)
  Open Scope string_scope.
  Require Import List.
  Import ListNotations.
  Goal is_no_dup ["aa"; "ab"; "cc"] = true. Proof. exact eq_refl. Qed.
  Goal is_no_dup ["aa"; "aa"; "cc"] = false. Proof. exact eq_refl. Qed.
  Goal is_in "bb" ["aa"; "bb"; "cc"] = true. Proof. exact eq_refl. Qed.
  Goal is_in "dd" ["aa"; "bb"; "cc"] = false. Proof. exact eq_refl. Qed.
  Goal is_disjoint ["aa"; "bb"; "cc"] ["dd"; "ee"] = true. Proof. exact eq_refl. Qed.
  Goal is_disjoint ["aa"; "bb"; "cc"] ["dd"; "ee"; "cc"] = false. Proof. exact eq_refl. Qed.
  Goal assigned (Seq (Assign "x" (Var "a")) (Label "y" ("a", "b"))) = ["x"; "y"]. Proof. exact eq_refl. Qed.
  Goal is_disjoint (assigned (Seq (Assign "x" (Var "a")) (Label "y" ("a", "b")))) ["aa"; "bb"] = true. Proof. exact eq_refl. Qed.
  Goal is_disjoint (assigned (Seq (Assign "x" (Var "a")) (Label "y" ("a", "b")))) ["aa"; "bb"; "x"] = false. Proof. exact eq_refl. Qed.
  
  Require Import StringSet.

  Require Import WordMapFacts.
  Import FMapNotations.
  Open Scope fmap.
  Require Import WordMap.
  Import WordMap.

  Require Import GeneralTactics2.
  Hint Extern 0 (_ == _) => reflexivity.

  Ltac copy h := generalize h; intro.

  Ltac copy_as h h' := generalize h; intro h'.

  (* unify and get rid of b *)
  Ltac unif b :=
    match goal with
      | H1 : ?L = Some _, H2 : ?L = Some b |- _ => rewrite H1 in H2; symmetry in H2; inject H2
    end.

  Ltac subst' H := rewrite H in *; clear H.

  Ltac openhyp' := 
    repeat match goal with
             | H : _ /\ _ |- _  => destruct H
             | H : _ \/ _ |- _ => destruct H
             | H : exists x, _ |- _ => destruct H
             | H : exists ! x, _ |- _ => destruct H
             | H : unique _ _ |- _ => destruct H
           end.

  Lemma find_Some_in : forall elt k m (v : elt), find k m = Some v -> In k m.
    intros; eapply MapsTo_In; eapply find_mapsto_iff; eauto.
  Qed.

  Lemma find_Some_in' : forall elt k m (v : elt), StringMap.find k m = Some v -> StringMap.In k m.
    intros; eapply StringMapFacts.MapsTo_In; eapply StringMapFacts.find_mapsto_iff; eauto.
  Qed.

  Lemma in_find_Some elt k m : In k m -> exists v : elt, find k m = Some v.
    intros H.
    eapply In_MapsTo in H.
    destruct H as [v H].
    eapply find_mapsto_iff in H.
    eauto.
  Qed.

  Lemma in_find_Some' elt k m : StringMap.In k m -> exists v : elt, StringMap.find k m = Some v.
    intros H.
    eapply StringMapFacts.In_MapsTo in H.
    destruct H as [v H].
    eapply StringMapFacts.find_mapsto_iff in H.
    eauto.
  Qed.

  Lemma diff_disjoint elt m1 m2 : @Disjoint elt (m1 - m2) m2.
  Proof.
    unfold Disjoint.
    intros k.
    nintro.
    openhyp.
    eapply diff_in_iff in H.
    openhyp; intuition.
  Qed.

  Lemma Disjoint_in_not elt h1 h2 x : @Disjoint elt h1 h2 -> In x h1 -> ~ In x h2.
  Proof.
    intros Hdisj Hin1 Hin2.
    eapply Hdisj; eauto.
  Qed.

  Lemma diff_find_Some_iff : forall elt k (v : elt) m m', find k (m - m') = Some v <-> find k m = Some v /\ ~ In k m'.
    split; intros.
    eapply find_mapsto_iff in H.
    eapply diff_mapsto_iff in H; openhyp.
    eapply find_mapsto_iff in H.
    eauto.
    openhyp.
    eapply find_mapsto_iff.
    eapply diff_mapsto_iff.
    eapply find_mapsto_iff in H.
    eauto.
  Qed.

  Lemma diff_swap_find elt k (v : elt) h h1 h2 : find k (h - h1 - h2) = Some v -> find k (h - h2 - h1) = Some v.
  Proof.
    intros Hf.
    eapply diff_find_Some_iff in Hf.
    destruct Hf as [Hf Hni2].
    eapply diff_find_Some_iff in Hf.
    destruct Hf as [Hf Hni1].
    eapply diff_find_Some_iff.
    split.
    eapply diff_find_Some_iff.
    eauto.
    eauto.
  Qed.

  Lemma diff_swap elt (h h1 h2 : t elt) : h - h1 - h2 == h - h2 - h1.
  Proof.
    unfold Equal.
    intros k.
    eapply option_univalence.
    intros v; split; intros Hf; eapply diff_swap_find; eauto.
  Qed.

  Definition Submap {elt} m1 m2 := forall {k v}, @find elt k m1 = Some v -> find k m2 = Some v.
  Infix "<=" := Submap.

  Require Import Setoid.

  Global Add Parametric Morphism elt : (@Submap elt)
      with signature Equal ==> Equal ==> iff as Submap_m.
  Proof.
    intros x y Hxy x' y' Hx'y'.
    unfold Submap.
    split; intros H.
    intros k v Hf.
    rewrite <- Hx'y' in *.
    rewrite <- Hxy in *.
    eauto.
    intros k v Hf.
    rewrite Hx'y' in *.
    rewrite Hxy in *.
    eauto.
  Qed.

  Lemma submap_trans elt (a b c : t elt) : a <= b -> b <= c -> a <= c.
  Proof.
    intros Hab Hbc; unfold Submap; intros k v Hf; eapply Hbc; eauto.
  Qed.

  Lemma submap_find : forall elt k (v : elt) m1 m2, m1 <= m2 -> find k m1 = Some v -> find k m2 = Some v.
    unfold Submap; eauto.
  Qed.

  Lemma submap_in elt h1 h2 : h1 <= h2 -> forall k, @In elt k h1 -> In k h2.
  Proof.
    intros Hsm k Hi.
    eapply in_find_Some in Hi.
    destruct Hi as [v Hf].
    eapply find_Some_in; eauto.
  Qed.

  Lemma diff_submap elt (m1 m2 : t elt) : m1 - m2 <= m1.
  Proof.
    unfold Submap.
    intros k v Hf.
    eapply diff_find_Some_iff in Hf; openhyp; eauto.
  Qed.

  Lemma submap_not_in : forall elt h1 h2, h1 <= h2 -> forall k, ~ @In elt k h2 -> ~ In k h1.
    intros; not_not; eapply submap_in; eauto.
  Qed.
  Lemma submap_diff elt (a b c : t elt) : c <= b -> b <= a -> a - b <= a - c.
  Proof.
    intros Hcb Hba.
    unfold Submap.
    intros k v Hf.
    eapply diff_find_Some_iff in Hf.
    destruct Hf as [Hf Hni].
    eapply diff_find_Some_iff.
    split.
    solve [eauto].
    solve [eapply submap_not_in; eauto].
  Qed.

  Lemma submap_restrict elt (h1 h2 h : t elt) : h1 <= h2 -> h1 - h <= h2 - h.
  Proof.
    unfold Submap; intros Hsml k v Hf.
    eapply diff_find_Some_iff in Hf; openhyp; rewrite diff_o; eauto.
  Qed.

  Lemma submap_diff_diff elt (h1 h2 h3 : t elt) : h1 <= h2 -> h2 <= h3 -> h2 - h1 == (h3 - h1) - (h3 - h2).
  Proof.
    intros H12 H23.
    unfold Equal.
    intros k.
    eapply option_univalence.
    intros v; split; intros Hf.
    eapply diff_find_Some_iff in Hf.
    destruct Hf as [Hf Hni].
    eapply diff_find_Some_iff.
    split.
    eapply diff_find_Some_iff.
    split.
    eapply submap_find; eauto.
    eauto.
    not_not.
    eapply diff_in_iff in H.
    destruct H as [Hi3 Hni2].
    eapply find_Some_in in Hf; contradiction.
    eapply diff_find_Some_iff in Hf.
    destruct Hf as [Hf Hni].
    eapply diff_find_Some_iff in Hf.
    destruct Hf as [Hf Hni1].
    eapply diff_find_Some_iff.
    split.
    destruct (option_dec (find k h2)) as [[v' Hs] | Hn].
    copy Hs; eapply H23 in Hs; unif v'; eauto.
    eapply not_find_in_iff in Hn.
    contradict Hni.
    eapply diff_in_iff.
    split.
    eapply find_Some_in; eauto.
    eauto.
    eauto.
  Qed.

  Lemma submap_case elt h2 h12 : h2 <= h12 -> forall k (v : elt), find k h12 = Some v <-> find k (h12 - h2) = Some v \/ find k h2 = Some v.
  Proof.
    intros Hsm k v; split.
    intros Hf12.
    destruct (In_dec h2 k) as [Hin | Hni].
    right.
    eapply in_find_Some in Hin.
    destruct Hin as [v' Hf2].
    copy_as Hf2 Hf2'; eapply Hsm in Hf2'.
    unif v'.
    eauto.
    left.
    eapply diff_find_Some_iff; eauto.

    intros [Hfd | Hf2].
    eapply diff_find_Some_iff in Hfd; eauto.
    destruct Hfd as [Hf12 Hni].
    eauto.
    eapply Hsm; eauto.
  Qed.

  Lemma submap_disjoint_1 elt (h1 h2 h1' : t elt) : Disjoint h1 h2 -> h1' <= h1 -> Disjoint h1' h2.
  Proof.
    intros Hdisj Hsm.
    unfold Disjoint.
    intros k [Hin1 Hin2].
    eapply submap_in in Hin1; eauto.
    eapply Hdisj; eauto.
  Qed.
  Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.

  Lemma diff_submap_cancel elt (h1 h12 : t elt) : h1 <= h12 -> h12 - (h12 - h1) == h1.
  Proof.
    intros Hsm.
    unfold Equal.
    intros k.
    eapply option_univalence.
    intros v; split; intros Hf.
    eapply diff_find_Some_iff in Hf.
    destruct Hf as [Hf12 Hni].
    eapply submap_case in Hf12; eauto.
    openhyp.
    contradict Hni; eapply find_Some_in; eauto.
    eauto.
    eapply diff_find_Some_iff.
    split.
    eapply Hsm; eauto.
    intros Hin.
    eapply diff_in_iff in Hin.
    destruct Hin as [? Hni].
    contradict Hni; eapply find_Some_in; eauto.
  Qed.

  Definition direct_sum elt (h1 h2 h12 : t elt) := (h1 + h2 == h12 /\ Disjoint h1 h2).

  Notation "h1 * h2 === h12" := (direct_sum h1 h2 h12) (at level 100).

  Global Add Parametric Morphism elt : (@direct_sum elt)
      with signature Equal ==> Equal ==> Equal ==> iff as direct_sum_m.
  Proof.
    intros.
    unfold direct_sum.
    rewrite H.
    rewrite H0.
    rewrite H1.
    intuition.
  Qed.

  Lemma direct_sum_disjoint elt h1 h2 h12 : direct_sum h1 h2 h12 -> @Disjoint elt h1 h2.
  Proof.
    intros H; destruct H; eauto.
  Qed.

  Lemma direct_sum_in_not elt h1 h2 h12 x : @direct_sum elt h1 h2 h12 -> In x h1 -> ~ In x h2.
  Proof.
    intros; eapply Disjoint_in_not; eauto.
    eapply direct_sum_disjoint; eauto.
  Qed.
  Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

  Lemma disjoint_update_iff elt h1 h2 : Disjoint h1 h2 -> forall k (v : elt), find k (h1 + h2) = Some v <-> find k h1 = Some v \/ find k h2 = Some v.
  Proof.
    intros Hdisj k v.
    split; intros Hf12.
    eapply find_mapsto_iff in Hf12.
    eapply update_mapsto_iff in Hf12.
    destruct Hf12 as [Hf2 | [Hf1 Hni2]].
    eapply find_mapsto_iff in Hf2.
    eauto.
    eapply find_mapsto_iff in Hf1.
    eauto.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff.
    destruct Hf12 as [Hf1 | Hf2].
    right.
    split.
    eapply find_mapsto_iff; eauto.
    eapply Disjoint_in_not; eauto.
    eapply find_Some_in; eauto.
    left.
    eapply find_mapsto_iff; eauto.
  Qed.

  Lemma direct_sum_intro elt h1 h2 h12 : @Disjoint elt h1 h2 -> (forall k v, find k h12 = Some v <-> find k h1 = Some v \/ find k h2 = Some v) -> direct_sum h1 h2 h12.
  Proof.
    intros Hdisj Hiff.
    unfold direct_sum.
    split.
    unfold Equal.
    intros k.
    eapply option_univalence.
    intros v.
    etransitivity.
    2 : symmetry; eauto.
    eapply disjoint_update_iff; eauto.
    eauto.
  Qed.

  Lemma find_Some_direct_sum elt h1 h2 h12 : direct_sum h1 h2 h12 -> forall k (v : elt), find k h12 = Some v <-> find k h1 = Some v \/ find k h2 = Some v.
  Proof.
    intros Hds k v.
    destruct Hds as [Hheq Hdisj].
    rewrite <- Hheq.
    eapply disjoint_update_iff; eauto.
  Qed.

  Lemma diff_direct_sum elt (h2 h12 : t elt) : h2 <= h12 -> direct_sum (h12 - h2) h2 h12.
  Proof.
    intros Hsm.
    eapply direct_sum_intro.
    eapply diff_disjoint.
    eapply submap_case; eauto.
  Qed.

  Lemma direct_sum_submap elt (h1 h2 h12 : t elt) : direct_sum h1 h2 h12 -> h1 <= h12 /\ h2 <= h12.
    intros Hds.
    specialize (find_Some_direct_sum Hds).
    intros Hiff.
    unfold Submap.
    split; intros k v Hf; eapply Hiff; eauto.
  Qed.

  Arguments direct_sum_submap [_] _ _ _ _.

  Lemma direct_sum_sym elt (h1 h2 h12 : t elt) : direct_sum h1 h2 h12 -> direct_sum h2 h1 h12.
  Proof.
    intros Hds.
    specialize (find_Some_direct_sum Hds).
    intros Hiff.
    eapply direct_sum_intro.
    eapply Disjoint_sym; eapply direct_sum_disjoint; eauto.
    intros k v.
    etransitivity.
    eauto.
    intuition.
  Qed.

  Lemma direct_sum_submap_submap elt (h1 h12 h123 h2 : t elt) : h1 <= h12 -> h12 <= h123 -> h2 == h12 - h1 -> direct_sum h2 (h123 - h12) (h123 - h1).
  Proof.
    intros Hsm1 Hsm12 Heq2.
    eapply direct_sum_intro.
    rewrite Heq2.
    eapply submap_disjoint_1; eauto.
    2 : solve [eapply diff_submap; eauto].
    eapply Disjoint_sym; eapply diff_disjoint; eauto.
    intros k v; split.
    intros Hfd.
    eapply diff_find_Some_iff in Hfd; eauto.
    destruct Hfd as [Hf123 Hni1].
    eapply submap_case in Hf123; eauto.
    destruct Hf123 as [Hfd | Hf12].
    eauto.
    left.
    rewrite Heq2.
    eapply submap_case in Hf12; eauto.
    destruct Hf12 as [Hfd | Hf1].
    eauto.
    contradict Hni1; eapply find_Some_in; eauto.
    
    intros Hor.
    eapply diff_find_Some_iff.
    rewrite Heq2 in Hor.
    destruct Hor as [Hf2 | Hfd].
    eapply diff_find_Some_iff in Hf2.
    openhyp.
    split.
    eapply Hsm12; eauto.
    eauto.
    eapply diff_find_Some_iff in Hfd.
    openhyp.
    split.
    eauto.
    not_not.
    eapply submap_in; eauto.
  Qed.

  Lemma combine_length_eq A B (ls1 : list A) : forall (ls2 : list B), length ls1 = length ls2 -> length (combine ls1 ls2) = length ls1.
  Proof.
    induction ls1; destruct ls2; simpl in *; intros; intuition.
  Qed.

  Lemma nth_error_combine A B ls1 : forall ls2 i (a : A) (b : B), nth_error ls1 i = Some a -> nth_error ls2 i = Some b -> nth_error (combine ls1 ls2) i = Some (a, b).
  Proof.
    induction ls1; destruct ls2; destruct i; simpl in *; intros; try discriminate.
    inject H; inject H0; eauto.
    eauto.
  Qed.

  Lemma nth_error_combine_elim A B ls1 : forall ls2 i (a : A) (b : B), nth_error (combine ls1 ls2) i = Some (a, b) -> nth_error ls1 i = Some a /\ nth_error ls2 i = Some b.
  Proof.
    induction ls1; destruct ls2; destruct i; simpl in *; intros; try discriminate.
    inject H; eauto.
    eauto.
  Qed.

  Lemma nth_error_map_elim : forall A B (f : A -> B) ls i b, nth_error (List.map f ls) i = Some b -> exists a, nth_error ls i = Some a /\ f a = b.
    intros.
    rewrite ListFacts.map_nth_error_full in H.
    destruct (option_dec (nth_error ls i)).
    destruct s; rewrite e in *; inject H; eexists; eauto.
    rewrite e in *; discriminate.
  Qed.

  Lemma map_nth_error_1 : forall A B (f : A -> B) ls1 ls2 i a, List.map f ls1 = ls2 -> nth_error ls1 i = Some a -> nth_error ls2 i = Some (f a).
    intros.
    rewrite <- H.
    erewrite map_nth_error; eauto.
  Qed.

  Lemma map_nth_error_2 A B (f : A -> B) ls1 : forall ls2 i b, List.map f ls1 = ls2 -> nth_error ls2 i = Some b -> exists a, nth_error ls1 i = Some a /\ f a = b.
  Proof.
    induction ls1; destruct ls2; destruct i; simpl in *; intros; try discriminate.
    inject H; inject H0; eexists; eauto.
    inject H; eauto.
  Qed.

  Lemma map_eq_nth_error_1 : forall A1 A2 B (f1 : A1 -> B) (f2 : A2 -> B) ls1 ls2 i a1, List.map f1 ls1 = List.map f2 ls2 -> nth_error ls1 i = Some a1 -> exists a2, nth_error ls2 i = Some a2 /\ f1 a1 = f2 a2.
    intros.
    eapply map_nth_error_1 in H; eauto.
    eapply nth_error_map_elim in H; openhyp.
    eexists; eauto.
  Qed.

  Lemma in_nth_error A ls : forall (a : A), List.In a ls -> exists i, nth_error ls i = Some a.
  Proof.
    induction ls; simpl in *; intros.
    intuition.
    openhyp.
    subst.
    exists 0; eauto.
    eapply IHls in H; eauto.
    openhyp.
    exists (S x); eauto.
  Qed.

  Lemma nth_error_nil A i : nth_error (@nil A) i = None.
  Proof.
    destruct i; simpl in *; eauto.
  Qed.

  Lemma mapM_length A B (f : A -> option B) ls1 : forall ls2, mapM f ls1 = Some ls2 -> length ls1 = length ls2.
  Proof.
    induction ls1; destruct ls2; simpl in *; intros; try discriminate.
    eauto.
    destruct (option_dec (f a)) as [[y Hy] | Hnone].
    rewrite Hy in *.
    destruct (option_dec (mapM f ls1)) as [[ys Hys] | Hnone].
    rewrite Hys in *.
    discriminate.
    rewrite Hnone in *; discriminate.
    rewrite Hnone in *; discriminate.

    f_equal.
    destruct (option_dec (f a)) as [[y Hy] | Hnone].
    rewrite Hy in *.
    destruct (option_dec (mapM f ls1)) as [[ys Hys] | Hnone].
    rewrite Hys in *.
    inject H; eauto.
    rewrite Hnone in *; discriminate.
    rewrite Hnone in *; discriminate.
  Qed.

  Lemma mapM_nth_error_1 A B (f : A -> option B) ls1 : forall ls2 i a, mapM f ls1 = Some ls2 -> nth_error ls1 i = Some a -> exists b, nth_error ls2 i = Some b /\ f a = Some b.
  Proof.
    induction ls1; destruct ls2; destruct i; simpl in *; intros; try discriminate.
    destruct (option_dec (f a)) as [[y Hy] | Hnone].
    rewrite Hy in *.
    destruct (option_dec (mapM f ls1)) as [[ys Hys] | Hnone].
    rewrite Hys in *.
    discriminate.
    rewrite Hnone in *; discriminate.
    rewrite Hnone in *; discriminate.
    destruct (option_dec (f a)) as [[y Hy] | Hnone].
    rewrite Hy in *.
    destruct (option_dec (mapM f ls1)) as [[ys Hys] | Hnone].
    rewrite Hys in *.
    discriminate.
    rewrite Hnone in *; discriminate.
    rewrite Hnone in *; discriminate.
    destruct (option_dec (f a)) as [[y Hy] | Hnone].
    rewrite Hy in *.
    destruct (option_dec (mapM f ls1)) as [[ys Hys] | Hnone].
    rewrite Hys in *.
    inject H; inject H0; eexists; eauto.
    rewrite Hnone in *; discriminate.
    rewrite Hnone in *; discriminate.
    destruct (option_dec (f a)) as [[y Hy] | Hnone].
    rewrite Hy in *.
    destruct (option_dec (mapM f ls1)) as [[ys Hys] | Hnone].
    rewrite Hys in *.
    inject H; eauto.
    rewrite Hnone in *; discriminate.
    rewrite Hnone in *; discriminate.
  Qed.

  Lemma length_eq_nth_error A B ls1 : forall ls2 i (a : A), nth_error ls1 i = Some a -> length ls1 = length ls2 -> exists b : B, nth_error ls2 i = Some b.
  Proof.
    induction ls1; destruct ls2; destruct i; simpl in *; intros; try discriminate.
    inject H; inject H0; eexists; eauto.
    inject H0; eauto.
  Qed.

  Lemma mapM_nth_error_2 A B (f : A -> option B) ls1 ls2 i a2 : mapM f ls1 = Some ls2 -> nth_error ls2 i = Some a2 -> exists a1, nth_error ls1 i = Some a1 /\ f a1 = Some a2.
  Proof.
    intros Hmm Ha2.
    copy_as Ha2 Ha2'; eapply length_eq_nth_error in Ha2'.
    2 : symmetry; eapply mapM_length; eauto.
    destruct Ha2' as [a1 Ha1].
    eapply mapM_nth_error_1 in Hmm; eauto.
    destruct Hmm as [a2' [Ha2' Hf]].
    unif a2'.
    rewrite <- Hf in *.
    eexists; eauto.
  Qed.

  Lemma cons_incl_elim A (a : A) ls1 ls2 : incl (a :: ls1) ls2 -> List.In a ls2 /\ incl ls1 ls2.
  Proof.
    unfold incl.
    intros Hincl.
    split.
    eapply Hincl.
    eapply in_eq.
    intros a' Hin.
    eapply Hincl.
    eapply in_cons; eauto.
  Qed.

  Lemma incl_nth_error A ls1 : forall i ls2 (a : A), List.incl ls1 ls2 -> nth_error ls1 i = Some a -> exists i', nth_error ls2 i' = Some a.
  Proof.
    induction ls1; destruct i; simpl in *; intros; try discriminate.
    inject H0.
    eapply cons_incl_elim in H.
    openhyp.
    eapply in_nth_error; eauto.
    eapply IHls1; eauto.
    eapply cons_incl_elim in H.
    openhyp.
    eauto.
  Qed.

  Lemma combine_map A B C (f1 : A -> B) (f2 : A -> C) ls : combine (List.map f1 ls) (List.map f2 ls) = List.map (fun x => (f1 x, f2 x)) ls.
  Proof.
    induction ls; simpl in *; intros; try f_equal; eauto.
  Qed.

  Lemma NoDup_nth_error A ls : NoDup ls -> forall i i' (x : A), nth_error ls i = Some x -> nth_error ls i' = Some x -> i = i'.
  Proof.
    induction 1; destruct i; destruct i'; simpl in *; intros; try discriminate.
    eauto.
    inject H1.
    contradict H; eapply Locals.nth_error_In; eauto.
    inject H2.
    contradict H; eapply Locals.nth_error_In; eauto.
    f_equal; eauto.
  Qed.

  Import StringSetFacts.
  Import StringSet.

  Lemma set_disjoint_list_disjoint ls1 ls2 : Disjoint (of_list ls1) (of_list ls2) -> ListFacts1.Disjoint ls1 ls2.
    unfold ListFacts1.Disjoint, Disjoint.
    intros Hdisj e [Hin1 Hin2].
    eapply Hdisj; split; eapply StringSetFacts.of_list_1; eapply SetoidListFacts.In_InA; eauto.
  Qed.

  Lemma is_disjoint_sound ls1 ls2 : is_disjoint ls1 ls2 = true -> ListFacts1.Disjoint ls1 ls2.
  Proof.
    intros Hdisj.
    eapply inter_is_empty_iff in Hdisj.
    eapply set_disjoint_list_disjoint; eauto.
  Qed.

  Import WordMapFacts.
  Import WordMap.

  Ltac unfold_related H := copy H; unfold related in H; simpl in H; openhyp.

  Lemma related_no_alias : forall vs h st x1 a1 x2 a2, related st (vs, h) -> StringMap.find x1 st = Some (ADT a1) -> StringMap.find x2 st = Some (ADT a2) -> vs x1 = vs x2 -> x1 = x2.
  Proof.
    intros.
    unfold_related H.
    copy H0; eapply H in H0; simpl in *.
    copy H1; eapply H in H1; simpl in *.
    unfold Locals.sel in *.
    rewrite H2 in *.
    rewrite H0 in H1; inject H1.
    eapply H4 in H0; openhyp'.
    assert (x = x1) by (eapply H1; eauto).
    assert (x = x2) by (eapply H1; eauto).
    eauto.
  Qed.
  Arguments related_no_alias [_ _] _ _ _ _ _ _ _ _ _.

  Definition not_reachable key (k : key) ks ins := forall i, nth_error ks i = Some k -> exists w, nth_error ins i = Some (Sca w).

  Lemma find_Some_add_remove_many ks : 
    forall ins outs h k v, 
      NoDup ks -> 
      length ks = length ins -> 
      length ks = length outs -> 
      (StringMap.find k (add_remove_many ks ins outs h) = Some v <-> 
       ((not_reachable k ks ins /\ StringMap.find k h = Some v) \/ 
        exists i a, 
          nth_error ks i = Some k /\ 
          nth_error ins i = Some (ADT a) /\ 
          nth_error outs i = Some (Some v))).
  Proof.
    induction ks; destruct ins; destruct outs; simpl in *; try solve [intros; discriminate].
    intros h k v Hnd Hlkin Hlkout.
    split.
    intros Hf.
    left.
    split.
    Lemma no_reachable_nil key (k : key) : not_reachable k [] [].
    Proof.
      unfold not_reachable; intros; rewrite nth_error_nil in *; discriminate.
    Qed.
    eapply no_reachable_nil.
    eauto.
    intros H.
    openhyp.
    eauto.
    rewrite nth_error_nil in *; discriminate.    

    Lemma not_reachable_cons_sca key (k : key) ks ins k' w : not_reachable k' ks ins -> not_reachable k' (k :: ks) (SCA ADTValue w :: ins).
    Proof.
      unfold not_reachable; intros Hnr.
      intros i Hk'.
      destruct i as [|i]; simpl in *.
      inject Hk'.
      exists w; eauto.
      eapply Hnr in Hk'.
      eauto.
    Qed.

    Lemma not_reachable_cons_neq key (k : key) ks ins k' v : not_reachable k' ks ins -> k' <> k -> not_reachable k' (k :: ks) (v :: ins).
    Proof.
      unfold not_reachable; intros Hnr Hne.
      intros i Hk'.
      destruct i as [|i]; simpl in *.
      inject Hk'.
      intuition.
      eapply Hnr in Hk'.
      eauto.
    Qed.

    rename a into k.
    intros h k' v' Hnd Hlkin Hlkout.
    inject Hlkin.
    inject Hlkout.
    inversion Hnd; subst.
    split.
    intros Hf.
    destruct v as [w | a].
    eapply IHks in Hf; eauto.
    destruct Hf as [[Hnr Hfk'] | [i [a [Hk' [Hin Hout]]]]].
    left.
    split.
    solve [eapply not_reachable_cons_sca; eauto].
    eauto.
    right.
    solve [exists (S i), a; eauto].

    destruct o as [ao |].
    eapply IHks in Hf; eauto.
    destruct Hf as [[Hnr Hfk'] | [i [a' [Hk' [Hin Hout]]]]].
    destruct (string_dec k' k) as [Heq | Hne].
    subst.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    inject Hfk'.
    right.
    solve [exists 0, a; eauto].
    rewrite StringMapFacts.add_neq_o in * by eauto.
    left.
    split.
    solve [eapply not_reachable_cons_neq; eauto].
    eauto.
    right.
    solve [exists (S i), a'; eauto].

    eapply IHks in Hf; eauto.
    destruct Hf as [[Hnr Hfk'] | [i [a' [Hk' [Hin Hout]]]]].
    destruct (string_dec k' k) as [Heq | Hne].
    subst.
    rewrite StringMapFacts.remove_eq_o in * by eauto.
    discriminate.
    rewrite StringMapFacts.remove_neq_o in * by eauto.
    left.
    split.
    solve [eapply not_reachable_cons_neq; eauto].
    eauto.
    right.
    solve [exists (S i), a'; eauto].

    Lemma not_reachable_cons_elim key (k : key) ks v vs k' : not_reachable k' (k :: ks) (v :: vs) -> not_reachable k' ks vs.
    Proof.
      unfold not_reachable; intros Hnr.
      intros i Hk'.
      specialize (Hnr (S i)); simpl in *.
      eauto.
    Qed.
    Lemma not_not_reachable key (k : key) ks a ins : ~ not_reachable k (k :: ks) (ADT a :: ins).
    Proof.
      unfold not_reachable.
      nintro.
      specialize (H 0); simpl in *.
      edestruct H; eauto.
      discriminate.
    Qed.

    intros Hor.
    destruct Hor as [[Hnr Hfk'] | [i [a [Hk' [Hin Hout]]]]].
    destruct v as [w | a].
    eapply IHks; eauto.
    left.
    split.
    solve [eapply not_reachable_cons_elim; eauto].
    eauto.
    destruct o as [ao|].
    eapply IHks; eauto.
    destruct (string_dec k' k) as [Heq | Hne].
    subst.
    solve [contradict Hnr; eapply not_not_reachable].
    rewrite StringMapFacts.add_neq_o in * by eauto.
    left.
    split.
    solve [eapply not_reachable_cons_elim; eauto].
    eauto.
    eapply IHks; eauto.
    destruct (string_dec k' k) as [Heq | Hne].
    subst.
    solve [contradict Hnr; eapply not_not_reachable].
    rewrite StringMapFacts.remove_neq_o in * by eauto.
    left.
    split.
    solve [eapply not_reachable_cons_elim; eauto].
    eauto.

    eapply IHks; eauto.
    destruct i as [|i]; simpl in *.
    inject Hk'.
    inject Hin.
    inject Hout.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    left.
    split.
    Lemma not_in_not_reachable key (k : key) ks ins : ~ List.In k ks -> not_reachable k ks ins.
    Proof.
      unfold not_reachable; intros Hni.
      intros i Hk.
      contradict Hni.
      eapply Locals.nth_error_In; eauto.
    Qed.
    solve [eapply not_in_not_reachable; eauto].
    eauto.
    solve [right; exists i, a; eauto].
  Qed.

  Lemma find_ADT_add_remove_many k ks (ins : list Value) outs st a :
    NoDup ks -> 
    mapM (sel st) ks = Some ins ->
    length ks = length outs ->
    StringMap.find k (add_remove_many ks ins outs st) = Some (ADT a)->
    exists a', StringMap.find k st = Some (ADT a').
  Proof.
    intros Hnd Hmm Hl Hf.
    eapply find_Some_add_remove_many in Hf; eauto.
    2 : eapply mapM_length; eauto.
    openhyp.
    eexists; eauto.
    eapply mapM_nth_error_2 in Hmm; eauto; openhyp.
    unif x1.
    eexists; eauto.
  Qed.

  Lemma is_in_iff a ls : is_in a ls = true <-> List.In a ls.
  Proof.
    unfold is_in; split; intros H; destruct (in_dec string_dec a ls); eauto; discriminate.
  Qed.
  Lemma iff_false_iff b P : (b = true <-> P) -> (b = false <-> ~ P).
  Proof.
    split; intros; destruct b; intuition.
  Qed.
  Lemma iff_not_true_iff b P : (b = true <-> P) -> (b <> true <-> ~ P).
  Proof.
    split; intros; destruct b; intuition.
  Qed.
  Lemma iff_negb_iff b P : (b = true <-> P) -> (negb b = true <-> ~ P).
  Proof.
    split; intros; destruct b; intuition.
  Qed.
  Lemma iff_negb_not_true_iff b P : (b = true <-> P) -> (negb b <> true <-> P).
  Proof.
    split; intros; destruct b; intuition.
  Qed.
  Lemma not_is_in_iff a ls : is_in a ls = false <-> ~ List.In a ls.
  Proof.
    eapply iff_false_iff; eapply is_in_iff.
  Qed.
  Lemma negb_is_in_iff a ls : negb (is_in a ls) = true <-> ~ List.In a ls.
  Proof.
    eapply iff_negb_iff; eapply is_in_iff.
  Qed.

  Lemma is_some_p_iff A p (o : option A) : is_some_p p o = true <-> match o with | Some a => p a = true | None => False end.
  Proof.
    destruct o as [a|]; simpl in *; intuition.
  Qed.

  Lemma is_adt_iff v : is_adt v = true <-> exists a : ADTValue, v = ADT a.
  Proof.
    destruct v as [w | a]; simpl in *.
    split; intros; openhyp; discriminate.
    intuition.
    eexists; eauto.
  Qed.

  Lemma is_mapsto_adt_iff x st : is_mapsto_adt x st = true <-> exists a : ADTValue, StringMap.find x st = Some (ADT a).
  Proof.
    unfold is_mapsto_adt.
    etransitivity.
    eapply is_some_p_iff.
    destruct (option_dec (StringMap.find x st)) as [[v Heq] | Hne].
    rewrite Heq in *.
    etransitivity.
    eapply is_adt_iff.
    split; intros Hex.
    openhyp; subst; eexists; eauto.
    destruct Hex as [a Ha]; inject Ha; eexists; eauto.

    rewrite Hne.
    split; intros.
    intuition.
    openhyp; discriminate.
  Qed.
  Lemma is_mapsto_adt_false_iff x st : is_mapsto_adt x st = false <-> ~ exists a : ADTValue, StringMap.find x st = Some (ADT a).
  Proof.
    eapply iff_false_iff; eapply is_mapsto_adt_iff.
  Qed.
  Lemma not_mapsto_adt_iff x st : not_mapsto_adt x st = true <-> ~ exists a : ADTValue, StringMap.find x st = Some (ADT a).
  Proof.
    eapply iff_negb_iff; eapply is_mapsto_adt_iff.
  Qed.
  Lemma not_mapsto_adt_not_true_iff x st : not_mapsto_adt x st <> true <-> exists a : ADTValue, StringMap.find x st = Some (ADT a).
  Proof.
    eapply iff_negb_not_true_iff; eapply is_mapsto_adt_iff.
  Qed.

(*

  s_st ------- s_env, s --------> exists s_st'
 (Safe)
   ||             |                  ||          
   ||          compile               ||
   ||             |                  ||
   ||             v                  ||

  t_st ------ t_env, t -------->    t_st' 

*)

  Theorem compile_runsto : 
    forall t t_env t_st t_st', 
      Cito.RunsTo t_env t t_st t_st' -> 
      forall s, 
        t = compile s -> 
        (* h1 : the heap portion that this program is allowed to change *)
        forall h1, 
          h1 <= snd t_st -> 
          forall s_st, 
            related s_st (fst t_st, h1) -> 
            forall s_env, 
              t_env = compile_env s_env -> 
              Safe s_env s s_st -> 
              exists s_st', 
                RunsTo s_env s s_st s_st' /\ 
                (* h2 : the frame heap (the outside portion that won't be touched by this program *)
                let h2 := snd t_st - h1 in 
                (* the frame heap will be intacked in the final state *)
                h2 <= snd t_st' /\ 
                (* variables not appearing as LHS won't change value in Cito state *)
                (forall x, ~ List.In x (assigned s) -> Locals.sel (fst t_st) x = Locals.sel (fst t_st') x) /\
                (* newly allocated ADT objects during this program's execution won't collide with the frame heap *)
                (forall x, is_mapsto_adt x s_st = false \/ is_mapsto_adt x s_st = true /\ Locals.sel (fst t_st) x <> Locals.sel (fst t_st') x -> is_mapsto_adt x s_st' = true -> ~ In (Locals.sel (fst t_st') x) h2) /\
                (* main result: final source-level and target level states are related *)
                related s_st' (fst t_st', snd t_st' - h2).
  Proof.
    induction 1; simpl; intros; destruct s; simpl in *; intros; try discriminate.

    Focus 7.
    (* call-operational *)
    unfold_all.
    inject H2.
    destruct (option_dec (Word2Spec s_env (SemanticsExpr.eval (fst v) e))); simpl in *.
    2 : rewrite e0 in *; simpl in *; discriminate.
    destruct s0.
    rewrite e0 in *; simpl in *.
    inject H.
    destruct x; simpl in *.
    destruct a; simpl in *; unfold compile_ax in *; simpl in *; discriminate.
    unfold compile_op in *; simpl in *.
    inject H2; simpl in *.
    inversion H6; subst.
    replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
    rewrite e0 in *.
    discriminate.
    
    unfold_all.
    replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
    rewrite e0 in *.
    inject H9.

    edestruct IHRunsTo; [ .. | clear IHRunsTo].
    eauto.
    2 : eauto.
    3 : eauto.
    3 : eauto.
    3 : eauto.
    Focus 3.
    openhyp.
    copy H; eapply H15 in H.
    openhyp.
    eapply ex_up in H.
    openhyp.
    eexists.
    split.
    eapply RunsToCallOp.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    reflexivity.
    Unfocus.

    Lemma find_Some_make_map_iff elt ks : 
      forall vs k (v : elt),
        NoDup ks ->
        length ks  = length vs ->
        (StringMap.find k (make_map ks vs) = Some v <->
         exists i,
           nth_error ks i = Some k /\
           nth_error vs i = Some v).
    Proof.
      induction ks; destruct vs; simpl in *; intros k v Hnd Hl; (split; [intros Hf | intros Hex]); try discriminate.
      destruct Hex as [i [Hk Hi]]; rewrite nth_error_nil in *; discriminate.
      rename a into k'.
      inject Hl.
      inversion Hnd; subst.
      destruct (string_dec k k') as [Heq | Hne].
      subst.
      rewrite StringMapFacts.add_eq_o in * by eauto.
      inject Hf.
      exists 0; eauto.
      rewrite StringMapFacts.add_neq_o in * by eauto.
      eapply IHks in Hf; eauto.
      destruct Hf as [i [Hk Hv]].
      solve [exists (S i); eauto].
      rename a into k'.
      inject Hl.
      inversion Hnd; subst.
      destruct Hex as [i [Hk Hv]].
      destruct i as [ | i]; simpl in *.
      inject Hk.
      inject Hv.
      rewrite StringMapFacts.add_eq_o in * by eauto.
      solve [eauto].
      destruct (string_dec k k') as [Heq | Hne].
      subst.
      contradict H2.
      solve [eapply Locals.nth_error_In; eauto].
      rewrite StringMapFacts.add_neq_o in * by eauto.
      eapply IHks; eauto.
    Qed.      
    Lemma make_map_in elt ks : forall (vs : list elt) k, StringMap.In k (make_map ks vs) -> List.In k ks.
    Proof.
      induction ks; destruct vs; simpl; intros k' Hi.
      eapply StringMapFacts.empty_in_iff in Hi; contradiction.
      eapply StringMapFacts.empty_in_iff in Hi; contradiction.
      eapply StringMapFacts.empty_in_iff in Hi; contradiction.
      rename a into k.
      eapply StringMapFacts.add_in_iff in Hi.
      destruct Hi as [He | Hi].
      subst; eauto.
      right; eauto.
    Qed.
    Lemma make_map_not_in elt k ks (vs : list elt) : ~ List.In k ks -> ~ StringMap.In k (make_map ks vs).
    Proof.
      intros; not_not.
      rename H0 into H.
      eapply make_map_in; eauto.
    Qed.

    Fixpoint make_mapM {elt} keys values :=
      match keys, values with
        | k :: keys', v :: values' => 
          match v with
            | Some a => add k a (make_mapM keys' values')
            | None => make_mapM keys' values'
          end
        | _, _ => @empty elt
      end.

    Definition no_dupM elt ks vs := forall i j (k : key) (ai aj : elt), nth_error ks i = Some k -> nth_error vs i = Some (Some ai) -> nth_error ks j = Some k -> nth_error vs j = Some (Some aj) -> i = j.

    Lemma no_dupM_cons_elim elt ks vs k (v : option elt) : no_dupM (k :: ks) (v :: vs) -> no_dupM ks vs.
    Proof.
      unfold no_dupM.
      intros Hnd i j k' ai aj Hik Hiv Hjk Hjv.
      assert (S i = S j).
      eapply Hnd; eauto; simpl; eauto.
      inject H; eauto.
    Qed.

    Lemma find_Some_make_mapM_iff elt ks : forall vs k (a : elt), length ks = length vs -> no_dupM ks vs -> (find k (make_mapM ks vs) = Some a <-> exists i, nth_error ks i = Some k /\ nth_error vs i = Some (Some a)).
    Proof.
      induction ks; try (rename a into k'); destruct vs as [ | v' vs]; simpl; intros k a Hl Hnd; (split; [intros Hi | intros Hex]); try discriminate.
      destruct Hex as [i [Hk Hv]]; rewrite nth_error_nil in *; discriminate.

      inject Hl.
      destruct v' as [a' | ].
      destruct (Word.weq k k') as [Heq | Hne].
      subst.
      rewrite add_eq_o in * by eauto.
      inject Hi.
      solve [exists 0; eauto].
      rewrite add_neq_o in * by eauto.
      eapply IHks in Hi; eauto.
      solve [destruct Hi as [i [Hk Hv]]; exists (S i); eauto].
      solve [eapply no_dupM_cons_elim; eauto].
      eapply IHks in Hi; eauto.
      solve [destruct Hi as [i [Hk Hv]]; exists (S i); eauto].
      solve [eapply no_dupM_cons_elim; eauto].

      inject Hl.
      destruct Hex as [i [Hk Hv]].
      destruct i as [ | i]; simpl in *.
      inject Hk.
      inject Hv.
      rewrite add_eq_o in * by eauto.
      solve [eauto].
      destruct v' as [a' |].
      destruct (Word.weq k k') as [Heq | Hne].
      subst.
      assert (0 = S i).
      eapply Hnd; eauto; simpl; eauto.
      discriminate.
      rewrite add_neq_o in * by eauto.
      eapply IHks; eauto.
      solve [eapply no_dupM_cons_elim; eauto].
      eapply IHks; eauto.
      solve [eapply no_dupM_cons_elim; eauto].
    Qed.

    Lemma in_make_mapM_iff elt ks : forall vs k, length ks = length vs -> (In k (make_mapM ks vs) <-> exists i (a : elt), nth_error ks i = Some k /\ nth_error vs i = Some (Some a)).
    Proof.
      induction ks; try (rename a into k'); destruct vs as [|v' vs]; simpl; intros k Hl; (split; [intros Hi | intros Hex]); try discriminate.
      eapply empty_in_iff in Hi; contradiction.
      destruct Hex as [i [a [Hk Hv]]]; rewrite nth_error_nil in *; discriminate.

      inject Hl.
      destruct v' as [a' | ].
      eapply add_in_iff in Hi.
      destruct Hi as [Heq | Hi].
      subst.
      solve [exists 0, a'; eauto].
      solve [eapply IHks in Hi; eauto; destruct Hi as [i [a [Hk Hv]]]; exists (S i), a; eauto].
      solve [eapply IHks in Hi; eauto; destruct Hi as [i [a [Hk Hv]]]; exists (S i), a; eauto].

      inject Hl.
      destruct Hex as [i [a [Hk Hv]]].
      destruct i as [ | i]; simpl in *.
      inject Hk.
      inject Hv.
      eapply add_in_iff; eauto.
      destruct v' as [a' |].
      eapply add_in_iff.
      right.
      eapply IHks; eauto.
      eapply IHks; eauto.
    Qed.

    Definition only_adt := List.map (fun x : Value => match x with | ADT a => Some a | _ => None end).

    Definition reachable_heap (vs : Locals.vals) argvars (input : list Value) := make_mapM (List.map (fun x => vs x) argvars) (only_adt input).

    Lemma in_reachable_heap_iff vs ks : forall ins p, length ks = length ins -> (In p (reachable_heap vs ks ins) <-> exists i k a, nth_error ks i = Some k /\ nth_error ins i = Some (ADT a) /\ vs k = p).
    Proof.
      unfold reachable_heap, only_adt; intros ins p Hl.
      split.
      intros Hi.
      eapply in_make_mapM_iff in Hi.
      destruct Hi as [i [a [Hk Hv]]].
      eapply nth_error_map_elim in Hk.
      destruct Hk as [k [Hk Hvs]].
      subst.
      eapply nth_error_map_elim in Hv.
      destruct Hv as [v [Hv Ha]].
      destruct v as [w | a'].
      discriminate.
      inject Ha.
      solve [exists i, k, a; eauto].
      solve [repeat rewrite map_length; eauto].

      intros Hex.
      destruct Hex as [i [k [a [Hk [Hv Hvs]]]]].
      subst.
      eapply in_make_mapM_iff.
      solve [repeat rewrite map_length; eauto].
      exists i, a.
      split.
      solve [erewrite map_nth_error; eauto].
      solve [erewrite map_nth_error; eauto; simpl; eauto].
    Qed.

    Definition no_aliasM (vs : Locals.vals) ks ins := no_dupM (List.map (fun x => vs x) ks) (only_adt ins).

    Lemma find_Some_reachable_heap_iff vs ks : forall ins p a, length ks = length ins -> no_aliasM vs ks ins -> (find p (reachable_heap vs ks ins) = Some a <-> exists i k, nth_error ks i = Some k /\ nth_error ins i = Some (ADT a) /\ vs k = p).
    Proof.
      unfold reachable_heap, only_adt; intros ins p a Hl Hna.
      split.
      intros Hi.
      eapply find_Some_make_mapM_iff in Hi; eauto.
      destruct Hi as [i [Hk Hv]].
      eapply nth_error_map_elim in Hk.
      destruct Hk as [k [Hk Hvs]].
      subst.
      eapply nth_error_map_elim in Hv.
      destruct Hv as [v [Hv Ha]].
      destruct v as [w | a'].
      discriminate.
      inject Ha.
      solve [exists i, k; eauto].
      solve [repeat rewrite map_length; eauto].

      intros Hex.
      destruct Hex as [i [k [Hk [Hv Hvs]]]].
      subst.
      eapply find_Some_make_mapM_iff; eauto.
      solve [repeat rewrite map_length; eauto].
      exists i.
      split.
      solve [erewrite map_nth_error; eauto].
      solve [erewrite map_nth_error; eauto; simpl; eauto].
    Qed.

    Lemma related_no_aliasM st args input vs h :
      mapM (sel st) args = Some input -> 
      related st (vs, h) -> 
      NoDup args ->
      no_aliasM vs args input.
    Proof.
      intros Hmm Hr Hnd.
      unfold no_aliasM, no_dupM, only_adt.
      intros i j p ai aj Hki Hvi Hkj Hvj.
      eapply nth_error_map_elim in Hki.
      destruct Hki as [ki [Hki Hvs]].
      subst.
      eapply nth_error_map_elim in Hvi.
      destruct Hvi as [vi [Hvi Hai]].
      destruct vi as [wi | ai'].
      discriminate.
      inject Hai.
      copy_as Hmm Hmm'; eapply mapM_nth_error_1 in Hmm'; eauto.
      destruct Hmm' as [v' [? Hfki]].
      unfold Value in *.
      unif v'.
      eapply nth_error_map_elim in Hkj.
      destruct Hkj as [kj [Hkj Hvs]].
      eapply nth_error_map_elim in Hvj.
      destruct Hvj as [vj [Hvj Haj]].
      destruct vj as [wj | aj'].
      discriminate.
      inject Haj.
      copy_as Hmm Hmm'; eapply mapM_nth_error_1 in Hmm'; eauto.
      destruct Hmm' as [v' [? Hfkj]].
      unif v'.
      assert (ki = kj).
      eapply related_no_alias; eauto.
      subst.
      eapply NoDup_nth_error; eauto.
    Qed.

    Ltac split' name :=
      match goal with
        | |- ?T /\ _ => assert (name: T); [ | split; [ auto | ] ]
      end.

    Lemma change_var_names vs1 vs2 h vars1 vars2 input : 
      related (make_map vars1 input) (vs1, h) -> 
      List.map (fun x => vs2 x) vars2 = List.map (fun x => vs1 x) vars1 -> 
      NoDup vars1 ->
      NoDup vars2 ->
      length vars1 = length input ->
      related (make_map vars2 input) (vs2, h).
    Proof.
      intros Hr Hm Hnd1 Hnd2 Hl.
      copy_as Hr Hr'.
      destruct Hr' as [Hr1 Hr2]; unfold related; simpl in *.
      unfold Locals.sel in *.
      split.

      intros x2 v Hf.
      eapply find_Some_make_map_iff in Hf; eauto.
      destruct Hf as [i [Hx2 Hv]].
      eapply map_eq_nth_error_1 in Hm; eauto.
      destruct Hm as [x1 [Hx1 Hvs]].
      subst' Hvs.
      eapply Hr1.
      solve [eapply find_Some_make_map_iff; eauto].
      rewrite <- Hl; solve [eapply map_eq_length_eq; eauto].

      intros p a Hfp.
      eapply Hr2 in Hfp.
      destruct Hfp as [x1 [[Hp Hfx1] Hu]].
      subst.
      eapply find_Some_make_map_iff in Hfx1; eauto.
      destruct Hfx1 as [i [Hx1 Hi]].
      copy_as Hm Hm'; symmetry in Hm'; eapply map_eq_nth_error_1 in Hm'; eauto.
      destruct Hm' as [x2 [Hx2 Hvs]].
      subst' Hvs.
      exists x2.
      split.
      split.
      eauto.
      eapply find_Some_make_map_iff; eauto.
      rewrite <- Hl; solve [eapply map_eq_length_eq; eauto].
      intros x2' [Hvs Hfx2'].
      eapply find_Some_make_map_iff in Hfx2'; eauto.
      destruct Hfx2' as [i' [Hx'2 Hi']].
      assert (Heqi : i = i').
      eapply map_eq_nth_error_1 in Hm; eauto.
      destruct Hm as [x1' [Hx1' Hvs']].
      subst' Hvs'.
      assert (Hex1 : x1 = x1').
      eapply Hu.
      split.
      eauto.
      eapply find_Some_make_map_iff; eauto.
      subst.
      solve [eapply (NoDup_nth_error Hnd1); eauto].
      subst.
      unif x2'.
      eauto.
      rewrite <- Hl; solve [eapply map_eq_length_eq; eauto].
    Qed.

    Lemma reachable_submap_related st args input vs h : 
      mapM (sel st) args = Some input -> 
      related st (vs, h) -> 
      NoDup args ->
      reachable_heap vs args input <= h /\ 
      related (make_map args input) (vs, reachable_heap vs args input).
    Proof.
      intros Hmm Hr Hdn.
      split.
      unfold Submap.
      intros p a Hf.
      eapply find_Some_reachable_heap_iff in Hf.
      destruct Hf as [i [k [Hk [Hin Hvs]]]].
      subst.
      eapply mapM_nth_error_1 in Hmm; eauto.
      destruct Hmm as [v [Hin' Hfk]].
      unfold Value in *.
      unif v.
      eapply Hr in Hfk; simpl in *.
      solve [eauto].
      solve [eapply mapM_length; eauto].
      solve [eapply related_no_aliasM; eauto].
        
      split; simpl.
      intros k v Hfk.
      eapply find_Some_make_map_iff in Hfk; eauto.
      destruct Hfk as [i [Hk Hin]].
      copy_as Hmm Hmm'; eapply mapM_nth_error_1 in Hmm'; eauto.
      destruct Hmm' as [v' [? Hfk]].
      unif v'.
      eapply Hr in Hfk; simpl in *.
      destruct v as [w | a]; simpl in *.
      eauto.
      eapply find_Some_reachable_heap_iff; eauto.
      solve [eapply mapM_length; eauto].
      solve [eapply related_no_aliasM; eauto].
      solve [eapply mapM_length; eauto].

      intros p a Hfp.
      eapply find_Some_reachable_heap_iff in Hfp; eauto.
      destruct Hfp as [i [k [Hk [Hin Hvs]]]].
      subst.
      copy_as Hmm Hmm'; eapply mapM_nth_error_1 in Hmm'; eauto.
      destruct Hmm' as [v' [? Hfk]].
      unfold Value in *.
      unif v'.
      exists k.
      split.
      split.
      eauto.
      eapply find_Some_make_map_iff; eauto.
      solve [eapply mapM_length; eauto].
      intros k' [Hvs Hfk'].
      eapply find_Some_make_map_iff in Hfk'; eauto.
      destruct Hfk' as [i' [Hk' Hin']].
      copy_as Hmm Hmm'; eapply mapM_nth_error_1 in Hmm'; eauto.
      destruct Hmm' as [v' [? Hfk']].
      unif v'.
      solve [eapply related_no_alias; eauto].
      solve [eapply mapM_length; eauto].
      solve [eapply mapM_length; eauto].
      solve [eapply related_no_aliasM; eauto].
    Qed.

    instantiate (1 := reachable_heap (fst v) l input).
    eapply reachable_submap_related in H4; openhyp; eauto.
    eapply submap_trans; eauto.
    eapply reachable_submap_related in H4; openhyp; eauto.
    Lemma is_no_dup_sound ls : is_no_dup ls = true -> NoDup ls.
      intros; eapply NoDup_bool_string_eq_sound; eauto.
    Qed.
    Lemma NoDup_ArgVars : forall spec, NoDup (ArgVars spec).
      intros; destruct spec; simpl; eapply is_no_dup_sound; eauto.
    Qed.
    eapply change_var_names; eauto.
    solve [rewrite map_map in H0; simpl in *; eauto].
    solve [eapply NoDup_ArgVars; eauto].
    solve [eapply mapM_length; eauto].

    split' Hsm.
    eapply submap_trans; eauto.
    eapply submap_diff; eauto.
    eapply reachable_submap_related in H4; openhyp; eauto.

    split.
    intros.
    Lemma singleton_iff_not : forall (e e' : string), ~ List.In e' [e] <-> e <> e'.
      unfold List.In; split; intros; not_not; intuition.
    Qed.
    
    eapply singleton_iff_not in H18.
    rewrite Locals.sel_upd_ne by eauto.
    eauto.

    Import WordMap.

    split.
    intros.
    destruct (string_dec x1 s).
    subst.
    eapply is_mapsto_adt_iff in H19.
    destruct H19 as [a H19].
    rewrite StringMapFacts.add_eq_o in * by eauto.
    inject H19.
    rewrite Locals.sel_upd_eq in * by eauto.
    eapply submap_not_in.
    2 : eapply H9.
    eapply submap_diff; eauto.
    solve [eapply reachable_submap_related in H4; openhyp; eauto].
    Lemma not_in_no_adt k m : ~ StringMap.In k m -> ~ exists a : ADTValue, StringMap.find k m = Some (ADT a).
    Proof.
      intros; not_not; openhyp; eapply find_Some_in'; eauto.
    Qed.
    Import WordMapFacts.
    Lemma NoDup_not_in : forall A (x : A) xs, NoDup (x :: xs) -> ~ List.In x xs.
      inversion 1; subst; eauto.
    Qed.
    Lemma not_incl_spec : forall spec, ~ List.In (RetVar spec) (ArgVars spec).
      intros; destruct spec; simpl; eapply negb_is_in_iff; eauto.
    Qed.

    left.
    eapply is_mapsto_adt_false_iff.
    eapply not_in_no_adt.
    eapply make_map_not_in.
    solve [eapply not_incl_spec].
    eapply is_mapsto_adt_iff.
    solve [eexists; eauto].

    eapply is_mapsto_adt_iff in H19.
    destruct H19 as [a H19].
    rewrite StringMapFacts.add_neq_o in * by eauto.
    rewrite Locals.sel_upd_ne  in * by eauto.
    destruct H18 as [H18 | H18].
    eapply is_mapsto_adt_false_iff in H18.
    nintro; eapply H18; clear H18.
    eapply find_ADT_add_remove_many; eauto.
    solve [rewrite map_length; eapply map_eq_length_eq in H0; eauto].
    solve [intuition].
    
    copy H4; eapply reachable_submap_related in H4; openhyp; eauto.
    destruct v as [vs h]; simpl in *.
    set (h2 := h - h1) in *.
    unfold related; simpl.
    split.

    (* related (1) *)
    rewrite map_map in H0; simpl in *.
    rename x into st_callee'.
    intros x v Hf.

    rename l into args.
    rename s into lhs.
    rename h into h123.
    rename h1 into h12.
    set (h3 := reachable_heap vs args input) in *.
    set (h23 := h123 - h3) in *.

    destruct (string_dec x lhs).
    (* x = lhs *)
    subst.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    rewrite Locals.sel_upd_eq by eauto.
    inject Hf.
    unfold_related H13.
    set (retp := Locals.sel vs_callee' (RetVar spec)) in *.
    eapply H13 in H.
    Lemma submap_represent p h1 h2 v : represent p (WordMap.find p h1) v -> h1 <= h2 -> represent p (WordMap.find p h2) v.
    Proof.
      intros Hpr Hsm.
      destruct v as [w | a]; simpl in *.
      eauto.
      eapply submap_find; eauto.
    Qed.
    eapply submap_represent; eauto.
    solve [eapply submap_diff; eauto; eapply submap_diff; eauto].

    (* x <> lhs *)
    rewrite Locals.sel_upd_ne by eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    eapply find_Some_add_remove_many in Hf.
    openhyp.
    (* not reachable *)
    Lemma not_reachable_iff ks st vs h input k a : related st (vs, h) -> mapM (sel st) ks = Some input -> StringMap.find k st = Some (ADT a) -> (not_reachable k ks input <-> ~ WordMap.In (vs k) (reachable_heap vs ks input)).
    Proof.
      intros Hr Hmm Hf.
      unfold not_reachable.
      split.
      intros Hnr.
      nintro.
      eapply in_reachable_heap_iff in H.
      2 : solve [eapply mapM_length; eauto].
      destruct H as [i [k' [a' [Hk' [Hi Hp]]]]].
      eapply mapM_nth_error_1 in Hmm; eauto.
      destruct Hmm as [v [Hi' Hf']].
      unfold Value in *.
      unif v.
      assert (k = k').
      eapply related_no_alias; eauto.
      subst.
      eapply Hnr in Hk'.
      destruct Hk' as [w Hi'].
      rewrite Hi in Hi'; discriminate.

      intros Hni i Hk.
      contradict Hni.
      eapply in_reachable_heap_iff.
      solve [eapply mapM_length; eauto].
      eapply mapM_nth_error_1 in Hmm; eauto.
      destruct Hmm as [v [Hi' Hf']].
      unfold sel in *.
      unif v.
      exists i, k, a; eauto.
    Qed.
    unfold_related H18.
    copy_as H21 Hf; eapply H18 in H21.
    destruct v as [w | a]; simpl in *.
    eauto.
    erewrite <- diff_o in H21.
    Focus 2.
    eapply not_reachable_iff; eauto.
    eapply submap_find; eauto.
    erewrite submap_diff_diff; eauto.
    eapply submap_restrict.
    solve [eauto].

    (* not reachable *)
    symmetry in H0; eapply map_eq_nth_error_1 in H0; [ | eauto ..].
    openhyp.
    unfold Locals.sel in *.
    rewrite H23.
    assert (Hvse : vs_callee x3 = vs_callee' x3).
    eapply H5.
    Lemma in_args_not_assigned spec x : List.In x (ArgVars spec) -> ~ List.In x (assigned (Body spec)).
    Proof.
      destruct spec; simpl in *; nintro; eapply is_disjoint_sound; eauto.
    Qed.

    eapply in_args_not_assigned; eauto.
    solve [eapply Locals.nth_error_In; eauto].
    subst' Hvse.
    rename x1 into i.
    erewrite map_nth_error in H22 by eauto.
    inject H22.
    unfold_related H13.
    eapply H13 in H24.
    unfold Locals.sel in *.
    set (p := vs_callee' x3) in *.
    eapply submap_represent; eauto.
    eapply submap_diff; eauto.
    solve [eapply submap_diff; eauto].

    solve [eauto].
    solve [eapply mapM_length; eauto].
    solve [rewrite map_length; eapply map_eq_length_eq in H0; eauto].

    (* related (2) *)
    rewrite map_map in H0; simpl in *.
    intros.
    rename s into lhs.
    rename l into args.
    (* set up the heap partitioning :
       h3 : the heap portion passed to the callee, i.e. reachable by arguments referring to ADT objects;
       h2 : the heap portion accessible by the caller, modulo h3;
       h1 : the heap portion not accessible by the caller.
       h1, h2 and h3 are mutually disjoint and cover the whole heap h123.
     *)
    rename h into h123.
    rename h1 into h23.
    rename h2 into h1.
    set (h3 := reachable_heap vs args input) in *.
    set (h12 := h123 - h3) in *.
    set (h2 := h12 - h1) in *.
    set (h3' := heap' - h12) in *.
    set (h23' := heap' - h1) in *.
    assert (direct_sum h1 h2 h12) by (eapply direct_sum_sym; eapply diff_direct_sum; eauto; eapply submap_diff; eauto).

    assert (direct_sum h1 h23 h123) by (eapply diff_direct_sum; eauto).
    assert (direct_sum h12 h3 h123).
    eapply diff_direct_sum; eauto.
    eapply submap_trans.
    eauto.
    solve [eapply (direct_sum_submap h1 h23); eauto].

    assert (Hd13 : Disjoint h1 h3).
    eapply (submap_disjoint_1 h12 h3).
    eapply direct_sum_disjoint; eauto.
    solve [eapply (direct_sum_submap h1 h2); eauto].

    assert (direct_sum h2 h3 h23).
    unfold_all.
    rewrite diff_swap.
    rewrite diff_submap_cancel by (eapply (direct_sum_submap _ h23); eauto).
    solve [eapply diff_direct_sum; eauto].

    assert (direct_sum h2 h3' h23').
    unfold_all.
    rewrite diff_swap.
    rewrite diff_submap_cancel by (eapply (direct_sum_submap _ h23); eauto).
    eapply direct_sum_submap_submap.
    solve [eapply submap_diff; eauto].
    solve [eauto].
    solve [erewrite submap_diff_diff; eauto].

    (* case analysis on which partition p falls into *)
    eapply find_Some_direct_sum in H20; eauto; openhyp.

    (* p is in h2 *)
    unfold_related H18.
    copy_as H20 Hf; eapply submap_find in H20.
    2 : eapply (direct_sum_submap h2 h3); eauto.
    eapply H27 in H20.

    openhyp'.
    rename x1 into x3.
    destruct (string_dec x3 lhs).
    subst; solve [contradict H12; eapply not_mapsto_adt_not_true_iff; eexists; eauto].
    (* x3 <> lhs *)
    exists x3.
    split.
    (* exists *)
    rewrite Locals.sel_upd_ne by eauto.
    rewrite StringMapFacts.add_neq_o by eauto.
    split.
    eauto.
    eapply find_Some_add_remove_many.
    solve [eauto].
    solve [eapply mapM_length; eauto].
    rewrite map_length.
    solve [eapply map_eq_length_eq in H0; eauto].
    left.
    split.
    2 : solve [eauto].
    eapply not_reachable_iff; eauto.
    eapply (direct_sum_in_not h2 h3); eauto.
    solve [subst; eapply find_Some_in; eauto].

    (* unique *)
    intros.
    openhyp.
    destruct (string_dec x' lhs).
    (* x' = lhs *)
    subst.
    rewrite StringMapFacts.add_eq_o in *.
    rewrite Locals.sel_upd_eq in * by eauto.
    inject H31.
    symmetry in H30; subst' H30.
    (* (vs_callee' RetVar) is a newly allocated ADT object, so it shouldn't be in h2 *)
    assert (Hni : ~ In (vs_callee' (RetVar spec)) h12).
    eapply H9.
    left.
    eapply is_mapsto_adt_false_iff.
    eapply not_in_no_adt.
    solve [eapply make_map_not_in; eapply not_incl_spec].
    eapply is_mapsto_adt_iff.
    solve [eexists; eauto].
    contradict Hni.
    eapply submap_in; eauto.
    solve [eapply (direct_sum_submap h1 h2); eauto].
    solve [eapply find_Some_in; eauto].
    solve [eauto].

    (* x' <> lhs *)
    rewrite StringMapFacts.add_neq_o in * by eauto.
    rewrite Locals.sel_upd_ne in * by eauto.
    eapply H28.
    split.
    eauto.
    Lemma not_reachable_add_remove_many k ks ins outs h :
      NoDup ks -> 
      length ks = length ins -> 
      length ks = length outs -> 
      not_reachable k ks ins -> 
      StringMap.find k (add_remove_many ks ins outs h) = StringMap.find k h.
    Proof.
      intros Hnd Hlki Hlko Hnr.
      eapply option_univalence.
      intros v; split; intros Hf.
      eapply find_Some_add_remove_many in Hf; eauto.
      destruct Hf as [[Hnr' Hf] | [i [a [Hk [Hi Ho]]]]].
      eauto.
      unfold not_reachable in *.
      eapply Hnr in Hk.
      destruct Hk as [w Hw].
      rewrite Hi in Hw; discriminate.
      eapply find_Some_add_remove_many; eauto.
    Qed.
    erewrite <- not_reachable_add_remove_many; eauto.
    solve [eapply mapM_length; eauto].
    solve [rewrite map_length; eapply map_eq_length_eq in H0; eauto].
    eapply find_ADT_add_remove_many in H31; eauto.
    openhyp.
    eapply not_reachable_iff; eauto.
    eapply (direct_sum_in_not h2 h3); eauto.
    subst.
    unfold Locals.sel in *.
    subst' H30.
    solve [eapply find_Some_in; eauto].
    solve [rewrite map_length; eapply map_eq_length_eq in H0; eauto].
    
    (* p is in h3' *)
    unfold_related H13.
    copy_as H20 Hf; eapply H27 in H20.
    openhyp'.
    rename x1 into x3.
    rename x into st_callee'.
    (* Since there is no memory leak, ADT-holding x3 can only be RetVar or an ADT-holding argument *)
    copy_as H29 Hf3; eapply H17 in H29.
    openhyp.

    (* x3 is RetVar (i.e. p is the address of the returned ADT object) *)
    subst.
    unfold sel in *.
    unif x0.
    exists lhs.
    split.
    (* exists *)
    rewrite Locals.sel_upd_eq by eauto.
    rewrite StringMapFacts.add_eq_o by eauto.
    eauto.

    (* unique *)
    intros.
    openhyp.
    destruct (string_dec x' lhs).
    eauto.
    (* x' <> lhs *)
    rewrite Locals.sel_upd_ne in * by eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    unfold Locals.sel in *.
    symmetry in H; subst' H.
    eapply find_Some_add_remove_many in H20.
    openhyp.
    (* not_reachable *)
    unfold_related H18.
    copy_as H20 Hf'; eapply H18 in H20; simpl in *.
    eapply find_Some_direct_sum in H20; eauto; openhyp.
    eapply find_Some_in in H20.
    eapply find_Some_in in Hf.
    contradict Hf.
    eapply (direct_sum_in_not h2 h3'); eauto.
    eapply not_reachable_iff in H; eauto.
    contradict H.
    solve [eapply find_Some_in; eauto].
    (* reachable *)
    eapply nth_error_map_elim in H29.
    openhyp.
    eapply map_eq_nth_error_1 in H0; [ | eauto ..].
    openhyp.
    unfold StringMap.key in *.
    unif x2.
    unfold Locals.sel in *.
    assert (RetVar spec = x1).
    eapply H28.
    split.
    rewrite <- H31.
    symmetry; eapply H5.
    eapply in_args_not_assigned; eauto.
    eapply Locals.nth_error_In; eauto.
    solve [eauto].
    subst.
    eapply Locals.nth_error_In in H29; eauto.
    contradict H29.
    solve [eapply not_incl_spec].
    solve [eauto].
    solve [eapply mapM_length; eauto].
    solve [rewrite map_length; eapply map_eq_length_eq in H0; eauto].

    (* x3 is an arg referring to an ADT object (i.e. p is the address of an output ADT object, not the returned ADT object) *)
    rename x into i.
    copy_as H0 H00; eapply map_eq_nth_error_1 in H0; [ | eauto ..].
    openhyp.
    rename x into arg.
    destruct (string_dec arg lhs).
    (* arg = lhs *)
    subst.
    contradict H12.
    eapply not_mapsto_adt_not_true_iff.
    eapply mapM_nth_error_1 in H11; eauto.
    openhyp.
    unif x.
    solve [eexists; eauto].

    (* arg <> lhs *)
    exists arg.
    split.
    (* exists *)
    rewrite Locals.sel_upd_ne by eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    unfold Locals.sel in *.
    split.
    subst.
    rewrite <- H31.
    eapply H5.
    eapply in_args_not_assigned; eauto.
    eapply Locals.nth_error_In; eauto.

    eapply find_Some_add_remove_many.
    solve [eauto].
    solve [eapply mapM_length; eauto].
    solve [rewrite map_length; eapply map_eq_length_eq in H00; eauto].
    right.
    exists i, x1.
    split.
    eauto.
    split.
    eauto.
    erewrite map_nth_error by eauto.
    f_equal; solve [eauto].

    (* unique *)
    intros.
    openhyp.
    destruct (string_dec x' lhs).
    (* x' = lhs *)
    subst.
    rewrite Locals.sel_upd_eq in * by eauto.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    inject H33.
    set (retp := Locals.sel vs_callee' (RetVar spec)) in *.
    set (p := Locals.sel vs_callee' x3) in *.
    assert (x3 = RetVar spec).
    eapply H28.
    solve [eauto].
    unfold_all; subst.
    eapply Locals.nth_error_In in H29; eauto.
    contradict H29.
    solve [eapply not_incl_spec].
    (* x' <> lhs *)
    rewrite Locals.sel_upd_ne in * by eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    unfold Locals.sel in *; subst.
    assert (vs arg = vs x').
    rewrite H32.
    rewrite <- H31.
    eapply H5.
    eapply in_args_not_assigned; eauto.
    solve [eapply Locals.nth_error_In; eauto].
    copy_as H11 Hmm; eapply mapM_nth_error_1 in Hmm; eauto.
    openhyp.
    unif x.
    eapply find_ADT_add_remove_many in H33; eauto.
    openhyp.
    eapply (related_no_alias s_st); eauto.
    solve [rewrite map_length; eapply map_eq_length_eq in H00; eauto].


    Focus 7.
    (* call-axiomatic *)

    Import Semantics.

    Fixpoint make_triples pairs (outs : list (ArgOut ADTValue)) :=
      match pairs, outs with
        | p :: ps, o :: os => {| Word := fst p; ADTIn := snd p; ADTOut := o |} :: make_triples ps os
        | _, _ => nil
      end.
    Lemma split_triples : forall triples words_cinput coutput, words_cinput = List.map (fun x => (Word x, ADTIn x)) triples -> coutput = List.map (@ADTOut _) triples -> triples = make_triples words_cinput coutput.
    Proof.
      induction triples; destruct words_cinput; destruct coutput; simpl in *; intros; try discriminate.
      eauto.
      destruct a; inject H; inject H0.
      f_equal; eauto.
    Qed.
    Lemma split_triples' : forall triples words cinput coutput, words = List.map (@Word _) triples -> cinput = List.map (@ADTIn _) triples -> coutput = List.map (@ADTOut _) triples -> triples = make_triples (combine words cinput) coutput.
    Proof.
      induction triples; destruct words; destruct cinput; destruct coutput; simpl in *; intros; try discriminate.
      eauto.
      destruct a; inject H; inject H0; inject H1.
      f_equal; eauto.
    Qed.
    Lemma nth_error_make_triples_intro words_cinput : forall coutput i p a a', nth_error words_cinput i = Some (p, a) -> nth_error coutput i = Some a' -> nth_error (make_triples words_cinput coutput) i = Some {| Word := p; ADTIn := a; ADTOut := a'|}.
    Proof.
      induction words_cinput; destruct coutput; destruct i; simpl in *; intros; try discriminate.
      destruct a; inject H; inject H0; eauto.
      eauto.
    Qed.
    Lemma nth_error_make_triples_elim wis : forall os i p a a', nth_error (make_triples wis os) i = Some {| Word := p; ADTIn := a; ADTOut := a' |} -> nth_error wis i = Some (p, a) /\ nth_error os i = Some a'.
    Proof.
      induction wis; destruct os; destruct i; simpl in *; intros; try discriminate.
      destruct a; inject H; eauto.
      eauto.
    Qed.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.

    Lemma make_triples_Word_ADTIn : forall pairs outs, length outs = length pairs -> List.map (fun x => (Word x, ADTIn x)) (make_triples pairs outs) = pairs.
      induction pairs; destruct outs; simpl; intuition.
      f_equal; auto.
    Qed.

    Lemma make_triples_ADTOut : forall pairs outs, length outs = length pairs -> List.map ADTOut (make_triples pairs outs) = outs.
      induction pairs; destruct outs; simpl; intuition.
      f_equal; auto.
    Qed.

    unfold_all.
    injection H6; intros; subst; clear H6.
    simpl in *.
    destruct (option_dec (Word2Spec s_env (SemanticsExpr.eval (fst v) e))).
    2 : rewrite e0 in *; simpl in *; discriminate.
    destruct s0.
    rewrite e0 in *; simpl in *.
    inject H.
    destruct x; simpl in *.
    2 : discriminate.
    destruct a; simpl in *.
    unfold compile_ax in *; simpl in *.
    injection H6; intros; subst; simpl in *; clear H6.

    inversion H10; subst.
    Focus 2.
    replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
    rewrite e0 in *.
    discriminate.
    
    unfold_all.
    replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
    rewrite e0 in *.
    inject H13.
    rewrite map_map in H0; simpl in *.

    rename l into args.
    destruct v as [vs h123]; simpl in *.
    rename h1 into h23.

    set (cinput := List.map (Semantics.ADTIn (ADTValue:=ADTValue)) triples) in *.
    set (coutput := List.map (Semantics.ADTOut (ADTValue:=ADTValue)) triples) in *.
    set (words := List.map (Semantics.Word (ADTValue:=ADTValue)) triples) in *.
    set (cinput_coutput := List.map (fun x => (Semantics.ADTIn x, Semantics.ADTOut x)) triples) in *.
    set (words_cinput := List.map (fun x => (Semantics.Word x, Semantics.ADTIn x)) triples) in *.
    assert (input = List.map CitoIn_FacadeIn cinput).
    Lemma good_input_mapM args : 
      forall words cinput input h h2 st vs,
        Forall (word_adt_match h) (combine words cinput) ->
        length words = length cinput ->
        h2 <= h ->
        related st (vs, h2) ->
        List.map (fun x => vs x) args = words ->
        mapM (sel st) args = Some input ->
        let input' := List.map CitoIn_FacadeIn cinput in
        same_types input input' ->
        input = input'.
    Proof.
      simpl; induction args; destruct words; destruct cinput; destruct input; try solve [simpl in *; intros; eauto; try discriminate].
      intros until 5; intros Hmm; intros; eapply mapM_length in Hmm; simpl in *; discriminate.
      rename a into x.
      intros h h2 st vs Hfa Hl Hsm Hr Hm Hmm Hte.
      simpl in *.
      destruct (option_dec (sel st x)) as [[y Hy] | Hn].
      2 : rewrite Hn in *; discriminate.
      rewrite Hy in *.
      destruct (option_dec (mapM (sel st) args)) as [[ys Hys] | Hn].
      2 : rewrite Hn in *; discriminate.
      rewrite Hys in *.
      inject Hmm.
      inject Hm.
      inject Hl.
      inversion Hfa; subst.
      inversion Hte; subst.
      f_equal.
      2 : solve [eapply IHargs; eauto].
      eapply Hr in Hy; simpl in *.
      unfold word_adt_match in H2.
      destruct s as [w | a]; simpl in *.
      subst.
      destruct v as [w' | a']; simpl in *.
      subst; eauto.
      intuition.
      destruct v as [w' | a']; simpl in *.
      intuition.
      eapply submap_find in Hy; eauto.
      unfold Locals.sel in *.
      unif a'.
      eauto.
    Qed.

    unfold_all.
    eapply good_input_mapM; eauto.
    solve [rewrite combine_map; destruct H1; eauto].
    solve [repeat rewrite map_length; eauto].
    eapply PreCondTypeConform; eauto.
    repeat rewrite map_length; eauto.
    eapply mapM_length in H14; eauto.
    eapply map_eq_length_eq in H0; eauto; rewrite <- H0.
    solve [eauto].

    rewrite H in *.

    eexists.
    split.
    eapply RunsToCallAx.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    simpl.
    eauto.
    instantiate (1 := coutput).
    unfold_all.
    repeat rewrite map_length; eauto.
    simpl.
    assert (combine (List.map CitoIn_FacadeIn cinput) coutput = List.map CitoInOut_FacadeInOut cinput_coutput) by (unfold_all; repeat rewrite map_map; rewrite combine_map; eauto).
    unfold Semantics.ArgOut in *.
    unfold Value in *.
    rewrite H6.
    eauto.
    reflexivity.

    Definition no_alias (words_cinput : list (W * ArgIn ADTValue)) := forall i j p (ai aj : ADTValue), nth_error words_cinput i = Some (p, inr ai) -> nth_error words_cinput j = Some (p, inr aj) -> i = j.

    assert (words_cinput = combine words cinput) by (unfold_all; rewrite combine_map; eauto).

    assert (no_alias words_cinput).

    Lemma NoDup_no_alias st vs h args words cinput input words_cinput :
      related st (vs, h) ->
      NoDup args ->
      List.map (fun x => vs x) args = words ->
      input = List.map CitoIn_FacadeIn cinput ->
      mapM (sel st) args = Some input ->
      words_cinput = combine words cinput ->
      no_alias words_cinput.
    Proof.
      intros Hr Hnd Hm Hid Hmm Hwid.
      subst.
      unfold no_alias.
      intros i j p ai aj Hi Hj.
      eapply nth_error_combine_elim in Hi; eauto.
      destruct Hi as [Hai Hii].
      eapply nth_error_combine_elim in Hj; eauto.
      destruct Hj as [Haj Hij].
      eapply nth_error_map_elim in Hai; eauto.
      destruct Hai as [xi [Hai ?]]; subst.
      eapply nth_error_map_elim in Haj; eauto.
      destruct Haj as [xj [Haj ?]]; subst.
      copy_as Hai Hai'; eapply mapM_nth_error_1 in Hai'; eauto.
      destruct Hai' as [vi [Hii' Hvi]]. 
      eapply nth_error_map_elim in Hii'; eauto.
      destruct Hii' as [ai' [Hii' Hai']].
      unfold Cito.ArgIn, ArgIn in *.
      unif ai'; simpl in *.
      copy_as Haj Haj'; eapply mapM_nth_error_1 in Haj'; eauto.
      destruct Haj' as [vj [Hij' Hvj]]. 
      eapply nth_error_map_elim in Hij'; eauto.
      destruct Hij' as [aj' [Hij' Haj']].
      unfold Cito.ArgIn, ArgIn in *.
      unif aj'; simpl in *.
      assert (xi = xj) by (eapply related_no_alias; eauto).
      subst; eapply NoDup_nth_error in Hnd; eauto.
    Qed.

    eapply NoDup_no_alias; eauto.
    rewrite H.
    eauto.

    set (h1 := h123 - h23) in *.
    assert (direct_sum h1 h23 h123) by (eapply diff_direct_sum; eauto).

    rename s into lhs.
    rename e into e_f.

    assert (h1 <= fold_left (store_out (ADTValue:=ADTValue)) triples h123).
    unfold Submap.
    intros p a Hf.
    eapply diff_find_Some_iff in Hf.
    openhyp.

    Definition not_reachable_p p (words_cinput : list (W * ArgIn ADTValue)) := forall i v, nth_error words_cinput i = Some (p, v) -> exists w, v = inl w.

    Lemma fold_bwd p a triples : 
      forall h,
        let words_cinput := List.map (fun x => (Word x, ADTIn x)) triples in
        no_alias words_cinput -> 
        ((not_reachable_p p words_cinput /\ find p h = Some a) \/ 
         exists i input, nth_error triples i = Some {| Word := p; ADTIn := inr input; ADTOut := Some a |}) ->
        find p (List.fold_left store_out triples h) = Some a.
    Proof.
      induction triples; simpl in *.
      intros h ? H.
      openhyp.
      eauto.
      rewrite nth_error_nil in H; discriminate.

      destruct a0 as [tp ti to]; simpl in *.
      intros h Hna H.
      eapply IHtriples.
      Lemma no_alias_tail ls : forall e, no_alias (e :: ls) -> no_alias ls.
      Proof.
        unfold no_alias; intros e Hna.
        intros i j p ai aj Hi Hj.
        assert (S i = S j).
        eapply Hna; eauto.
        inject H; eauto.
      Qed.
      eapply no_alias_tail; eauto.
      destruct H as [[Hnr hf] | [i [ai Ht]] ].
      left.
      split.
      Lemma not_reachable_p_incl ls1 ls2 p : List.incl ls1 ls2 -> not_reachable_p p ls2 -> not_reachable_p p ls1.
        unfold not_reachable_p; intros Hin Hnr.
        intros i v Hi.
        eapply incl_nth_error in Hi; eauto; openhyp.
        eapply Hnr in H; eauto; openhyp.
      Qed.
      Lemma not_reachable_p_tail ls e p : not_reachable_p p (e :: ls) -> not_reachable_p p ls.
        intros; eapply not_reachable_p_incl; eauto.
        eapply incl_tl; eapply incl_refl; eauto.
      Qed.
      eapply not_reachable_p_tail; eauto.
      unfold store_out; simpl.
      destruct ti as [w | ai].
      eauto.
      destruct to as [ao |].
      destruct (Word.weq p tp).
      Lemma not_not_reachable_p p a ls : ~ not_reachable_p p ((p, inr a) :: ls).
      Proof.
        unfold not_reachable_p.
        nintro.
        specialize (H 0 (inr a)).
        simpl in *.
        edestruct H; eauto.
        discriminate.
      Qed.
      subst; solve [eapply not_not_reachable_p in Hnr; intuition].
      solve [rewrite add_neq_o; eauto].
      destruct (Word.weq p tp).
      subst; solve [eapply not_not_reachable_p in Hnr; intuition].
      solve [rewrite remove_neq_o; eauto].
      destruct i as [| i]; simpl in *.
      inject Ht.
      left.
      split.
      Lemma no_alias_not_reachable_p p a ls : no_alias ((p, inr a) :: ls) -> not_reachable_p p ls.
      Proof.
        intros Hna.
        unfold not_reachable_p.
        intros i v Hi.
        destruct v.
        eauto.
        unfold no_alias in *.
        assert (S i = 0).
        eapply Hna; simpl in *; eauto.
        discriminate.
      Qed.
      eapply no_alias_not_reachable_p; eauto.
      unfold store_out; simpl.
      solve [rewrite add_eq_o; eauto].

      right.
      eauto.
    Qed.

    Lemma fold_fwd : 
      forall k (v : ADTValue) ls h,
        WordMap.MapsTo k v (fold_left store_out ls h) -> 
        (WordMap.MapsTo k v h /\ 
         forall a o, ~List.In {| Word := k; ADTIn := inr a; ADTOut := o |} ls) 
        \/ exists a, 
             List.In {| Word := k; ADTIn := inr a; ADTOut := Some v |} ls.
    Proof.
      induction ls; simpl; intuition.
      apply IHls in H; intuition.

      unfold store_out, Semantics.store_out in H; simpl in H.
      destruct a; simpl in *.
      destruct ADTIn.
      left; intuition eauto.
      discriminate.
      destruct ADTOut.
      apply add_mapsto_iff in H; intuition subst.
      eauto.
      left; intuition.
      eauto 2.
      apply remove_mapsto_iff in H; intuition subst.
      left; intuition.
      eauto 2.
      destruct H0.
      eauto.
    Qed.

    Lemma fold_store_out_elim p a triples words_cinput coutput h :
      words_cinput = List.map (fun x => (Word x, ADTIn x)) triples ->
      coutput = List.map ADTOut triples ->
      find p (List.fold_left store_out triples h) = Some a -> 
      (not_reachable_p p words_cinput /\ find p h = Some a) \/ 
      exists i input, nth_error triples i = Some {| Word := p; ADTIn := inr input; ADTOut := Some a |}.
    Proof.
      intros Hwid Hod Hf.
      subst.
      eapply find_mapsto_iff in Hf.
      eapply fold_fwd in Hf.
      destruct Hf as [[Hf Hnr] | [ai Hin]].
      eapply find_mapsto_iff in Hf.
      left.
      split.
      unfold not_reachable_p.
      intros i v Hwi.
      eapply nth_error_map_elim in Hwi.
      destruct Hwi as [[tp ti to] [Ht He]]; simpl in *.
      inject He.
      destruct v.
      eexists; eauto.
      eapply Locals.nth_error_In in Ht.
      solve [eapply Hnr in Ht; intuition].
      solve [eauto].

      right.
      eapply in_nth_error in Hin.
      destruct Hin as [i Ht].
      repeat eexists; eauto.
    Qed.

    Lemma fold_store_out_intro p a triples words_cinput coutput h :
      words_cinput = List.map (fun x => (Word x, ADTIn x)) triples ->
      coutput = List.map ADTOut triples ->
      no_alias words_cinput -> 
      ((not_reachable_p p words_cinput /\ find p h = Some a) \/ 
       exists i input, nth_error triples i = Some {| Word := p; ADTIn := inr input; ADTOut := Some a |}) ->
      find p (List.fold_left store_out triples h) = Some a.
    Proof.
      intros; subst; eapply fold_bwd; eauto.
    Qed.

    Lemma find_Some_fold_store_out p a words_cinput coutput h :
      no_alias words_cinput -> 
      length words_cinput = length coutput ->
      (find p (List.fold_left store_out (make_triples words_cinput coutput) h) = Some a <-> 
       ((not_reachable_p p words_cinput /\ find p h = Some a) \/ 
        exists i input, 
          nth_error words_cinput i = Some (p, inr input) /\
          nth_error coutput i = Some (Some a))).
    Proof.
      intros Hna Hl.
      split.
      intros Hf.
      eapply fold_store_out_elim in Hf; simpl; eauto.
      destruct Hf as [[Hnr Hf] | [i [ai Ht]]].
      left.
      rewrite make_triples_Word_ADTIn in *; eauto.
      right.
      exists i, ai.
      eapply nth_error_make_triples_elim in Ht; eauto.

      intros H.
      eapply fold_store_out_intro; eauto.
      rewrite make_triples_Word_ADTIn; eauto.
      destruct H as [[Hnr Hf] | [i [ai [Hwi Ho]]]].
      left.
      split.
      rewrite make_triples_Word_ADTIn; eauto.
      solve [eauto].
      right.
      exists i, ai.
      eapply nth_error_make_triples_intro; eauto.
    Qed.

    rewrite (@split_triples triples words_cinput coutput) by eauto.

    eapply find_Some_fold_store_out.
    eauto.
    unfold_all; repeat rewrite map_length; eauto.
    rewrite H6.
    left.
    split.
    Lemma not_in_not_reachable_p st vs h args words cinput p :
        related st (vs, h) -> 
        List.map (fun x => vs x) args = words -> 
        mapM (sel st) args = Some (List.map CitoIn_FacadeIn cinput) -> 
        ~ In p h ->
        not_reachable_p p (combine words cinput).
    Proof.
      intros Hr Hm Hmm Hni.
      unfold not_reachable_p.
      intros i v Hi.
      eapply nth_error_combine_elim in Hi.
      destruct Hi as [Hw Hi].
      eapply map_nth_error_2 in Hm; eauto.
      destruct Hm as [a [Ha Hp]].
      subst.
      eapply mapM_nth_error_1 in Hmm; eauto.
      destruct Hmm as [b [Hi' Hs]].
      eapply nth_error_map_elim in Hi'.
      destruct Hi' as [a' [? ?]].
      unfold Cito.ArgIn in *.
      unif a'.
      destruct v; simpl in *.
      eexists; eauto.
      eapply Hr in Hs; simpl in *.
      contradict Hni.
      eapply find_Some_in; eauto.
    Qed.
    eapply not_in_not_reachable_p; eauto.
    solve [eauto].

    split.
    (* h1 <= heap' *)
    rewrite H5.
    destruct ret; simpl in *.
    eauto.
    unfold separated in H4; simpl in *.
    openhyp.
    discriminate.
    Lemma add_new_submap elt k m : ~ In k m -> forall (v : elt), m <= add k v m.
    Proof.
      intros Hni v.
      unfold Submap.
      intros k' v' Hf.
      destruct (Word.weq k' k).
      subst.
      contradict Hni.
      eapply find_Some_in; eauto.
      rewrite add_neq_o by eauto; eauto.
    Qed.
    eapply submap_trans.
    eauto.
    solve [eapply add_new_submap; eauto].

    split.
    (* no illegal local variable overwrite *)
    intros.
    eapply singleton_iff_not in H18.
    rewrite Locals.sel_upd_ne by eauto.
    solve [eauto].

    split.
    (* newly allocated objects won't sabotage frame heap *)
    intros.
    destruct (string_dec x lhs).
    (* x = lhs *)
    rewrite e in *.
    eapply is_mapsto_adt_iff in H19.
    destruct H19 as [a H19].
    rewrite Locals.sel_upd_eq in * by eauto.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    destruct ret; simpl in *.
    discriminate.
    inject H19.
    unfold separated in H4; simpl in *.
    destruct H4 as [H4 | H4].
    discriminate.
    solve [eapply submap_not_in; eauto].
    (* x <> lhs *)
    eapply is_mapsto_adt_iff in H19.
    destruct H19 as [a H19].
    rewrite Locals.sel_upd_ne in * by eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    destruct H18 as [H18 | H18].
    eapply is_mapsto_adt_false_iff in H18.
    contradict H18.
    eapply find_ADT_add_remove_many; eauto.
    solve [subst; unfold_all; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
    solve [intuition].

    Lemma not_reachable_p_not_reachable st vs args words cinput x :
        List.map (fun x => vs x) args = words -> 
        mapM (sel st) args = Some (List.map CitoIn_FacadeIn cinput) -> 
        not_reachable_p (vs x) (combine words cinput) -> 
        not_reachable x args (List.map CitoIn_FacadeIn cinput).
    Proof.
      intros Hm Hmm.
      intros Hnr; unfold not_reachable_p, not_reachable in *.
      intros i Hi.
      eapply map_nth_error_1 in Hm; eauto.
      eapply mapM_nth_error_1 in Hmm; eauto.
      openhyp; rename x0 into v.
      eapply nth_error_map_elim in H.
      openhyp; subst; rename x0 into cv.
      set (p := vs x) in *.
      edestruct Hnr.
      eapply nth_error_combine; eauto.
      subst; rename x0 into w.
      exists w.
      erewrite map_nth_error; eauto; eauto.
    Qed.

    Lemma not_reachable_not_reachable_p st vs h args words cinput x a :
        related st (vs, h) -> 
        NoDup args ->
        List.map (fun x => vs x) args = words -> 
        mapM (sel st) args = Some (List.map CitoIn_FacadeIn cinput) -> 
        StringMap.find x st = Some (ADT a) ->
        not_reachable x args (List.map CitoIn_FacadeIn cinput) ->
        not_reachable_p (vs x) (combine words cinput).
    Proof.
      intros Hr Hnd Hm Hmm Hf.
      intros Hnr; unfold not_reachable_p, not_reachable in *.
      intros i v Hi.
      eapply nth_error_combine_elim in Hi.
      openhyp.
      eapply map_nth_error_2 in Hm; eauto.
      openhyp; subst.
      rename x0 into x'.
      eapply mapM_nth_error_1 in Hmm; eauto.
      openhyp; subst.
      rename x0 into v'.
      eapply nth_error_map_elim in H3.
      openhyp; subst.
      unfold Cito.ArgIn in *.
      unif x0.
      destruct v; simpl in *.
      eexists; eauto.
      assert (x = x').
      eapply related_no_alias; eauto.
      subst.
      eapply Hnr in H1.
      openhyp; subst.
      eapply nth_error_map_elim in H1.
      openhyp; subst.
      unif x0.
      simpl in *; discriminate.
    Qed.

    Lemma add_remove_many_fold_store_out_iff : 
      forall st vs h2 args triples words cinput coutput input h h' p a, 
        related st (vs, h2) ->
        NoDup args ->
        words = List.map (@Word _) triples ->
        cinput = List.map (@ADTIn _) triples ->
        coutput = List.map (@ADTOut _) triples ->
        input = List.map CitoIn_FacadeIn cinput ->
        List.map (fun x => vs x) args = words ->
        mapM (sel st) args = Some input ->
        h2 <= h ->
        let h1 := h - h2 in
        h' == fold_left store_out triples h ->
        h1 <= h' ->
        ((exists x,
            p = Locals.sel vs x /\
            StringMap.find x (add_remove_many args input (wrap_output coutput) st) = Some (ADT a)) <->
         find p (h' - h1) = Some a).
    Proof.
      intros st vs h2 args triples words cinput coutput input h h' p a Hr Hnd Hw Hci Hco Hi Hm Hmm Hsm2 h1 He Hsm1'.
      assert (Hna : no_alias (combine words cinput)) by (eapply NoDup_no_alias; eauto).
      assert (Hsm1 : h1 <= h) by eapply diff_submap.
      assert (Hd : Disjoint h1 h2) by eapply diff_disjoint.
      assert (Hds : direct_sum h1 h2 h) by (eapply diff_direct_sum; eauto).
      
      rewrite He.
      erewrite (@split_triples' triples) by eauto.
      split; intro Hf.

      (* direction 1 *)
      destruct Hf as [x Hf].
      destruct Hf as [Hp Hf].
      eapply find_Some_add_remove_many in Hf.
      openhyp.

      (* not_reachable *)
      unfold_related Hr.
      copy_as H0 H00; eapply H1 in H0; simpl in *.
      eapply diff_find_Some_iff.
      split.

      eapply find_Some_fold_store_out.
      solve [eauto].
      solve [subst; rewrite combine_length_eq; repeat rewrite map_length; eauto].
      left.
      split.
      subst; eapply not_reachable_not_reachable_p; eauto.
      solve [subst; eauto].

      subst; eapply Disjoint_in_not.
      solve [eapply Disjoint_sym; eauto].
      solve [eapply find_Some_in; eauto].

      (* reachable *)
      rename x0 into i.
      rename a into a'.
      rename x1 into a.
      eapply mapM_nth_error_2 in Hmm; eauto; openhyp.
      unif x0.
      eapply nth_error_map_elim in H0; openhyp.
      destruct x0; simpl in *.
      discriminate.
      inject H2.
      eapply nth_error_map_elim in H0; openhyp.
      destruct x0; simpl in *; subst.
      unfold wrap_output in H1; eapply nth_error_map_elim in H1; openhyp.
      destruct x0; simpl in *.
      2 : discriminate.
      inject H2.
      eapply nth_error_map_elim in H1; openhyp.
      unif x0; simpl in *; subst.
      eapply map_eq_nth_error_1 in Hm; [ | eauto ..]; openhyp.
      unif x0; simpl in *; subst.

      unfold_related Hr.
      eapply H1 in H3; simpl in *.
      eapply diff_find_Some_iff.
      split.

      eapply find_Some_fold_store_out.
      solve [eauto].
      solve [subst; rewrite combine_length_eq; repeat rewrite map_length; eauto].
      right.
      exists i; exists a.
      unfold Locals.sel in *.
      split.

      solve [erewrite nth_error_combine; eauto; erewrite map_nth_error by eauto; simpl; eauto].
      solve [erewrite map_nth_error by eauto; simpl; eauto].

      subst; eapply Disjoint_in_not.
      solve [eapply Disjoint_sym; eauto].
      solve [eapply find_Some_in; eauto].

      solve [eauto].
      solve [subst; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
      solve [subst; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].

      (* direction 2 *)
      eapply diff_find_Some_iff in Hf; openhyp.
      eapply find_Some_fold_store_out in H.
      openhyp.

      (* p is an address not affected by the call *)
      eapply find_Some_direct_sum in H1; [ | eauto .. ].
      openhyp.
      solve [contradict H0; eapply find_Some_in; eauto].
      unfold_related Hr.
      eapply H3 in H1; simpl in *.
      openhyp'.
      exists x.
      split.
      eauto.
      eapply find_Some_add_remove_many.
      solve [eauto].
      solve [subst; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
      solve [subst; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
      left.
      split.
      subst; eapply not_reachable_p_not_reachable; eauto.
      solve [eauto].

      (* p is the address of an output ADT object (but not the returned ADT object) *)
      rename x into i.
      rename x0 into a0.
      eapply nth_error_combine_elim in H; openhyp.
      subst.
      eapply nth_error_map_elim in H; openhyp.
      destruct x; simpl in *; subst.
      eapply nth_error_map_elim in H2; openhyp.
      unif x; simpl in *; subst.
      eapply nth_error_map_elim in H1; openhyp.
      unif x; simpl in *; subst.
      eapply mapM_nth_error_2 in Hmm.
      2 : solve [repeat eapply map_nth_error; eauto].
      simpl in *.
      openhyp.
      copy_as Hm Hm'; eapply map_eq_nth_error_1 in Hm'; [ | eauto ..]; openhyp.
      unif x0; simpl in *; subst.
      exists x.
      split.
      eauto.
      eapply find_Some_add_remove_many.
      solve [eauto].
      solve [repeat rewrite map_length; eapply map_eq_length_eq; eauto].
      solve [unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
      right.
      exists i; exists a0.
      split.
      eauto.
      split.
      solve [repeat erewrite map_nth_error; eauto; simpl; eauto].
      solve [unfold wrap_output; repeat erewrite map_nth_error; eauto; simpl; eauto].
      solve [eauto].
      solve [subst; rewrite combine_length_eq; repeat rewrite map_length; eauto].

    Qed.

    Lemma add_remove_many_fold_store_out : 
      forall st vs h2 args triples words cinput coutput input h h' x p a, 
        related st (vs, h2) ->
        NoDup args ->
        words = List.map (@Word _) triples ->
        cinput = List.map (@ADTIn _) triples ->
        coutput = List.map (@ADTOut _) triples ->
        input = List.map CitoIn_FacadeIn cinput ->
        List.map (fun x => vs x) args = words ->
        mapM (sel st) args = Some input ->
        h2 <= h ->
        let h1 := h - h2 in
        h' == fold_left store_out triples h ->
        h1 <= h' ->
        p = Locals.sel vs x ->
        StringMap.find x (add_remove_many args input (wrap_output coutput) st) = Some (ADT a) ->
         find p (h' - h1) = Some a.
    Proof.
      intros.
      eapply add_remove_many_fold_store_out_iff; eauto.
    Qed.

    (* related *)
    unfold related; simpl.
    split.
    (* related (1) *)
    intros x v Hf.
    destruct (string_dec x lhs).
    (* x = lhs *)
    subst' e.
    rewrite H5.
    rewrite Locals.sel_upd_eq in * by eauto; simpl.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    inject Hf.
    destruct ret; simpl in *.
    eauto.
    eapply diff_find_Some_iff.
    split.
    solve [rewrite add_eq_o in * by eauto; eauto].
    unfold separated in H4; simpl in *.
    openhyp.
    discriminate.
    solve [eapply submap_not_in; eauto].

    (* x <> lhs *)
    rewrite Locals.sel_upd_ne by eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    destruct v; simpl in *.

    (* v is scalar *)
    eapply find_Some_add_remove_many in Hf.
    openhyp.
    unfold_related H8.
    eapply H8 in H19; simpl in *.
    eauto.
    Lemma wrap_output_not_sca coutput i w : nth_error (wrap_output coutput) i <> Some (Some (SCA ADTValue w)).
    Proof.
      unfold wrap_output.
      rewrite ListFacts.map_nth_error_full.
      destruct (option_dec (nth_error coutput i)) as [s | e]; simpl in *.
      destruct s as [a e]; rewrite e in *; simpl in *.
      destruct a; simpl in *; discriminate.
      rewrite e in *; discriminate.
    Qed.
    contradict H20.
    eapply wrap_output_not_sca; eauto.
    solve [eauto].
    solve [unfold_all; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
    solve [unfold_all; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].

    (* v is ADT object *)
    rewrite H5.

    Definition ret_doesn't_matter (p addr : W) (ret : Ret ADTValue) := p <> addr \/ exists w, ret = inl w.
    Definition p_addr_ret_dec (p addr : W) (ret : Ret ADTValue) : { a : ADTValue | ret = inr a /\ p = addr} + {ret_doesn't_matter p addr ret}.
      destruct ret.
      right; right; eexists; eauto.
      destruct (Word.weq p addr).
      left; eexists; eauto.
      right; left; eauto.
    Defined.
    destruct (p_addr_ret_dec (Locals.sel vs x) addr ret).
    destruct s; openhyp.
    subst; simpl in *.
    unfold separated in H4; simpl in *.
    openhyp.
    discriminate.
    contradict H.
    eapply add_remove_many_fold_store_out in Hf; eauto.
    eapply diff_find_Some_iff in Hf; openhyp.
    solve [eapply find_Some_in; eauto].

    Lemma find_ret_doesn't_matter p addr ret triples h h1 : ret_doesn't_matter p addr ret -> find p (heap_upd_option (fold_left store_out triples h) (fst (decide_ret addr ret)) (snd (decide_ret addr ret)) - h1) = find p (fold_left store_out triples h - h1).
    Proof.
      intros Hdm; destruct Hdm.
      2 : solve [openhyp; subst; simpl; eauto].
      destruct ret; simpl in *.
      solve [openhyp; subst; simpl; eauto].
      solve [eapply option_univalence; intros v; split; intros Hf; eapply diff_find_Some_iff in Hf; eapply diff_find_Some_iff; rewrite add_neq_o in *; eauto].
    Qed.
    rewrite find_ret_doesn't_matter by eauto.
    solve [eapply add_remove_many_fold_store_out in Hf; eauto].

    (* related (2) *)
    intros.
    rewrite H5 in H18.

    destruct (p_addr_ret_dec p addr ret).

    (* p is the address of the return ADT object *)
    destruct s; openhyp.
    subst; simpl in *.
    eapply diff_find_Some_iff in H18; openhyp.
    rewrite add_eq_o in * by eauto.
    inject H.
    exists lhs.
    split.
    (* exists *)
    rewrite Locals.sel_upd_eq by eauto.
    rewrite StringMapFacts.add_eq_o by eauto.
    eauto.
    (* unique *)
    intros.
    openhyp.
    destruct (string_dec x' lhs).
    eauto.
    rewrite Locals.sel_upd_ne in * by eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    unfold separated in H4; simpl in *.
    openhyp.
    discriminate.
    contradict H4.
    subst.
    eapply add_remove_many_fold_store_out in H19; eauto.
    eapply diff_find_Some_iff in H19; openhyp.
    solve [eapply find_Some_in; eauto].

    (* p is not the address of the return ADT object *)
    rewrite find_ret_doesn't_matter in H18 by eauto.
    eapply add_remove_many_fold_store_out_iff in H18; eauto.
    2 : solve [rewrite H; eauto].
    rewrite H in H18.
    openhyp.
    destruct (string_dec x lhs).
    subst.
    contradict H16.
    eapply not_mapsto_adt_not_true_iff.
    eapply find_ADT_add_remove_many; eauto.
    solve [unfold_all; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].

    exists x.
    split.
    (* exists *)
    rewrite Locals.sel_upd_ne by eauto.
    rewrite StringMapFacts.add_neq_o by eauto.
    eauto.

    (* unique *)
    intros.
    openhyp.
    destruct (string_dec x' lhs).
    subst' e.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    rewrite Locals.sel_upd_eq in * by eauto.
    destruct ret; simpl in *.
    discriminate.
    inject H21.
    solve [unfold ret_doesn't_matter in *; simpl in *; openhyp; intuition].
    rewrite StringMapFacts.add_neq_o in * by eauto.
    rewrite Locals.sel_upd_ne in * by eauto.
    eapply find_ADT_add_remove_many in H19; eauto; openhyp.
    eapply find_ADT_add_remove_many in H21; eauto; openhyp.
    solve [eapply related_no_alias; eauto].
    solve [unfold_all; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
    solve [unfold_all; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].

    Import Facade.

    Focus 3.
    (* if-true *)
    rename H1 into Hcomp.
    inject Hcomp.
    rename IHRunsTo into IHa.
    edestruct IHa as [s_st' [Hart [Hasm [Havs [Hanew Har]]]]]; clear IHa; eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eapply safe_if_true; eauto.
    eapply wneb_is_true; eauto.
    eapply safe_if_is_bool; eauto.
    openhyp.
    eexists.
    split.
    eapply RunsToIfTrue.
    eapply wneb_is_true; eauto.
    eapply safe_if_is_bool; eauto.
    eauto.
    split.
    eauto.
    split.
    intros s Hni.
    eapply Havs.
    solve [not_not; eapply in_or_app; eauto].
    solve [eauto].

    Focus 3.
    (* if-false *)
    rename H1 into Hcomp.
    inject Hcomp.
    rename IHRunsTo into IHa.
    edestruct IHa as [s_st' [Hart [Hasm [Havs [Hanew Har]]]]]; clear IHa; eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eapply safe_if_false; eauto.
    eapply wneb_is_false; eauto.
    eapply safe_if_is_bool; eauto.
    openhyp.
    eexists.
    split.
    eapply RunsToIfFalse.
    eapply wneb_is_false; eauto.
    eapply safe_if_is_bool; eauto.
    eauto.
    split.
    eauto.
    split.
    intros s Hni.
    eapply Havs.
    solve [not_not; eapply in_or_app; eauto].
    solve [eauto].

    Lemma safe_seq_1 : forall (env : Env ADTValue) a b st, Safe env (Seq a b) st -> Safe env a st.
    Proof.
      intros.
      inversion H; subst.
      openhyp.
      eauto.
    Qed.

    Ltac pick_related := try match goal with | |- related _ _ => eauto end.

    Lemma safe_seq_2 : forall (env : Env ADTValue) a b st, Safe env (Seq a b) st -> forall st', RunsTo env a st st' -> Safe env b st'.
    Proof.
      intros.
      inversion H; subst.
      openhyp.
      eauto.
    Qed.

    Infix "===" := (@StringMapFacts.M.Equal _) (at level 70).
    Hint Extern 0 (_ === _) => reflexivity.
    Lemma related_Equal_1 st vs h st' vs' h' : st === st' -> (forall x, Locals.sel vs x = Locals.sel vs' x) -> h == h' -> related st (vs, h) -> related st' (vs', h').
    Proof.
      unfold related; intros Hst Hvs Hh; intros [Hr1 Hr2]; simpl in *.
      split.
      intros k v Hfk.
      rewrite <- Hst in Hfk.
      rewrite <- Hh.
      rewrite <- Hvs.
      eauto.
      intros p a Hfp.
      rewrite <- Hh in Hfp.
      eapply Hr2 in Hfp.
      destruct Hfp as [k [Hex Hu]].
      exists k.
      split.
      rewrite <- Hst.
      rewrite <- Hvs.
      eauto.
      intros k'.
      rewrite <- Hst.
      rewrite <- Hvs.
      eauto.
    Qed.

    Lemma related_Equal st vs h st' vs' h' : st === st' -> (forall x, Locals.sel vs x = Locals.sel vs' x) -> h == h' -> (related st (vs, h) <-> related st' (vs', h')).
    Proof.
      intros Hst Hvs Hh; split; intros Hr.
      eapply related_Equal_1; eauto.
      eapply related_Equal_1; pick_related; eauto.
      symmetry; eauto.
      symmetry; eauto.
    Qed.

    Definition new_adt_no_pollute s_st vs s_st' vs' h := forall x, @is_mapsto_adt ADTValue x s_st = false \/ is_mapsto_adt x s_st = true /\ Locals.sel vs x <> Locals.sel vs' x -> @is_mapsto_adt ADTValue x s_st' = true -> ~ @In ADTValue (Locals.sel vs' x) h.
    Lemma new_adt_no_pollute_seq st vs st' vs' st'' vs'' h h' h'' : new_adt_no_pollute st vs st' vs' h -> new_adt_no_pollute st' vs' st'' vs'' h' -> h == h'' -> h' == h'' -> new_adt_no_pollute st vs st'' vs'' h''.
    Proof.
      unfold new_adt_no_pollute; intros Hanew Hbnew Hheq Hheq' x Hmt Hmt''.
      unfold Locals.sel in *.
      destruct (boolcase (is_mapsto_adt x st')) as [Hmt' | Hmtf'].
      destruct (Word.weq (vs' x) (vs'' x)) as [Heq | Hne].
      rewrite <- Heq in *.
      rewrite <- Hheq.
      solve [eapply Hanew; eauto].
      eapply Hbnew in Hmt''.
      rewrite <- Hheq'.
      solve [eauto].
      solve [right; eauto].
      eapply Hbnew in Hmt''.
      rewrite <- Hheq'.
      solve [eauto].
      solve [left; eauto].
    Qed.

    Focus 2.
    (* seq *)
    subst.
    rename H1 into Hcomp.
    inject Hcomp.
    rename s1 into a.
    rename s2 into b.
    destruct v as [vs h]; simpl in *.
    destruct v' as [vs' h']; simpl in *.
    destruct v'' as [vs'' h'']; simpl in *.
    rename h1 into h2.
    rename IHRunsTo1 into IHa.
    rename IHRunsTo2 into IHb.
    rename H into Hartt.
    rename H0 into Hbrtt.
    rename H2 into Hsm.
    rename H5 into Hsf.
    rename H3 into Hr.
    edestruct IHa as [s_st' [Hart [Hasm [Havs [Hanew Har]]]]]; clear IHa; eauto.
    eapply safe_seq_1; eauto.
    edestruct IHb as [s_st'' [Hbrt [Hbsm [Hbvs [Hbnew Hbr]]]]]; clear IHb; pick_related; eauto.
    solve [eapply diff_submap; eauto].
    eapply safe_seq_2; eauto.
    set (h1 := h - h2) in *.
    rewrite diff_submap_cancel in Hbsm by eauto.
    exists s_st''.
    split.
    eapply RunsToSeq; eauto.
    split.
    eauto.
    split.
    intros s Hni.
    etransitivity.
    eapply Havs.
    not_not; eapply in_or_app; eauto.
    eapply Hbvs.
    not_not; eapply in_or_app; eauto.
    split.
    eapply new_adt_no_pollute_seq; eauto.
    solve [rewrite diff_submap_cancel; eauto].
    eapply related_Equal; pick_related; eauto.
    solve [rewrite diff_submap_cancel; eauto].

    Focus 2.
    (* while-true *)
    subst.
    rename H2 into Hcomp.
    inject Hcomp.
    destruct v as [vs h]; simpl in *.
    destruct v' as [vs' h']; simpl in *.
    destruct v'' as [vs'' h'']; simpl in *.
    rename h1 into h2.
    rename e into cond.
    rename s into body.
    rename H into Hcondt.
    rename H3 into Hsm.
    rename H4 into Hr.
    rename H6 into Hsf.
    rename H0 into Hbrtt.
    rename H1 into Hlrtt.
    rename IHRunsTo1 into IHb.
    rename IHRunsTo2 into IHl.
    inversion Hsf as [ | | | | ? ? ? loop' Hcond Hsfb Hrtsf | | | | | ]; unfold_all; subst.
    edestruct IHb as [s_st' [Hbrt [Hbsm [Hbvs [Hbnew Hbr]]]]]; clear IHb; eauto.
    edestruct IHl as [s_st'' [Hlrt [Hlsm [Hlvs [Hlnew Hlr]]]]]; clear IHl; pick_related; eauto; simpl; eauto.
    solve [eapply diff_submap; eauto].
    rewrite diff_submap_cancel in Hlsm by eauto.
    exists s_st''.
    split.
    eapply RunsToWhileTrue; eauto.
    split.
    eauto.
    split.
    intros s Hni.
    etransitivity.
    eapply Hbvs.
    eauto.
    eapply Hlvs.
    simpl in *; eauto.
    split.
    eapply new_adt_no_pollute_seq; eauto.
    solve [rewrite diff_submap_cancel; eauto].
    eapply related_Equal; pick_related; eauto.
    solve [rewrite diff_submap_cancel; eauto].

    exfalso; eapply is_true_is_false; eauto.
    eapply wneb_is_true; eauto.
    eapply is_false_is_bool; eauto.

    (* skip *)
    exists s_st.
    split.
    eapply RunsToSkip.
    split.
    solve [eapply diff_submap; eauto].
    split.
    eauto.
    split.
    solve [intros; openhyp; intuition].
    eapply related_Equal; pick_related; eauto.
    solve [rewrite diff_submap_cancel; eauto].

    Lemma safe_while_is_bool (env : Env ADTValue) e s st : Safe env (While e s) st -> is_bool st e.
    Proof.
      intros H.
      inversion H; unfold_all; subst.
      eapply is_true_is_bool; eauto.
      eapply is_false_is_bool; eauto.
    Qed.

    (* while-false *)
    subst.
    rename H0 into Hcomp.
    inject Hcomp.
    exists s_st.
    split.
    eapply RunsToWhileFalse.
    eapply wneb_is_false; eauto.
    solve [eapply safe_while_is_bool; eauto].
    split.
    solve [eapply diff_submap; eauto].
    split.
    eauto.
    split.
    solve [intros; openhyp; intuition].
    eapply related_Equal; pick_related; eauto.
    solve [rewrite diff_submap_cancel; eauto].

    Lemma is_mapsto_adt_eq_sca x w st : is_mapsto_adt x (StringMap.add x (SCA ADTValue w) st) = false.
    Proof.
      unfold is_mapsto_adt.
      rewrite StringMapFacts.add_eq_o in * by eauto.
      eauto.
    Qed.

    Lemma is_mapsto_adt_neq x (v : Value ADTValue) st x' : x' <> x -> is_mapsto_adt x' (StringMap.add x v st) = is_mapsto_adt x' st.
    Proof.
      unfold is_mapsto_adt; intros.
      rewrite StringMapFacts.add_neq_o in * by eauto.
      eauto.
    Qed.

    Lemma not_mapsto_adt_find x st v : not_mapsto_adt x st = true -> StringMap.find x st = Some v -> exists w, v = SCA ADTValue w.
    Proof.
      intros Hnmt Hfx.
      unfold not_mapsto_adt in *.
      unfold is_mapsto_adt in *.
      rewrite Hfx in Hnmt; simpl in *.
      destruct v as [w | a]; simpl in *.
      eauto.
      discriminate.
    Qed.

    Lemma related_add_sca st vs h lhs w h' : related st (vs, h) -> not_mapsto_adt lhs st = true -> h' == h -> related (StringMap.add lhs (SCA _ w) st) (Locals.upd vs lhs w, h').
    Proof.
      intros Hr Hnmt Hheq.
      unfold related; simpl in *.
      split.
      intros x v Hfx.
      destruct (string_dec x lhs) as [Heq | Hne].
      subst.
      rewrite StringMapFacts.add_eq_o in * by eauto.
      inject Hfx; simpl in *.
      rewrite Locals.sel_upd_eq in * by eauto.
      eauto.
      rewrite StringMapFacts.add_neq_o in * by eauto.
      rewrite Locals.sel_upd_ne in * by eauto.
      eapply Hr in Hfx; simpl in *.
      solve [rewrite Hheq; eauto].
      
      intros p a Hfp.
      rewrite Hheq in Hfp.
      eapply Hr in Hfp.
      simpl in *.
      destruct Hfp as [x [[Hvs Hfx] Hu]].
      subst.
      destruct (string_dec x lhs) as [Heq | Hne].
      subst.
      eapply not_mapsto_adt_find in Hfx; eauto.
      openhyp; discriminate.
      exists x.
      split.
      rewrite Locals.sel_upd_ne in * by eauto.
      rewrite StringMapFacts.add_neq_o in * by eauto.
      eauto.
      intros x' [Hvs Hfx'].
      destruct (string_dec x' lhs) as [Heq' | Hne'].
      subst.
      rewrite StringMapFacts.add_eq_o in * by eauto.
      discriminate.
      rewrite Locals.sel_upd_ne in * by eauto.
      rewrite StringMapFacts.add_neq_o in * by eauto.
      eauto.
    Qed.

    Lemma new_adt_no_pollute_add_sca st vs lhs w1 w2 h : new_adt_no_pollute st vs (StringMap.add lhs (SCA _ w1) st) (Locals.upd vs lhs w2) h.
    Proof.
      unfold new_adt_no_pollute.
      intros x Hmt Hmt'.
      destruct (string_dec x lhs) as [Heq | Hne].
      subst.
      rewrite Locals.sel_upd_eq in * by eauto.
      rewrite is_mapsto_adt_eq_sca in *.
      discriminate.
      rewrite Locals.sel_upd_ne in * by eauto.
      rewrite is_mapsto_adt_neq in * by eauto.
      solve [intros; openhyp; intuition].
    Qed.

    (* label *)
    subst.
    rename H0 into Hcomp.
    inject Hcomp.
    rename s into lhs.
    rename g into lbl.
    destruct v as [vs h]; simpl in *.
    rename h1 into h2.
    rename H1 into Hsm.
    rename H4 into Hsf.
    rename H2 into Hr.
    rename H into Hlbl.
    inversion Hsf as [ | | | | | | | ? ? ? w' Hlbl' Hnmt | | ]; unfold_all; subst.
    unif w'.
    eexists.
    split.
    eapply RunsToLabel; eauto.
    split.
    solve [eapply diff_submap; eauto].
    split.
    intros x Hni.
    eapply singleton_iff_not in Hni.
    solve [rewrite Locals.sel_upd_ne; eauto].
    split.
    solve [eapply new_adt_no_pollute_add_sca].
    eapply related_add_sca; eauto.
    solve [rewrite diff_submap_cancel; eauto].

    (* assign *)
    subst.
    unfold_all.
    rename H into Hcomp.
    inject Hcomp.
    rename s into lhs.
    rename e0 into e.
    destruct v as [vs h]; simpl in *.
    rename h1 into h2.
    rename H0 into Hsm.
    rename H3 into Hsf.
    rename H1 into Hr.
    inversion Hsf as [ | | | | | | ? ? ? w He Hnmt | | | ]; unfold_all; subst.
    eexists.
    split.
    eapply RunsToAssign; eauto.
    split.
    solve [eapply diff_submap; eauto].
    split.
    intros x Hni.
    eapply singleton_iff_not in Hni.
    solve [rewrite Locals.sel_upd_ne; eauto].
    split.
    solve [eapply new_adt_no_pollute_add_sca].
    eapply eval_ceval in He; eauto.
    rewrite He in *.
    eapply related_add_sca; eauto.
    solve [rewrite diff_submap_cancel; eauto].
  Qed.

End Make.