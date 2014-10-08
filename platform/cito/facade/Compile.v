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

  Definition compile_ax (spec : AxiomaticSpec) : Cito.Callee :=
    Semantics.Foreign 
      {|
        Semantics.PreCond args := PreCond spec (List.map CitoIn_FacadeIn args) ;
        Semantics.PostCond pairs ret := PostCond spec (List.map CitoInOut_FacadeInOut pairs) (CitoIn_FacadeIn ret)
      |}.

  Definition compile_op (spec : OperationalSpec) : Cito.Callee.
    refine
      (Cito.Internal
         {|
           Semantics.Fun :=
             {|
               FuncCore.ArgVars := ArgVars spec;
               FuncCore.RetVar := RetVar spec;
               FuncCore.Body := compile (Body spec)
             |};
           Semantics.NoDupArgVars := _
         |}
      ).
    simpl.
    destruct spec.
    simpl.
    inversion NoDupArgVars.
    eauto.
  Defined.

  Definition FuncSpec := @FuncSpec ADTValue.

  Definition compile_spec (spec : FuncSpec) : Cito.Callee :=
    match spec with
      | Axiomatic s => compile_ax s
      | Operational s => compile_op s
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

  Require Import StringSet.

  Require Import WordMapFacts.
  Import FMapNotations.
  Open Scope fmap.
  Require Import WordMap.
  Import WordMap.

  Definition Submap {elt} m1 m2 := forall {k v}, @find elt k m1 = Some v -> find k m2 = Some v.
  Infix "<=" := Submap.

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
                (forall x, ~ StringSet.In x (assigned s) -> Locals.sel (fst t_st) x = Locals.sel (fst t_st') x) /\
                (* newly allocated ADT objects during this program's execution won't collide with the frame heap *)
                (forall x a, ~ StringMap.In x s_st -> StringMap.find x s_st' = Some (ADT a) -> ~ WordMap.In (Locals.sel (fst t_st') x) h2) /\
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
    Ltac copy h := generalize h; intro.
    copy H; eapply H16 in H.
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
    eauto.
    reflexivity.
    Unfocus.
    Require Import List.
    Fixpoint reachable_heap vs argvars (input : list Value) := 
      match argvars, input with
        | k :: ks, i :: is =>
          let h := reachable_heap vs ks is in
          match i with
            | SCA _ => h 
            | ADT a => WordMap.add (Locals.sel vs k) a h
          end
        | _, _ => WordMap.empty _
      end.

    instantiate (1 := reachable_heap (fst v) l input).
    Lemma reachable_submap_related : forall st args input vs h, mapM (sel st) args = Some input -> related st (vs, h) -> reachable_heap vs args input <= h /\ related (make_state args input) (vs, reachable_heap vs args input).
      admit.
    Qed.
    eapply reachable_submap_related in H4; openhyp; eauto.
    Lemma submap_trans : forall elt (a b c : WordMap.t elt), a <= b -> b <= c -> a <= c.
      admit.
    Qed.
    eapply submap_trans; eauto.
    eapply reachable_submap_related in H4; openhyp; eauto.
    Lemma change_var_names : forall vs1 vs2 h vars1 vars2 input, related (make_state vars1 input) (vs1, h) -> (map (Locals.sel vs2) vars2 = map (fun x => vs1 x) vars1) -> related (make_state vars2 input) (vs2, h).
      admit.
    Qed.
    eapply change_var_names; eauto.
    rewrite map_map in H0; simpl in *; eauto.
    Ltac split' name :=
      match goal with
        | |- ?T /\ _ => assert (name: T); [ | split; [ auto | ] ]
      end.

    split' Hsm.
    eapply submap_trans; eauto.
    Lemma submap_diff : forall elt (a b c : WordMap.t elt), c <= b -> b <= a -> a - b <= a - c.
      admit.
    Qed.
    eapply submap_diff; eauto.
    eapply reachable_submap_related in H4; openhyp; eauto.

    split.
    intros.
    Require Import GeneralTactics2.
    Lemma singleton_iff_not : forall e e', ~ StringSet.In e' (StringSet.singleton e) <-> e <> e'.
      split; intros; not_not; eapply StringSetFacts.singleton_iff; eauto.
    Qed.
    eapply singleton_iff_not in H19.
    rewrite Locals.sel_upd_ne by eauto.
    eauto.

    Import WordMap.

    split.
    intros.
    destruct (string_dec x1 s).
    subst.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    inject H20.
    rewrite Locals.sel_upd_eq by eauto.
    Lemma submap_in : forall elt h1 h2, h1 <= h2 -> forall k, @In elt k h1 -> In k h2.
      admit.
    Qed.
    Lemma submap_not_in : forall elt h1 h2, h1 <= h2 -> forall k, ~ @In elt k h2 -> ~ In k h1.
      intros; not_not; eapply submap_in; eauto.
    Qed.
    eapply submap_not_in.
    2 : eapply H9.
    eapply submap_diff; eauto.
    eapply reachable_submap_related in H4; openhyp; eauto.
    Lemma make_state_not_in : forall k ks (vs : list Value), ~ List.In k ks -> ~ StringMap.In k (make_state ks vs).
      admit.
    Qed.
    eapply make_state_not_in.
    Require Import ListFacts1 ListFacts2 ListFacts3 ListFactsNew.
    Import WordMapFacts.
    Lemma NoDup_not_in : forall A (x : A) xs, NoDup (x :: xs) -> ~ List.In x xs.
      inversion 1; subst; eauto.
    Qed.
    eapply NoDup_not_in.
    destruct spec; eauto.
    eauto.

    rewrite StringMapFacts.add_neq_o in * by eauto.
    rewrite Locals.sel_upd_ne by eauto.
    nintro; eapply H19; clear H19.
    Definition not_reachable key (k : key) ks ins := forall i, nth_error ks i = Some k -> exists w, nth_error ins i = Some (Sca w).

    Lemma find_Some_add_remove_many : 
      forall k ks ins outs h v, 
        NoDup ks -> 
        length ks = length ins -> 
        length ks = length outs -> 
        (StringMap.find k (add_remove_many ks ins outs h) = Some v <-> 
         ((not_reachable k ks ins /\ StringMap.find k h = Some v) \/ 
          exists i a, 
            nth_error ks i = Some k /\ 
            nth_error ins i = Some (ADT a) /\ 
            nth_error outs i = Some (Some v))).
      admit.
    Qed.
    Lemma In_add_remove_many : 
      forall k ks (ins : list Value) outs h, 
        NoDup ks -> 
        mapM (sel h) ks = Some ins ->
        StringMap.In k (add_remove_many ks ins outs h) -> 
        StringMap.In k h.
      admit.
    Qed.
    eapply In_add_remove_many; eauto.
    eapply StringMapFacts.MapsTo_In.
    eapply StringMapFacts.find_mapsto_iff.
    eauto.
    
    copy H4; eapply reachable_submap_related in H4; openhyp; eauto.
    destruct v as [vs h]; simpl in *.
    set (h2 := h - h1) in *.
    unfold related; simpl.
    split.

    (* related (1) *)
    intros k v Hf.

    eapply StringMapFacts.find_mapsto_iff in Hf.
    eapply StringMapFacts.add_mapsto_iff in Hf; openhyp.
    subst.
    rewrite Locals.sel_upd_eq by eauto.
    unfold related in H14; simpl in H14; openhyp.
    eapply H14 in H.
    set (h23 := h - reachable_heap vs l input) in *.
    set (retp := Locals.sel vs_callee' (RetVar spec)) in *.
    Lemma submap_represent : forall p h1 h2 v, represent p (WordMap.find p h1) v -> h1 <= h2 -> represent p (WordMap.find p h2) v.
      admit.
    Qed.
    eapply submap_represent.
    eauto.
    eapply submap_diff; eauto.
    eapply submap_diff; eauto.

    rewrite Locals.sel_upd_ne by eauto.
    eapply StringMapFacts.find_mapsto_iff in H22.
    eapply find_Some_add_remove_many in H22.
    openhyp.
    copy H19; unfold related in H19; simpl in H19; openhyp.
    eapply H19 in H23.
    Lemma not_in_find_submap : forall elt h1 h2 k, h2 <= h1 -> ~@WordMap.In elt k h2 -> WordMap.find k h1 = WordMap.find k (h1 - h2).
      admit.
    Qed.
    erewrite not_in_find_submap in H23.
    Focus 3.
    Lemma not_reachable_iff : forall k ks st vs h input, related st (vs, h) -> mapM (sel st) ks = Some input -> (not_reachable k ks input <-> ~ WordMap.In (Locals.sel vs k) (reachable_heap vs ks input)).
      admit.
    Qed.
    eapply not_reachable_iff; eauto.
    2 : eauto.
    eapply submap_represent.
    eauto.
    Lemma submap_diff_diff : forall elt (h1 h2 h3 : WordMap.t elt), h1 <= h2 -> h2 <= h3 -> h2 - h1 == (h3 - h1) - (h3 - h2).
      admit.
    Qed.
    Require Import Setoid.
    Global Add Parametric Morphism elt : (@Submap elt)
        with signature Equal ==> Equal ==> iff as Submap_m.
      admit.
    Qed.
    erewrite submap_diff_diff; eauto.
    Lemma submap_restrict : forall elt (h1 h2 h : WordMap.t elt), h1 <= h2 -> h1 - h <= h2 - h.
      admit.
    Qed.
    eapply submap_restrict.
    eauto.

    rewrite map_map in H0; simpl in *.
    Lemma map_nth_error_1 : forall A B (f : A -> B) ls1 ls2 i a, List.map f ls1 = ls2 -> nth_error ls1 i = Some a -> nth_error ls2 i = Some (f a).
      intros.
      rewrite <- H.
      erewrite map_nth_error; eauto.
    Qed.
    Lemma nth_error_map_elim : forall A B (f : A -> B) ls i b, nth_error (List.map f ls) i = Some b -> exists a, nth_error ls i = Some a /\ f a = b.
      intros.
      rewrite ListFacts.map_nth_error_full in H.
      destruct (option_dec (nth_error ls i)).
      destruct s; rewrite e in *; inject H; eexists; eauto.
      rewrite e in *; discriminate.
    Qed.
    Lemma map_eq_nth_error_1 : forall A1 A2 B (f1 : A1 -> B) (f2 : A2 -> B) ls1 ls2 i a1, List.map f1 ls1 = List.map f2 ls2 -> nth_error ls1 i = Some a1 -> exists a2, nth_error ls2 i = Some a2 /\ f1 a1 = f2 a2.
      intros.
      eapply map_nth_error_1 in H; eauto.
      eapply nth_error_map_elim in H; openhyp.
      eexists; eauto.
    Qed.
    symmetry in H0.
    eapply map_eq_nth_error_1 in H0; [ | eauto ..].
    openhyp.
    unfold Locals.sel in *.
    rewrite H25.
    rewrite H5.
    Focus 2.
    Lemma disjoint_in_not : forall s1 s2 x, disjoint s1 s2 -> StringSet.In x s2 -> ~ StringSet.In x s1.
      admit.
    Qed.
    eapply disjoint_in_not; eauto.
    eapply StringSetFacts.of_list_1.
    eapply SetoidListFacts.In_InA.
    eapply Locals.nth_error_In; eauto.
    rename x1 into i.
    rename l into args.
    erewrite map_nth_error in H24 by eauto.
    inject H24.
    copy H14; unfold related in H14; simpl in H14; eapply H14 in H26.
    unfold Locals.sel in *.
    set (h23 := h - reachable_heap vs args input) in *.
    set (p := vs_callee' x3) in *.
    eapply submap_represent.
    eauto.
    eapply submap_diff; eauto.
    eapply submap_diff; eauto.

    eauto.

    Lemma mapM_length : forall A B (f : A -> option B) ls1 ls2, mapM f ls1 = Some ls2 -> length ls1 = length ls2.
      admit.
    Qed.
    eapply mapM_length; eauto.
    rewrite map_length.
    rewrite map_map in H0.
    eapply map_eq_length_eq in H0.
    eauto.

    (* related (2) *)
    intros.
    rename s into lhs.
    rename l into args.
    rename h into h123.
    rename h1 into h23.
    rename h2 into h1.
    set (h3 := reachable_heap vs args input) in *.
    set (h12 := h123 - h3) in *.
    set (h2 := h12 - h1) in *.
    set (h3' := heap' - h12) in *.
    set (h23' := heap' - h1) in *.
    Notation direct_sum h1 h2 h12 := (h1 <= h12 /\ h2 <= h12 /\ Disjoint h1 h2).
    Notation "h1 * h2 === h12" := (direct_sum h1 h2 h12) (at level 100).
    assert (direct_sum h1 h2 h12) by admit.
    assert (direct_sum h2 h3 h23) by admit.
    assert (direct_sum h1 h23 h123) by admit.
    assert (direct_sum h12 h3 h123) by admit.
    assert (direct_sum h2 h3' h23') by admit.

    Lemma find_Some_direct_sum : forall elt h1 h2 h12, direct_sum h1 h2 h12 -> forall k (v : elt), find k h12 = Some v <-> find k h1 = Some v \/ find k h2 = Some v.
      admit.
    Qed.

    eapply find_Some_direct_sum in H21; eauto; openhyp.

    (* p is in h2 *)
    Ltac unfold_related H := copy H; unfold related in H; simpl in H; openhyp.
    unfold_related H19.
    specialize (H38 _ _ (H23 _ _ H21)).
    Ltac openhyp' := 
      repeat match goal with
               | H : _ /\ _ |- _  => destruct H
               | H : _ \/ _ |- _ => destruct H
               | H : exists x, _ |- _ => destruct H
               | H : exists ! x, _ |- _ => destruct H
               | H : unique _ _ |- _ => destruct H
             end.
    openhyp'.
    rename x1 into x3.
    destruct (string_dec x3 lhs).
    subst.
    contradict H12; eexists; eauto.
    exists x3.
    split.
    split.
    rewrite Locals.sel_upd_ne by eauto; eauto.
    rewrite StringMapFacts.add_neq_o by eauto.
    eapply find_Some_add_remove_many.
    eauto.
    eapply mapM_length; eauto.
    rewrite map_length.
    rewrite map_map in H0.
    eapply map_eq_length_eq in H0.
    eauto.
    left.
    split.
    eapply not_reachable_iff; eauto.
    Lemma Disjoint_in_not : forall elt h1 h2 x, @Disjoint elt h1 h2 -> In x h1 -> ~ In x h2.
      admit.
    Qed.
    eapply (Disjoint_in_not H34).
    rewrite H38.
    Lemma find_Some_in : forall elt k m (v : elt), find k m = Some v -> In k m.
      intros; eapply MapsTo_In; eapply find_mapsto_iff; eauto.
    Qed.
    eapply find_Some_in; eauto.
    eauto.

    intros.
    openhyp.
    destruct (string_dec x' lhs).
    subst.
    rewrite StringMapFacts.add_eq_o in *.
    rewrite Locals.sel_upd_eq in * by eauto.
    inject H42.
    eapply H9 in H.
    contradict H.
    rewrite H41.
    eapply submap_in; eauto.
    eapply find_Some_in; eauto.
    eapply make_state_not_in.
    eapply NoDup_not_in.
    destruct spec; eauto.
    eauto.

    rewrite StringMapFacts.add_neq_o in * by eauto.
    rewrite Locals.sel_upd_ne in * by eauto.
    eapply H39.
    split.
    eauto.
    Lemma not_reachable_add_remove_many : 
      forall k ks ins outs h, 
        NoDup ks -> 
        length ks = length ins -> 
        length ks = length outs -> 
        not_reachable k ks ins -> 
        StringMap.find k (add_remove_many ks ins outs h) = StringMap.find k h.
      admit.
    Qed.
    erewrite <- not_reachable_add_remove_many; eauto.
    solve [eapply mapM_length; eauto].
    rewrite map_length.
    rewrite map_map in H0.
    solve [eapply map_eq_length_eq in H0; eauto].
    eapply not_reachable_iff; eauto.
    eapply (Disjoint_in_not H34).
    rewrite H41.
    solve [eapply find_Some_in; eauto].

    
    (* p is in h3' *)
    unfold_related H14.
    copy H21; eapply H38 in H21.
    do 2 destruct H21.
    openhyp.
    rename x1 into x3.
    copy H41; eapply H18 in H41.
    openhyp.

    (* x3 is RetVar (i.e. p is the address of the returned ADT object) *)
    subst.
    unfold sel in *; rewrite H42 in H.
    inject H.
    exists lhs.
    split.
    (* exists *)
    split.
    rewrite Locals.sel_upd_eq by eauto.
    eauto.
    rewrite StringMapFacts.add_eq_o by eauto.
    eauto.

    (* unique *)
    intros.
    openhyp.
    destruct (string_dec x' lhs).
    eauto.
    set (p := Locals.sel vs_callee' (RetVar spec)) in *.
    rewrite Locals.sel_upd_ne in * by eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    eapply find_Some_add_remove_many in H21.
    openhyp.
    (* not_reachable *)
    unfold_related H19.
    eapply H19 in H41; simpl in *.
    eapply find_Some_direct_sum in H41; eauto; openhyp.
    rewrite H in *.
    eapply find_Some_in in H41.
    eapply find_Some_in in H39.
    contradict H39.
    eapply (Disjoint_in_not H28); eauto.
    eapply not_reachable_iff in H21; eauto.
    contradict H21.
    solve [eapply find_Some_in; eauto].
    (* reachable *)
    rewrite map_map in H0; simpl in *.
    symmetry in H0.
    eapply map_eq_nth_error_1 in H0; [ | eauto ..].
    openhyp.
    unfold Locals.sel in *.
    erewrite map_nth_error in H43 by eauto.
    inject H43.
    assert (RetVar spec = x2).
    eapply H40.
    split.
    rewrite <- H.
    rewrite H44.
    symmetry; eapply H5.
    eapply disjoint_in_not; eauto.
    eapply StringSetFacts.of_list_1.
    eapply SetoidListFacts.In_InA.
    eapply Locals.nth_error_In; eauto.
    solve [eauto].
    rewrite <- H43 in *.
    eapply Locals.nth_error_In in H0; eauto.
    contradict H0.
    eapply NoDup_not_in.
    destruct spec; eauto.
    eauto.
    eapply mapM_length; eauto.
    rewrite map_length.
    rewrite map_map in H0.
    solve [eapply map_eq_length_eq in H0; eauto].

    (* x3 is an arg referring to an ADT object (i.e. p is the address of an output ADT object, not the returned ADT object) *)
    rewrite map_map in H0; simpl in *.
    Ltac copy_as h h' := generalize h; intro h'.
    copy_as H0 H00; eapply map_eq_nth_error_1 in H0; [ | eauto ..].
    openhyp.
    rename x1 into i.
    rename x4 into arg.
    destruct (string_dec arg lhs).
    subst.
    contradict H12.
    Lemma mapM_nth_error_2 : forall A B (f : A -> option B) ls1 ls2 i a2, mapM f ls1 = Some ls2 -> nth_error ls2 i = Some a2 -> exists a1, nth_error ls1 i = Some a1 /\ f a1 = Some a2.
      admit.
    Qed.
    eapply mapM_nth_error_2 in H11; [ | eauto].
    openhyp.
    unfold StringMap.key in *.
    rewrite H0 in H11.
    inject H11.
    eexists; eauto.
   
    exists arg.
    split.
    (* exists *)
    rewrite Locals.sel_upd_ne by eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    unfold Locals.sel in *.
    split.
    subst.
    rewrite <- H44.
    eapply H5.
    eapply disjoint_in_not; eauto.
    eapply StringSetFacts.of_list_1.
    eapply SetoidListFacts.In_InA.
    eapply Locals.nth_error_In; eauto.

    eapply find_Some_add_remove_many.
    eauto.
    eapply mapM_length; eauto.
    rewrite map_length.
    eapply map_eq_length_eq in H00; eauto.
    right.
    exists i.
    eexists.
    split.
    eauto.
    split.
    eauto.
    erewrite map_nth_error by eauto.
    f_equal.
    eauto.

    (* unique *)
    intros.
    openhyp.
    destruct (string_dec x' lhs).
    subst.
    set (retp := Locals.sel vs_callee' (RetVar spec)) in *.
    set (p := Locals.sel vs_callee' x3) in *.
    rewrite Locals.sel_upd_eq in * by eauto.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    inject H46.
    assert (x3 = RetVar spec).
    eapply H40.
    split.
    eauto.
    eauto.
    rewrite H21 in *.
    eapply Locals.nth_error_In in H41; eauto.
    contradict H41.
    eapply NoDup_not_in.
    destruct spec; eauto.

    set (retp := Locals.sel vs_callee' (RetVar spec)) in *.
    rewrite Locals.sel_upd_ne in * by eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    eapply find_Some_add_remove_many in H46.
    openhyp.
    (* not_reachable *)
    unfold_related H19.
    eapply H19 in H47.
    unfold represent in H47.
    eapply find_Some_direct_sum in H47; eauto; openhyp.
    rewrite H45 in *.
    eapply find_Some_in in H47.
    eapply find_Some_in in H39.
    contradict H39.
    eapply (Disjoint_in_not H28); eauto.
    eapply not_reachable_iff in H46; eauto.
    contradict H46.
    solve [eapply find_Some_in; eauto].
    (* reachable *)
    rename x1 into i'.
    symmetry in H00.
    eapply map_eq_nth_error_1 in H00; [ | eauto ..].
    openhyp.
    unfold Locals.sel in *.
    erewrite map_nth_error in H48 by eauto.
    inject H48.
    assert (x3 = x1).
    eapply H40.
    split.
    rewrite <- H45.
    rewrite H50.
    symmetry; eapply H5.
    eapply disjoint_in_not; eauto.
    eapply StringSetFacts.of_list_1.
    eapply SetoidListFacts.In_InA.
    eapply Locals.nth_error_In; eauto.
    eauto.
    rewrite <- H21 in *.
    Lemma NoDup_nth_error : forall {A ls i i'} (x : A), nth_error ls i = Some x -> nth_error ls i' = Some x -> NoDup ls -> i = i'.
      admit.
    Qed.
    assert (i = i').
    eapply (NoDup_nth_error H41); eauto.
    Lemma NoDup_ArgVars : forall spec, NoDup (ArgVars spec).
      intros; destruct spec; simpl.
      inversion NoDupArgVars; eauto.
    Qed.
    eapply NoDup_ArgVars; eauto.
    rewrite <- H48 in *.
    unfold StringMap.key in *.
    rewrite H0 in H46.
    inject H46.
    eauto.
    eauto.
    eapply mapM_length; eauto.
    rewrite map_length.
    eapply map_eq_length_eq in H00; eauto.

    Lemma submap_find : forall elt k (v : elt) m1 m2, m1 <= m2 -> find k m1 = Some v -> find k m2 = Some v.
      unfold Submap; eauto.
    Qed.

    Ltac subst' H := rewrite H in *; clear H.

    (* unify and get rid of b *)
    Ltac unif b :=
      match goal with
        | H1 : ?L = Some _, H2 : ?L = Some b |- _ => rewrite H1 in H2; symmetry in H2; inject H2
      end.

    Lemma combine_length_eq : forall A B (ls1 : list A) (ls2 : list B), length ls1 = length ls2 -> length (combine ls1 ls2) = length ls1.
      admit.
    Qed.
    Lemma nth_error_combine : forall A B ls1 ls2 (a : A) (b : B) i, nth_error ls1 i = Some a -> nth_error ls2 i = Some b -> nth_error (combine ls1 ls2) i = Some (a, b).
      admit.
    Qed.
    Lemma nth_error_combine_elim : forall A B ls1 ls2 (a : A) (b : B) i, nth_error (combine ls1 ls2) i = Some (a, b) -> nth_error ls1 i = Some a /\ nth_error ls2 i = Some b.
      admit.
    Qed.
    Lemma mapM_nth_error_1 : forall A B (f : A -> option B) ls1 ls2 i a, mapM f ls1 = Some ls2 -> nth_error ls1 i = Some a -> exists b, nth_error ls2 i = Some b /\ f a = Some b.
      admit.
    Qed.
    Lemma map_nth_error_2 : forall A B (f : A -> B) ls1 ls2 i b, List.map f ls1 = ls2 -> nth_error ls2 i = Some b -> exists a, nth_error ls1 i = Some a /\ f a = b.
      admit.
    Qed.

    Lemma in_nth_error A ls (a : A) : List.In a ls -> exists i, nth_error ls i = Some a.
      admit.
    Qed.
    Lemma nth_error_nil A i : nth_error (@nil A) i = None.
      admit.
    Qed.
    Lemma incl_nth_error A ls1 ls2 i (a : A) : List.incl ls1 ls2 -> nth_error ls1 i = Some a -> exists i', nth_error ls2 i' = Some a.
      admit.
    Qed.
    Lemma combine_map A B C (f1 : A -> B) (f2 : A -> C) ls : combine (List.map f1 ls) (List.map f2 ls) = List.map (fun x => (f1 x, f2 x)) ls.
      admit.
    Qed.

    Import Semantics.

    Fixpoint make_triples pairs (outs : list (ArgOut ADTValue)) :=
      match pairs, outs with
        | p :: ps, o :: os => {| Word := fst p; ADTIn := snd p; ADTOut := o |} :: make_triples ps os
        | _, _ => nil
      end.
    Lemma split_triples : forall triples words_cinput coutput, words_cinput = List.map (fun x => (Word x, ADTIn x)) triples -> coutput = List.map (@ADTOut _) triples -> triples = make_triples words_cinput coutput.
      admit.
    Qed.
    Lemma split_triples' : forall triples words cinput coutput, words = List.map (@Word _) triples -> cinput = List.map (@ADTIn _) triples -> coutput = List.map (@ADTOut _) triples -> triples = make_triples (combine words cinput) coutput.
      admit.
    Qed.
    Lemma nth_error_make_triples_intro words_cinput coutput i p a a' : nth_error words_cinput i = Some (p, a) -> nth_error coutput i = Some a' -> nth_error (make_triples words_cinput coutput) i = Some {| Word := p; ADTIn := a; ADTOut := a'|}.
      admit.
    Qed.
    Lemma nth_error_make_triples_elim wis os i p a a' : nth_error (make_triples wis os) i = Some {| Word := p; ADTIn := a; ADTOut := a' |} -> nth_error wis i = Some (p, a) /\ nth_error os i = Some a'.
      admit.
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

    Focus 7.
    (* call-axiomatic *)
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
    rewrite combine_map; destruct H1; eauto.
    repeat rewrite map_length; eauto.
    eapply H14; eauto.
    repeat rewrite map_length; eauto.
    eapply mapM_length in H15; eauto.
    eapply map_eq_length_eq in H0; eauto; rewrite <- H0.
    eauto.

    rewrite H in *.

    eexists.
    split.
    eapply RunsToCallAx.
    eauto.
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

    Definition no_alias (words_cinput : list (W * ArgIn ADTValue)) := forall i j p (ai aj : ADTValue), nth_error words_cinput i = Some (p, inr ai) -> nth_error words_cinput j = Some (p, inr aj) -> i = j.

    assert (words_cinput = combine words cinput) by (unfold_all; rewrite combine_map; eauto).

    assert (no_alias words_cinput).

    Lemma related_no_alias : forall st vs h x1 a1 x2 a2, related st (vs, h) -> StringMap.find x1 st = Some (ADT a1) -> StringMap.find x2 st = Some (ADT a2) -> Locals.sel vs x1 = Locals.sel vs x2 -> x1 = x2.
    Proof.
      intros.
      unfold_related H.
      copy H0; eapply H in H0; simpl in *.
      copy H1; eapply H in H1; simpl in *.
      rewrite H2 in *.
      rewrite H0 in H1; inject H1.
      eapply H4 in H0; openhyp'.
      assert (x = x1) by (eapply H1; eauto).
      assert (x = x2) by (eapply H1; eauto).
      eauto.
    Qed.

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

    Lemma Disjoint_diff elt m1 m2 : @Disjoint elt (m1 - m2) m2.
    Proof.
      unfold Disjoint.
      intros k.
      nintro.
      openhyp.
      eapply diff_in_iff in H.
      openhyp; intuition.
    Qed.

    Lemma diff_submap elt (m1 m2 : t elt) : m1 - m2 <= m1.
    Proof.
      unfold Submap.
      intros k v Hf.
      eapply diff_find_Some_iff in Hf; openhyp; eauto.
    Qed.

    set (h1 := h123 - h23) in *.
    assert (direct_sum h1 h23 h123).
    split.
    eapply diff_submap.
    split.
    eauto.
    eapply Disjoint_diff.

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
    eapply singleton_iff_not in H19.
    rewrite Locals.sel_upd_ne by eauto.
    solve [eauto].

    split.
    (* newly allocated objects won't sabotage frame heap *)
    intros.
    destruct (string_dec x lhs).
    (* x = lhs *)
    rewrite e in *.
    rewrite Locals.sel_upd_eq by eauto.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    destruct ret; simpl in *.
    discriminate.
    inject H20.
    unfold separated in H4; simpl in *.
    openhyp.
    discriminate.
    solve [eapply submap_not_in; eauto].
    (* x <> lhs *)
    rewrite Locals.sel_upd_ne by eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    contradict H19.
    eapply In_add_remove_many; eauto.
    eapply StringMapFacts.MapsTo_In.
    solve [eapply StringMapFacts.find_mapsto_iff; eauto].

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
      assert (Hd : Disjoint h1 h2) by eapply Disjoint_diff.
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
    eapply H8 in H22; simpl in *.
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
    contradict H23.
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
    Hint Extern 0 (_ == _) => reflexivity.
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
    rewrite H5 in H19.

    destruct (p_addr_ret_dec p addr ret).

    (* p is the address of the return ADT object *)
    destruct s; openhyp.
    subst; simpl in *.
    eapply diff_find_Some_iff in H19; openhyp.
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
    eapply add_remove_many_fold_store_out in H20; eauto.
    eapply diff_find_Some_iff in H20; openhyp.
    solve [eapply find_Some_in; eauto].

    (* p is not the address of the return ADT object *)
    rewrite find_ret_doesn't_matter in H19 by eauto.
    eapply add_remove_many_fold_store_out_iff in H19; eauto.
    2 : solve [rewrite H; eauto].
    rewrite H in H19.
    openhyp.
    destruct (string_dec x lhs).
    subst.
    contradict H17.
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
    inject H24.
    solve [unfold ret_doesn't_matter in *; simpl in *; openhyp; intuition].
    rewrite StringMapFacts.add_neq_o in * by eauto.
    rewrite Locals.sel_upd_ne in * by eauto.
    eapply find_ADT_add_remove_many in H22; eauto; openhyp.
    eapply find_ADT_add_remove_many in H24; eauto; openhyp.
    solve [eapply related_no_alias; eauto].
    solve [unfold_all; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
    solve [unfold_all; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].

    (* skip *)
    (* here *)
    eexists; split.
    eapply RunsToSkip.
    eauto.

    (* seq *)
    subst.
    inject H1.
    edestruct IHRunsTo1; clear IHRunsTo1; eauto.
    Lemma safe_seq_1 : forall (env : Env) a b st, Safe env (Seq a b) st -> Safe env a st.
    Proof.
      intros.
      inversion H; subst.
      openhyp.
      eauto.
    Qed.
    eapply safe_seq_1; eauto.
    openhyp.
    edestruct IHRunsTo2; clear IHRunsTo2; eauto.
    Lemma safe_seq_2 : forall (env : Env) a b st, Safe env (Seq a b) st -> forall st', RunsTo env a st st' -> Safe env b st'.
    Proof.
      intros.
      inversion H; subst.
      openhyp.
      eauto.
    Qed.
    eapply safe_seq_2; eauto.
    openhyp.
    eexists.
    split.
    eapply RunsToSeq; eauto.
    eauto.

    (* if-true *)
    injection H1; intros; subst; clear H1.
    edestruct IHRunsTo.
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
    eauto.

    (* if-false *)
    injection H1; intros; subst; clear H1.
    edestruct IHRunsTo.
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
    eauto.


    (* while-true *)
    admit.
    (* while-false *)
    admit.

    (* label *)
    admit.

    (* assign *)
    admit.

  Qed.

End Make.