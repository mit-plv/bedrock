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
  Require Import GeneralTactics4.
  Require Import FacadeFacts.

  Notation ceval := SemanticsExpr.eval.
  Notation cRunsTo := Semantics.RunsTo.
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

  Require Import GeneralTactics2.
  Hint Extern 0 (_ == _) => reflexivity.

  Ltac subst' H := rewrite H in *; clear H.

  Ltac openhyp' := 
    repeat match goal with
             | H : _ /\ _ |- _  => destruct H
             | H : _ \/ _ |- _ => destruct H
             | H : exists x, _ |- _ => destruct H
             | H : exists ! x, _ |- _ => destruct H
             | H : unique _ _ |- _ => destruct H
           end.

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

  Require Import Option.

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
    Import WordMapFacts.
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

    Ltac pick_related := try match goal with | |- related _ _ => eauto end.

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