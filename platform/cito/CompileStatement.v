Set Implicit Arguments.

Require Import DepthExpr.

Local Notation edepth := DepthExpr.depth.

Local Notation "fs ~:~ v1 ~~ s ~~> v2" := (RunsToRelax fs s v1 v2) (no associativity, at level 60).

Definition starD (f : W -> ADTValue -> HProp) (d : Heap) := MHeap.MSet.starS (fun p => f p (MHeap.sel d p)) (MHeap.keys d).

Section LayoutSection.

Variable layout : ADTValue -> W -> HProp.

Definition is_heap (heap : Heap) : HProp := starD (fun w adt_value => layout adt_value w) heap.

Definition is_return (ret : RetType) : HProp :=
  match snd ret with
    | None => ([| True |])%Sep
    | Some adt_value => layout adt_value (fst ret)
  end.

Require Import AutoSep Wrap Arith.
Require Import ExprLemmas.
Require Import VariableLemmas.
Require Import GeneralTactics.
Require Import SyntaxExpr SemanticsExpr.
Require Import Syntax Semantics.
Require Import SyntaxNotations.
Require Import RunsToRelax.
Require Import Footprint Depth.
Require Import DefineStructured.
Require Import Safety.
Require Import Malloc.

Definition S_RESERVED := "!reserved".

<<<<<<< local
Definition funcsOk (stn : settings) (fs : W -> option Callee) : PropX W (settings * state) := 
(
  (Al i : W, Al fspec, [| fs i = Some (Foreign fspec) |]
    ---> (i, stn) @@@ (st ~> ExX, Ex vs, Ex a, Ex args, Ex res, let narg := length args in
      ![^[locals ("rp" :: S_RESERVED :: tempVars narg) vs res st#Sp * is_heap a * mallocHeap 0] * #0] st
      /\ [| res = wordToNat (vs S_RESERVED) /\ match_heap a (sels vs (tempVars narg)) args /\ exists args' ret, Pred fspec {| Args := args; After := args'; Ret := ret |} |]
      /\ (st#Rp, stn) @@@ (st' ~> Ex vs', Ex a', Ex args', Ex ret,
        [| st'#Sp = st#Sp |]
        /\ ![^[locals ("rp" :: S_RESERVED :: tempVars narg) vs' res st'#Sp * is_heap a' * is_return ret * mallocHeap 0] * #1] st'
        /\ [| a' = store_result a (sels vs (tempVars narg)) args' /\ Pred fspec {| Args := args; After := args'; Ret := ret |} /\ st'#Rv = fst ret |] ))) 
  /\
  (Al i : W, Al ispec, [| fs i = Some (Internal ispec) |]
=======
Lemma star_diff_ptrs : forall specs st other p1 p2, interp specs (![p1 =?>1 * p2 =?> 1 * other] st) -> p1 <> p2.
  rewrite sepFormula_eq.
  propxFo.
  subst.
  unfold smem_get_word in *.
  simpl in *.
  case_eq (smem_get p2 x3).
  intros.
  clear H6.
  case_eq (smem_get p2 x6).
  clear H9.
  intros.
  destruct H2.
  subst.
  destruct H5.
  subst.
  destruct H4.
  subst.
  Require Import Bootstrap.
  eapply disjoint_get_fwd in H2.
  eauto.
  erewrite join_Some by eassumption.
  discriminate.
  erewrite join_Some by eassumption.
  discriminate.
  intros.
  rewrite H0 in H9.
  discriminate.
  intros.
  rewrite H in H6.
  discriminate.
Qed.

Hint Resolve star_diff_ptrs.

Definition RunsToRelax fs s v v_new := 
  exists v', RunsTo fs s v v' 
    /\ changed_in (fst v') (fst v_new) (tempVars (depth s))
    /\ snd v_new = snd v'.

Local Notation "fs ~:~ v1 ~~ s ~~> v2" := (RunsToRelax fs s v1 v2) (no associativity, at level 60).

Ltac hiding tac :=
  (let P := fresh "P" in
    match goal with
      | [ H : Safe ?fs _ _ |- _ ] => set (P := Safe fs) in *
      | [ H : ?fs ~:~ _ ~~ _ ~~> _ |- _ ] => set (P := RunsToRelax fs) in *
    end;
    hiding tac;
    subst P) || tac.

Ltac rearrange_stars HEAD :=
  match goal with
    H : interp ?SPECS (![?P] ?ST) |- _ =>
      let OTHER := fresh in 
        evar (OTHER : HProp); 
        assert (interp SPECS (![HEAD * OTHER] ST));
          unfold OTHER in *; clear OTHER;
            [ hiding ltac:(step auto_ext) | .. ]
  end.

Infix "=~*>" := (ptsto32 nil) (at level 30).

Lemma array_with_size_star_diff : forall specs st other ls1 p1 ls2 p2, interp specs (![array_with_size ls1 p1 * array_with_size ls2 p2 * other] st) -> p1 <> p2.
  unfold array_with_size; intros.
  rearrange_stars ((p1 ^- $ (8)) =?> 1 * (p2 ^- $ (8)) =?> 1)%Sep; eauto.
  eapply star_diff_ptrs in H1.
  intuition.
Qed.

Hint Resolve array_with_size_star_diff.

Lemma starS_not_in : forall specs st d ptrs ls p other, interp specs (![starS (array_ptr d) ptrs * array_with_size ls p * other] st) -> ~ p %in ptrs.
  intros.
  intro.
  assert (interp specs
        (![(starS (array_ptr d) (ptrs %- p) * array_ptr d p) * array_with_size ls p * other] st)).
  set (starS (array_ptr d) ptrs) in *.
  set (starS (array_ptr d) (ptrs %- p)) in *.
  set (array_with_size ls p) in *.
  set (array_ptr d p) in *.
  step auto_ext.
  unfold h, h0, h2.
  eapply Himp_trans.
  eapply starS_del_fwd.
  eauto.
  set (starS (array_ptr d) (ptrs %- p)) in *.
  set (array_ptr d p) in *.
  sepLemma.
  clear H.
  unfold array_ptr in H1 at 2.
  set (starS (array_ptr d) (ptrs %- p)) in *.
  rearrange_stars (array_with_size (d p) p * array_with_size ls p)%Sep.
  eapply array_with_size_star_diff in H2.
  intuition.
Qed.

Lemma heap_star_not_in : forall specs st other arrs ls p, interp specs (![heap arrs * array_with_size ls p * other] st) -> ~ p %in fst arrs.
  intros; unfold arrays in *; destruct arrs; unfold heap in *; simpl in *; eapply starS_not_in; eauto.
Qed.

Ltac auto_apply :=
  match goal with
    H : _ |- _ => eapply H
  end.

Ltac open_Some := 
  match goal with
    H : Some _ = Some _ |- _ => injection H; clear H; intros
  end.

Ltac condition_solver :=  
  match goal with
    H : evalCond _ _ _ _ _ = Some ?T |- wneb _ _ = ?T => 
    unfold evalCond in *; simpl in *; open_Some; rewriter_r; f_equal
  end.

Local Notation "var <- 'new' size" := (Syntax.Malloc var size) (no associativity, at level 60).

Open Scope nat.

Hint Rewrite sum_S : arith.
Hint Resolve S_le_lt.
Hint Resolve sel_upd_firstn.
Hint Resolve firstn_S_upd.
Hint Resolve VariableLemmas.noChange.
Hint Resolve Max.le_max_l Max.le_max_r.
Hint Extern 12 => rv_solver.
Hint Extern 12 => sp_solver.
Hint Resolve le_plus_lt lt_max_l lt_max_r.
Hint Resolve plus_le.
Hint Resolve lt_le_S plus_lt.

Lemma le_max_l_trans : forall a b c, (a <= b -> a <= max b c)%nat.
  intros; eapply le_trans.
  2: eapply Max.le_max_l.
  eauto.
Qed.
Hint Resolve le_max_l_trans.

Lemma le_max_r_trans : forall a b c, (a <= c -> a <= max b c)%nat.
  intros; eapply le_trans.
  2: eapply Max.le_max_r.
  eauto.
Qed.
Hint Resolve le_max_r_trans.

Ltac max_le_solver :=
  repeat 
    match goal with
      | |- ?A <= ?A => eapply le_n
      | |- max ?A ?B <= _ => eapply Max.max_lub
      | |- ?S <= max ?A _ =>
        match A with
          context [ S ] => eapply le_max_l_trans
        end
      | |- ?S <= max _ ?B =>
        match B with
          context [ S ] => eapply le_max_r_trans
        end
    end.
Hint Extern 0 (_ <= _) => progress max_le_solver.

Ltac incl_app_solver :=
  repeat 
    match goal with
      | |- List.incl ?A ?A => eapply List.incl_refl
      | |- List.incl (?A ++ ?B) _ => eapply incl_app
      | |- List.incl (?A :: ?B) _ => eapply List.incl_cons
      | |- List.incl ?S (?A ++ _) =>
        match A with
          context [ S ] => eapply incl_appl
        end
      | |- List.incl ?S (_ ++ ?B) =>
        match B with
          context [ S ] => eapply incl_appr
        end
      | |- List.incl ?S (?A :: _) =>
        match A with
          context [ S ] => eapply (@incl_appl _ _ _ (_ :: nil))
        end
      | |- List.incl ?S (?A :: ?B) =>
        match B with
          context [ S ] => eapply (@incl_appr _ _ (_ :: nil))
        end
    end.
Hint Extern 0 (List.incl _ _) => progress incl_app_solver.

Hint Resolve in_eq In_incl.
Hint Resolve List.incl_cons incl_cons_l incl_cons_r List.incl_refl incl_nil incl_tl incl_array.
Hint Resolve incl_app incl_appl incl_appr.
Hint Resolve List.incl_tran.
Hint Resolve disjoint_trans_lr.
Hint Resolve changedVariables_upd.
Hint Resolve unchanged_in_except_disjoint unchanged_in_except_upd unchanged_in_except_shrink.
Hint Constructors or.
Hint Resolve sel_upd_eq.

Hint Constructors RunsTo.
Hint Constructors runs_loop_partially.
Hint Resolve unchanged_exprDenote.
Hint Resolve changedVariables_upd_bwd.
Hint Resolve unchanged_incl.
Hint Resolve two_merge_equiv.
Hint Resolve changed_in_upd_same.

Hint Extern 12 (unchanged_in _ _ _) => use_changed_unchanged.
Hint Extern 12 (unchanged_in _ _ _) => use_changed_unchanged'.
Hint Extern 12 (changed_in _ _ _) => use_changed_trans2.
Hint Extern 12 (changed_in _ _ _) => use_changed_incl.
Hint Extern 12 => condition_solver'.
Hint Extern 12 (unchanged_in _ _ _) => use_unchanged_in_symm.
Hint Extern 12 (changed_in _ _ _) => use_changed_in_symm.

Hint Resolve runs_loop_partially_finish.
Hint Resolve exprDenote_disjoint.
Hint Resolve RunsTo_footprint.

Hint Extern 12 (_ = _) => condition_solver.

Ltac use_unchanged_exprDenote :=
  match goal with
    |- exprDenote ?E _ = exprDenote ?E _ => eapply unchanged_exprDenote; solve [eauto]
  end.
Hint Extern 12 => use_unchanged_exprDenote.

Lemma incl_tempChunk2 : forall b n m, b + n <= m -> List.incl (tempChunk b n) (tempVars m).
  intros; eapply incl_tempChunk; eauto.
Qed.

Hint Resolve incl_tempChunk2.

Ltac auto_apply_in t :=
  match goal with
    H : _ |- _ => eapply t in H
  end.

Ltac apply_in_all t :=
  repeat match goal with
           H : _ |- _ => eapply t in H
         end.

Ltac inv_Safe :=
  match goal with
    H : Safe _ _ _ |- _ => inversion H
  end.

Ltac break_st := unfold st in *; repeat break_pair; simpl in *.

Ltac use_Safe_immune :=
  match goal with
    H : RunsTo _ _ _ _, H2 : context [RunsTo _ _ _ _ -> Safe _ _ _] |- _ => eapply H2 in H; break_st; eapply Safe_immune
  end.

Ltac change_RunsTo :=
  match goal with
    H : RunsTo _ _ (?VS1, ?ARRS) _, H2 : changed_in ?VS2 ?VS1 _ |- _ => 
      generalize H; eapply RunsTo_immune with (vs1' := (VS2, ARRS)) in H; intros
  end.

Definition equiv (a b : arrays) := fst a %= fst b /\ forall e, e %in fst a -> snd a e = snd b e.

Infix "%%=" := equiv (at level 70, no associativity).

Lemma disjoint_cons : forall A a (e : A) b, ~In e a -> disjoint a b -> disjoint a (e :: b).
  unfold disj; intros; simpl; intuition; eauto.
Qed.

Lemma disjoint_disj : forall A (a : list A) b, disjoint a b -> disj a b.
  unfold disj, disj; eauto.
Qed.

Lemma changed_trans_l : forall vs1 vs2 vs3 a c, 
  changedVariables vs1 vs2 a -> 
  changedVariables vs2 vs3 c ->
  List.incl a c ->
  changedVariables vs1 vs3 c.
  eauto.
Qed.

Lemma del_not_in : forall s e, ~ e %in s %- e.
  unfold mem, del; intros; intuition.
Qed.

Ltac is_reg t r :=
  match t with
    | _ # r => idtac
    | Regs _ r => idtac
  end.

Ltac sp_solver' := 
  match goal with
    |- ?A = ?B => is_reg A Sp; is_reg B Sp; pattern_r; rewriter_r
  end.

Hint Extern 12 => sp_solver'.

Ltac use_disjoint_trans :=
  match goal with
    H : disjoint ?A ?B |- disjoint ?C _ =>
      match A with context [ C ] =>
        eapply (@disjoint_trans_lr _ A B C _ H); [ | eapply List.incl_refl ]
      end 
  end.

Hint Resolve del_not_in.
Hint Resolve temp_in_array.
Hint Resolve temps_not_in_array.
Hint Resolve true_false_contradict.

Ltac to_tempOf :=
  replace "!." with (tempOf 1) in * by eauto;
    replace "." with (tempOf 0) in * by eauto.

Lemma del_add : forall s e, e %in s -> s %- e %+ e %= s.
  clear; intros.
  set (s %- e).
  eapply WMake.equiv_symm.
  eapply del_to_add.
  eauto.
  unfold s0; eauto.
Qed.

Hint Resolve le_n_S.

Ltac use_disjoint_trans' :=
  match goal with
    H : disjoint ?A ?B |- disjoint ?C _ =>
      match A with context [ C ] =>
        eapply (@disjoint_trans_lr _ A B C _ H)
      end 
  end.

Hint Resolve Safe_cond_true Safe_cond_false.

Ltac decide_constructor :=
  match goal with
    H : evalCond _ _ _ _ _ = Some ?B |- RunsTo (Syntax.Conditional _ _ _) _ _ =>
      match B with
        | true => econstructor 6
        | false => econstructor 7
      end
  end.

Hint Extern 1 => decide_constructor.

Hint Resolve runs_loop_partially_body_safe.

Hint Resolve Safe_immune.

Ltac tempOf_solver :=
  match goal with
    H : List.incl (tempVars _) ?VARS |- In (tempOf ?N) ?VARS =>
      eapply In_incl; [eapply temp_in_array with (n := S N); omega | eapply incl_tran with (2 := H) ]
  end.

Hint Extern 1 => tempOf_solver.

Opaque tempVars.

Ltac incl_tran_tempVars :=
  match goal with
    H : List.incl (tempVars _) ?VARS |- List.incl (tempVars _) ?VARS => eapply incl_tran with (2 := H)
  end.

Hint Extern 1 => incl_tran_tempVars.

Ltac clear_step := try clear_imports; step auto_ext.

Ltac in_solver :=
  match goal with
    H : Safe _ _ (_, ?ARRS) |- _ %in fst ?ARRS => rewriter; inv_Safe
  end.

Hint Extern 1 => in_solver.

Ltac use_Safe_immune2 :=
  match goal with
    | H : Safe _ ?S_H (?VS1, ?ARRS), H2 : changed_in ?VS1 ?VS2 _ |- Safe _ ?S_G (?VS2, ?ARRS) =>
      match S_H with
        context [ S_G ] => eapply (@Safe_immune _ S_G VS1 VS2 ARRS); [ | simpl; use_changed_unchanged; use_disjoint_trans']
      end
    | H : Safe _ (Syntax.Seq ?A ?B) ?V, H2 : RunsTo _ ?A ?V ?V' |- Safe _ ?B _ => break_st; rewriter; eapply Safe_immune
    | H : Safe _ (Loop ?E ?B) _, H2 : runs_loop_partially ?E ?B _ _ |- Safe _ ?B _ => break_st; rewriter; eapply Safe_immune; [ eapply (@runs_loop_partially_body_safe _ _ _ _ _ H2) | ]; [ try use_Safe_immune2 | .. ]
  end.

Lemma Safe_seq_first : forall fs a b v, Safe fs (Syntax.Seq a b) v -> Safe fs a v.
  intros; inv_Safe; eauto.
Qed.

Hint Resolve Safe_seq_first.

Lemma unchanged_in_refl : forall vs vars, unchanged_in vs vs vars.
  unfold unchanged_in; eauto.
Qed.

Hint Resolve unchanged_in_refl.

Lemma Safe_seq_second : forall fs a b v v', Safe fs (Syntax.Seq a b) v -> RunsTo fs a v v' -> Safe fs b v'.
  intros; inv_Safe; use_Safe_immune; eauto.
Qed.

Hint Resolve Safe_seq_second.

Ltac change_RunsTo_arrs :=
  match goal with
    H : RunsTo _ ?S (?VS, ?ARRS1) _ |- RunsTo _ ?S (?VS, ?ARRS2) _ => replace ARRS2 with ARRS1
  end.

Hint Extern 1 => change_RunsTo_arrs.

Ltac extend_runs_loop_partially :=
  match goal with
    H : runs_loop_partially _ ?E ?B ?V (?VS, _), H2 : RunsTo _ ?B (?VS, _) ?V'' |- runs_loop_partially _ ?E ?B ?V _ =>
      eapply (@LoopPartialStep _ _ _ _ _ V'' H)
  end.

Ltac use_changed_in_eval :=
  match goal with
    H : VariableLemmas.equiv ?V (merge _ _ _) |- changed_in ?V _ _ =>
      apply_in_all RunsTo_footprint; eapply changed_in_eval; [eassumption | ..]
  end.

Ltac pre_descend := first [change_RunsTo | auto_apply_in runs_loop_partially_finish; [change_RunsTo | ..] ]; open_hyp; break_st.

Ltac arrays_eq_solver :=
  match goal with
    |- ?A = _ =>
    match type of A with
      arrays => simpl in *; congruence
    end
  end.

Ltac choose_changed_unchanged :=
  match goal with
    H : disjoint ?A ?B |- unchanged_in _ _ ?C =>
      match A with
        context [ C ] => eapply (@changed_unchanged _ _ B _)
      end
  end.

Ltac iter_changed_discharger := first [eassumption | eapply changedVariables_incl; [eassumption | ..] | eapply changedVariables_upd_fwd | eapply changedVariables_incl; [eapply changedVariables_upd_fwd | ..] ].

Ltac iter_changed := repeat first [iter_changed_discharger | eapply changed_trans_l].

Ltac format_solver :=
  match goal with
    |- _ = exprDenote _ _ ^+ $4 ^* exprDenote _ _ =>
    rewriter; erewrite changed_in_inv by eauto; rewrite sel_upd_eq by eauto; rewriter; repeat (f_equal; try (eapply unchanged_exprDenote; choose_changed_unchanged; iter_changed))
  end.

Opaque List.incl.

Lemma changed_in_upd_eq : forall vs1 vs2 vars s val1 val2,
  changed_in vs1 vs2 vars ->
  val2 = val1 ->
  changed_in (upd vs1 s val1) (upd vs2 s val2) vars.
  intros; rewriter; eauto.
Qed.

Hint Resolve changed_in_upd_eq.

Lemma safe_access_in : forall arrs arr idx, safe_access arrs arr idx -> arr %in fst arrs.
  unfold safe_access; intuition.
Qed.

Hint Resolve safe_access_in.

Ltac use_changed_in_upd_same :=
  match goal with
    |- changed_in (upd _ ?S _) (upd _ ?S _) _ => eapply changed_in_upd_same; iter_changed
  end.

Ltac auto_unfold :=
  repeat match goal with
           t := _ |- _ => unfold t in *; clear t
         end.

Hint Resolve del_add.

Hint Resolve WMake.equiv_symm.

Ltac max_2_plus :=
  match goal with
    |- (max _ _ >= 2 + _)%nat => simpl
  end.

Hint Extern 1 => max_2_plus.

Ltac tempOf_neq :=
  match goal with
    |- ~ (tempOf _ = tempOf _) => discriminate
  end.

Hint Extern 1 => tempOf_neq.

Ltac not_in_solver :=
  match goal with 
    H : ?ARRS = _ |- ~ _ %in fst ?ARRS => rewriter
  end.

Ltac no_question_mark :=
  match goal with
    |- ?T => match T with T => idtac end
  end.

Ltac upd_chain_solver :=
  match goal with
    H1 : changed_in _ _ _, H2 : changed_in (upd _ _ _) _ _, H3 : changed_in (upd _ _ _) _ _ |- changed_in _ _ _ => no_question_mark; simpl; iter_changed
  end.

Ltac rv_length_solver :=
  match goal with
    H : Regs ?ST Rv = natToW (length _) |- Regs ?ST Rv = natToW (length _) => rewriter
  end.

Hint Extern 1 => rv_length_solver.

Ltac arrays_eq_solver2 :=
  match goal with
    H : ?A = _ |- ?A = _ =>
      match type of A with
        arrays => rewriter
      end
  end.

Ltac RunsTo_Malloc :=
  match goal with
    |- RunsTo _ (Syntax.Malloc _ _) _ _ => econstructor
  end.

Local Notation "v [( e )]" := (exprDenote e (fst v)) (no associativity, at level 60).
  
Lemma RunsToRelax_loop_false : forall fs e b k v1 v2, 
  fs ~:~ v1 ~~ k ~~> v2 -> 
  wneb (v1[(e)]) $0 = false -> 
  fs ~:~ v1 ~~ Loop e b;: k ~~> v2.
  unfold RunsToRelax; intros; openhyp; descend; eauto.
Qed.
Hint Resolve RunsToRelax_loop_false.

Hint Constructors Safe.
Lemma Safe_cond_true_k : forall fs e t f k v, 
  Safe fs (Conditional e t f;: k) v ->
  wneb (v[(e)]) $0 = true ->
  Safe fs (t;: k) v.
  inversion 1; intros; econstructor; eauto.
Qed.
Hint Resolve Safe_cond_true_k.
Lemma Safe_cond_false_k : forall fs e t f k v, 
  Safe fs (Conditional e t f;: k) v ->
  wneb (v[(e)]) $0 = false ->
  Safe fs (f;: k) v.
  inversion 1; intros; econstructor; eauto.
Qed.
Hint Resolve Safe_cond_false_k.

Ltac use_disjoint_trans'' := 
  match goal with
    | H : disjoint ?A ?B |- disjoint ?C _ =>
      match A with context [ C ] =>
        eapply (@disjoint_trans_lr _ A B C _ H)
      end 
    | H : disjoint ?A ?B |- disjoint (?C1 ++ ?C2) _ =>
      match A with context [ C1 ] =>
        match A with context [ C2 ] =>
          eapply (@disjoint_trans_lr _ A B (C1 ++ C2) _ H)
        end
      end 
  end.
Hint Extern 1 => use_disjoint_trans''.

Ltac change_rp :=
  match goal with
    H : ?SPECS (sel ?VS1 "rp") = Some _ |- ?SPECS (sel ?VS2 "rp") = Some _ =>
      replace (sel VS2 "rp") with (sel VS1 "rp") by (symmetry; eapply changed_in_inv; [ eauto | ]; eapply in_tran_not; [ | eauto ]; eapply incl_tran; [ | eassumption ]; eauto)
  end.
Local Notation "'tmps' s" := (tempVars (depth s)) (at level 60).
Local Notation "'etmps' s" := (tempVars (edepth s)) (at level 60).
Ltac change_RunsTo_for_goal :=
  match goal with
    H : RunsTo _ ?S ?VS1 _ |- context [ RunsTo _ ?S ?VS1' _ ] => generalize H; eapply RunsTo_immune with (vs1' := VS1') in H; intros
  end.

Local Notation agree_in := unchanged_in.
Local Notation agree_except := changed_in.
Definition st_agree_except (v1 v2 : st) vars := agree_except (fst v1) (fst v2) vars /\ snd v1 = snd v2.
Local Notation "b [ vars => c ]" := (merge c b vars) (no associativity, at level 60).
Infix "==" := VariableLemmas.equiv.
Local Notation "v1 =~= v2 [^ except ]" := (st_agree_except v1 v2 except) (no associativity, at level 60).

Lemma st_agree_except_symm : forall v1 v2 ex, v1 =~= v2 [^ex] -> v2 =~= v1 [^ex].
  unfold st_agree_except; intuition.
Qed.
Lemma RunsToRelax_immune : forall fs s v1 v2 v1' v2', 
  fs ~:~ v1 ~~ s ~~> v2 ->
  v1' =~= v1 [^ tmps s] -> 
  v2' =~= v2 [^ tmps s] ->
  disjoint (footprint s) (tmps s) ->
  fs ~:~ v1' ~~ s ~~> v2'.
  intros; eapply st_agree_except_symm in H0; eapply st_agree_except_symm in H1; unfold st_agree_except, RunsToRelax in *; openhyp; change_RunsTo_for_goal; eauto; openhyp; descend.
  eauto.
  use_changed_in_eval; eauto; eapply changedVariables_symm in H0; eauto.
  congruence.
Qed.
Ltac change_RunsTo_to t :=
  match goal with
    H : RunsTo _ ?S ?VS1 _ |- _ => generalize H; eapply RunsTo_immune with (vs1' := t) in H; intros
  end.
Local Notation "fs -:- v1 -- s --> v2" := (RunsTo fs s v1 v2) (no associativity, at level 60).
Lemma inversion_RunsTo_seq : forall fs a b v1 v2, fs -:- v1 -- a;: b --> v2 -> exists v, fs -:- v1 -- a --> v /\ fs -:- v -- b --> v2.
  inversion 1; eauto.
Qed.
Hint Resolve Max.max_lub.
Lemma st_agree_except_refl : forall v ex, v =~= v [^ex].
  unfold st_agree_except; eauto.
Qed.
Hint Resolve st_agree_except_refl.
Lemma RunsToRelax_cond_true' : forall fs e t f k v1 v2,
  fs ~:~ v1 ~~ t;: k ~~> v2 ->
  wneb (v1[(e)]) $0 = true ->
  fs ~:~ v1 ~~ Conditional e t f;: k ~~> v2.
  unfold RunsToRelax; intros; openhyp; auto_apply_in inversion_RunsTo_seq; openhyp; descend; simpl in *; eauto 6.
Qed.
Hint Resolve RunsToRelax_cond_true'.
Lemma RunsToRelax_cond_true : forall fs e t f k v1 v1' v2,
  let s := Conditional e t f;: k in
    fs ~:~ v1 ~~ t;: k ~~> v2 ->
    v1' =~= v1 [^etmps e] ->
    wneb (v1'[(e)]) $0 = true ->
    disjoint (footprint s) (tmps s) ->
    fs ~:~ v1' ~~ s ~~> v2.
  intros; eapply RunsToRelax_immune; unfold s, st_agree_except in *; openhyp; descend; simpl in *; eauto.
Qed.
Lemma RunsToRelax_cond_false' : forall fs e t f k v1 v2,
  fs ~:~ v1 ~~ f;: k ~~> v2 ->
  wneb (v1[(e)]) $0 = false ->
  fs ~:~ v1 ~~ Conditional e t f;: k ~~> v2.
  unfold RunsToRelax; intros; openhyp; auto_apply_in inversion_RunsTo_seq; openhyp; descend; simpl in *; eauto 6.
Qed.
Hint Resolve RunsToRelax_cond_false'.
Lemma RunsToRelax_cond_false : forall fs e t f k v1 v1' v2,
  let s := Conditional e t f;: k in
    fs ~:~ v1 ~~ f;: k ~~> v2 ->
    v1' =~= v1 [^etmps e] ->
    wneb (v1'[(e)]) $0 = false ->
    disjoint (footprint s) (tmps s) ->
    fs ~:~ v1' ~~ s ~~> v2.
  intros; eapply RunsToRelax_immune; unfold s, st_agree_except in *; openhyp; descend; simpl in *; eauto.
Qed.
Hint Unfold st_agree_except.
Hint Resolve RunsToRelax_cond_true RunsToRelax_cond_false.

Local Notation "v [ e ]" := (exprDenote e v) (no associativity, at level 60).
Lemma Safe_assign : forall fs var e k vs arrs,
  Safe fs (var <- e;: k) (vs, arrs)
  -> Safe fs k (upd vs var (vs[e]), arrs).
  inversion 1; eauto.
Qed.
Lemma in_not_in_ne : forall A ls (a b : A), In a ls -> ~ In b ls -> a <> b.
  intuition.
Qed.

Local Notation "a [ i ] *<- e" := (Syntax.WriteAt a i e) (at level 60).

Fixpoint denote_sem s (v : st) := 
  match s with
    | var <- e => (upd (fst v) var (fst v[e]), snd v)
    | arr[idx] *<- val => 
      let (vs, arrs) := v in 
        let arr_v := exprDenote arr vs in
          let idx_v := exprDenote idx vs in
            let value_v := exprDenote val vs in
              let new_arr := Array.upd (snd arrs arr_v) idx_v value_v in
                (vs, (fst arrs, WDict.upd (snd arrs) arr_v new_arr))
    | Syntax.ReadAt var arr idx =>
      let (vs, arrs) := v in
        let arr_v := exprDenote arr vs in
          let idx_v := exprDenote idx vs in
            let value_v := Array.sel (snd arrs arr_v) idx_v in  
              (Locals.upd vs var value_v, arrs)
    | Syntax.Len var arr => 
      let (vs, arrs) := v in
        let arr_v := exprDenote arr vs in
          let len := natToW (length (snd arrs arr_v)) in
            (Locals.upd vs var len, arrs)
    | _ => v
  end.

Lemma RunsToRelax_assign : forall fs var e k v1 v2 v3,
  fs ~:~ v2 ~~ k ~~> v3 ->
  denote_sem (var <- e) v1 =~= v2 [^etmps e] ->
  disjoint (footprint k) (etmps e) ->
  fs ~:~ v1 ~~ var <- e;: k ~~> v3.
  intros; eapply st_agree_except_symm in H0; unfold denote_sem, RunsToRelax, st_agree_except in *; openhyp; change_RunsTo_to (denote_sem (var <- e) v1); eauto; openhyp; destruct v1; simpl in *; descend.
  eauto.
  eapply changedVariables_symm in H0; use_changed_in_eval; eauto.
  congruence.
Qed.

Lemma Safe_assoc_left : forall fs a b c v, Safe fs (a;: b;: c) v -> Safe fs (a;: (b;: c)) v.
  clear; intros; inv_Safe; subst; inversion H; subst; econstructor; [ | intros; econstructor ]; eauto.
Qed.
Ltac true_not_false :=
  match goal with
    H1 : ?A = true, H2 : ?A = false |- _ => eapply Bool.eq_true_false_abs in H1; intuition
  end.
Hint Extern 1 => true_not_false.
Lemma Safe_loop_true : forall fs e b v,
  Safe fs (Loop e b) v ->
  wneb (v[(e)]) $0 = true ->
  Safe fs (b;: Loop e b) v.
  intros.
  inv_Safe.
  unfold statement0 in *.
  rewrite <- H2 in *.
  eauto.
  eauto.
Qed.
Hint Resolve Safe_loop_true.
Lemma RunsTo_loop_true : forall fs e b v1 v2,
  fs -:- v1 -- b;: Loop e b --> v2 ->
  wneb (v1[(e)]) $0 = true ->
  fs -:- v1 -- Loop e b --> v2.
  clear; intros; eapply inversion_RunsTo_seq in H; openhyp; eauto.
Qed.
Hint Resolve RunsTo_loop_true.
Lemma Safe_loop_true_k : forall fs e b k v, 
  Safe fs (Loop e b;: k) v ->
  wneb (v[(e)]) $0 = true ->
  Safe fs (b;: (Loop e b;: k)) v.
  intros.
  inv_Safe.
  subst.
  inversion H3; try (unfold vals in *; congruence).
  subst b.
  subst v.
  econstructor.
  eauto.
  intros.
  econstructor; eauto.
Qed.
Hint Resolve Safe_loop_true_k.
Local Notation agree_except_trans := changedVariables_trans.
Definition tmps_diff big small := tempChunk (depth small) (depth big - depth small).
Lemma agree_except_app_comm : forall vs1 vs2 a b,
  agree_except vs1 vs2 (a ++ b) ->
  agree_except vs1 vs2 (b ++ a).
  intros; eauto.
Qed.
Lemma merge_comm : forall v vars1 v1 vars2 v2,
  disjoint vars1 vars2 ->
  v [vars1 => v1] [vars2 => v2] == v [vars2 => v2] [vars1 => v1].
  intros.
  unfold VariableLemmas.equiv, changedVariables.
  intros.
  contradict H0.
  destruct (In_dec string_dec x vars1).
  destruct (In_dec string_dec x vars2).
  unfold disj in *.
  contradict H.
  eauto.
  rewrite sel_merge by eauto.
  rewrite sel_merge_outside by eauto.
  rewrite sel_merge by eauto.
  eauto.
  destruct (In_dec string_dec x vars2).
  rewrite sel_merge_outside by eauto.
  rewrite sel_merge by eauto.
  rewrite sel_merge by eauto.
  eauto.
  rewrite sel_merge_outside by eauto.
  rewrite sel_merge_outside by eauto.
  rewrite sel_merge_outside by eauto.
  rewrite sel_merge_outside by eauto.
  eauto.
Qed.
Lemma equiv_merge_equiv : forall v1 v2 vars v,
  v1 == v2 ->
  v1 [vars => v] == v2 [vars => v].
  intros; eapply two_merge_equiv; eauto.
Qed.
Lemma RunsToRelax_seq_fwd : forall fs a b v1 v2,
  fs ~:~ v1 ~~ a;: b ~~> v2 ->
  disjoint (footprint (a;: b)) (tmps (a;: b)) ->
  exists v, fs ~:~ v1 ~~ a ~~> v /\ fs ~:~ v ~~ b ~~> v2.
  clear.
  unfold RunsToRelax; intros.
  openhyp.
  eapply inversion_RunsTo_seq in H.
  openhyp.
  simpl in *.
  destruct (le_lt_dec (depth a) (depth b)).
  exists (fst x0 [tmps a => fst v2], snd x0).
  split.
  descend; eauto.
  eapply changed_merge_fwd.
  change_RunsTo_for_goal.
  openhyp.
  simpl in *.
  descend; eauto.
  use_changed_in_eval.
  eapply changed_trans_l.
  eapply changed_merge_bwd.
  eauto.
  eauto.
  eauto.
  congruence.
  simpl.
  eapply changed_unchanged.
  eapply changed_merge_fwd.
  eauto.
  eauto.
  set (diff := tmps_diff a b).
  exists (fst x0 [diff => fst v2], snd x0).
  split.
  descend; eauto.
  eapply agree_except_trans.
  2 : eapply changed_merge_fwd.
  eauto.
  eauto.
  unfold diff, tmps_diff.
  eapply incl_tempChunk2.
  omega.
  change_RunsTo_for_goal.
  openhyp.
  simpl in *.
  descend; eauto.
  eapply changed_trans_l.
  Focus 2.
  eapply changed_merge.
  eapply agree_except_app_comm.
  rewrite Max.max_l in * by eauto.
  erewrite <- split_tmps.
  eauto.
  eauto.
  2 : eapply List.incl_refl.
  eapply changedVariables_incl.
  2 : eauto.
  eapply VariableLemmas.equiv_trans.
  eauto.
  apply_in_all RunsTo_footprint.
  eapply VariableLemmas.equiv_trans.
  eapply VariableLemmas.equiv_symm.
  eapply merge_comm.
  unfold diff, tmps_diff.
  eauto.
  unfold diff, tmps_diff.
  eapply equiv_merge_equiv.
  eapply changed_merge.
  eauto.
  congruence.
  simpl.
  unfold diff, tmps_diff.
  eapply changed_unchanged.
  eapply changed_merge_fwd.
  eauto.
  eauto.
Qed.
Lemma RunsToRelax_seq_bwd : forall fs a b v1 v2 v3,
  fs ~:~ v1 ~~ a ~~> v2 ->
  fs ~:~ v2 ~~ b ~~> v3 ->
  disjoint (footprint (a;: b)) (tmps (a;: b)) ->
  fs ~:~ v1 ~~ a;: b ~~> v3.
  unfold RunsToRelax; intros; openhyp; generalize dependent H; simpl in *; change_RunsTo_to x0; eauto; openhyp; descend; eauto; try use_changed_in_eval; eauto.
  congruence.
Qed.
Hint Resolve RunsToRelax_seq_bwd.
Lemma RunsToRelax_assoc_left : forall fs a b c v1 v2,
  fs ~:~ v1 ~~ a;: (b;: c) ~~> v2 ->
  disjoint (footprint (a;: (b;: c))) (tmps (a;: (b;: c))) ->
  fs ~:~ v1 ~~ a;: b;: c ~~> v2.
  clear; simpl; intros; eapply RunsToRelax_seq_fwd in H; eauto; openhyp; eapply RunsToRelax_seq_fwd in H1; eauto; openhyp; repeat eapply RunsToRelax_seq_bwd; repeat (simpl; eauto).
Qed.
Lemma RunsToRelax_loop_true : forall fs e b v1 v2, 
  fs ~:~ v1 ~~ b;: Loop e b ~~> v2 -> 
  wneb (v1[(e)]) $0 = true -> 
  fs ~:~ v1 ~~ Loop e b ~~> v2.
  unfold RunsToRelax; intros; openhyp; simpl in *; descend; eauto.
Qed.
Hint Resolve RunsToRelax_loop_true.
Lemma RunsToRelax_loop_true_k : forall fs e b k v1 v2, 
  let s := Loop e b;: k in
    fs ~:~ v1 ~~ b;: s ~~> v2 -> 
    wneb (v1[(e)]) $0 = true -> 
    disjoint (footprint s) (tmps s) ->
    fs ~:~ v1 ~~ s ~~> v2.
  simpl; intros; eapply RunsToRelax_assoc_left in H; simpl; eauto; eapply RunsToRelax_seq_fwd in H; simpl; eauto; openhyp; eauto.
Qed.
Hint Resolve RunsToRelax_loop_true_k.

Hint Resolve Safe_assoc_left.

Local Notation skip := Syntax.Skip.

Lemma RunsToRelax_skip : forall fs s v1 v2,
  fs ~:~ v1 ~~ s ~~> v2 ->
  fs ~:~ v1 ~~ skip;: s ~~> v2.
  unfold RunsToRelax; intros; openhyp; descend; eauto.
Qed.
Hint Resolve RunsToRelax_skip.

Lemma mult_S_distr : forall a b, a * S b = a + a * b.
  intros; ring.
Qed.

Opaque star. (* necessary to use eapply_cancel *)

Ltac eapply_cancel h specs st := let HP := fresh in let Hnew := fresh in
  evar (HP : HProp); assert (interp specs (![HP] st)) as Hnew;
    [ | eapply h in Hnew; [ | clear Hnew .. ] ]; unfold HP in *; clear HP; 
      [ solve [try clear_imports; hiding ltac:(step auto_ext) ] | .. ].

Ltac transit := 
  match goal with
    | H_interp : interp _ _, H : _ |- _ => eapply H in H_interp; clear H
    | H_interp : interp ?SPECS (![_] ?ST), H : context [interp _ (![_] ?ST) -> _] |- _ => eapply_cancel H SPECS ST; clear H H_interp
  end.

Ltac try_post :=
  try match goal with
    H_interp : interp _ ?P |- _ =>
      match P with
        | context [ Exists ] => post
      end
  end.

Lemma pack_pair' : forall A B (x : A * B), (let (x, _) := x in x, let (_, y) := x in y) = x.
  destruct x; simpl; intuition.
Qed.

Lemma fold_second : forall A B (p : A * B), (let (_, y) := p in y) = snd p.
  destruct p; simpl; intuition.
Qed.

Lemma fold_first : forall A B (p : A * B), (let (x, _) := p in x) = fst p.
  destruct p; simpl; intuition.
Qed.

Ltac post_step := repeat first [ rewrite pack_pair' in * | rewrite fold_second in * | rewrite fold_first in *].

Ltac not_mem_rv INST := 
  match INST with
    | context [LvMem ?LOC] =>
      match LOC with
        | context [Rv] => fail 2
        | _ => idtac
      end
    | _ => idtac
  end.

Ltac pre_eval_auto := 
  repeat 
    match goal with
      | H_eval : evalInstrs _ ?ST ?INST = _, H_interp : interp _ (![?P] (_, ?ST)) |- _ =>
        match INST with
          context [ Rv ] => 
          match goal with
            H_rv : Regs ST Rv = _ |- _ => not_mem_rv INST; post_step; generalize dependent H_rv
          end
        end
      | H_eval : evalInstrs _ ?ST ?INST = _, H_interp : interp _ (![?P] (_, ?ST)) |- _ =>
        match P with
          context [ heap ?HEAP ] => 
          match goal with
            H_heap : HEAP = _ |- _ => post_step; generalize dependent H_heap
          end
        end
    end.

Ltac evaluate_hints hints :=
  match goal with
    H : evalInstrs _ ?ST _ = _ |- _ => generalize dependent H; evaluate hints; intro; evaluate auto_ext
  end.

Ltac my_evaluate hints :=
  match goal with
    | H: interp _ (![_](_, ?ST)), H_eval: evalInstrs _ ?ST ?INST = _ |- _  =>
      match INST with
        | context [LvMem (Reg Rv) ] => evaluate_hints hints
        | _ => pre_eval_auto; evaluate hints
      end
  end.

Ltac simpl_sp :=
  repeat match goal with
           H : (_, _) # Sp = _ |- _ => simpl in H
         end.

Ltac fold_length := 
  change (fix length (l : list string) : nat :=
    match l with
      | nil => 0
      | _ :: l' => S (length l')
    end) with (@length string) in *.

Lemma fold_4S : forall n, (S (S (S (S (4 * n))))) = (4 + (4 * n)).
  eauto.
Qed.

Lemma Safe_ReadAt_safe_access : forall fs var arr idx v, 
  Safe fs (Syntax.ReadAt var arr idx) v ->
  safe_access (snd v) (exprDenote arr (fst v)) (exprDenote idx (fst v)).
  intros; inv_Safe_clear; eauto.
Qed.

Lemma Safe_WriteAt_safe_access : forall fs arr idx val v, 
  Safe fs (Syntax.WriteAt arr idx val) v ->
  safe_access (snd v) (exprDenote arr (fst v)) (exprDenote idx (fst v)).
  intros; inv_Safe_clear; eauto.
Qed.

Lemma Safe_ReadAt_k_safe_access : forall fs var arr idx v k, 
  Safe fs (Syntax.ReadAt var arr idx;: k) v ->
  safe_access (snd v) (exprDenote arr (fst v)) (exprDenote idx (fst v)).
  intros; eapply Safe_seq_first in H; inv_Safe_clear; eauto.
Qed.

Lemma Safe_WriteAt_k_safe_access : forall fs arr idx val v k, 
  Safe fs (Syntax.WriteAt arr idx val;: k) v ->
  safe_access (snd v) (exprDenote arr (fst v)) (exprDenote idx (fst v)).
  intros; eapply Safe_seq_first in H; inv_Safe_clear; eauto.
Qed.

Ltac not_exist t :=
  match goal with
    | H : t |- _ => fail 1
    | |- _ => idtac
  end.

Ltac assert_new t := not_exist t; assert t.

Ltac assert_new_as t name := not_exist t; assert t as name.

Definition heap_tag arrs (_ _ : W) := heap arrs.

Ltac set_all t := let name := fresh "t" in set (name := t) in *.

Ltac clear_bad H_interp s :=
  repeat 
    match goal with
      | H : context [changed_in _ _ _] |- _ => generalize H; clear H
      | H : Regs ?ST Rv = _  |- _ => not_eq ST s; generalize H; clear H
      | H : context [Safe _ _ _] |- _ => not_eq H H_interp; generalize H; clear H
    end.

Lemma Safe_Len_k_in : forall fs var ptr v k, 
  Safe fs (Syntax.Len var ptr;: k) v ->
  fst v[ptr] %in fst (snd v).
  intros; eapply Safe_seq_first in H; inv_Safe_clear; eauto.
Qed.

Ltac simpl_interp :=
  match goal with
    | H: interp _ (![_](_, ?ST)), H_eval: evalInstrs _ ?ST _ = _ |- _  =>
      simpl in H; try rewrite fold_4S in H
  end.

Ltac pre_eval :=
  match goal with
    | H: interp _ (![_](_, ?ST)), H_eval: evalInstrs _ ?ST _ = _ |- _  =>
      try clear_imports; HypothesisParty H; prep_locals; clear_bad H ST;
        simpl_interp; simpl_sp; try rewrite fold_4S in *
  end.

Ltac post_eval := intros; try fold (@length W) in *; post_step; try fold_length; try rewrite fold_4S in *.

Definition heap_to_split arrs (_ : W) := heap arrs.
  
Ltac cond_gen := try
  match goal with
    | H_interp : interp _ (![_](_, ?ST)), H_eval : evalInstrs _ ?ST ?INST = _ |- _ =>
      match INST with
        | context [variablePosition ?vars ?s] => assert_new (In s vars)
        | context [variableSlot ?s ?vars] => assert_new (In s vars)
        | context [ LvMem (Reg Rv) ] =>
          match goal with
            | H : safe_access ?ARRS ?ARR ?IDX, H_rv : Regs ST Rv = _ |- _ =>
              assert_new (Regs ST Rv = ARR ^+ $4 ^* IDX); [ | clear H_rv; replace (heap ARRS) with (heap_tag ARRS ARR IDX) in * by eauto; set_all ARR; set_all IDX ]
            | H : ?ARR %in fst ?ARRS, H_rv : Regs ST Rv = _ |- _ =>
              assert_new (Regs ST Rv = ARR ^- $4); [ | clear H_rv; replace (heap ARRS) with (heap_to_split ARRS ARR) in * by eauto; set_all ARR ]
            | H : Safe _ (Syntax.ReadAt _ ?ARR ?IDX) ?ST |- _ => eapply Safe_ReadAt_safe_access in H; simpl in H
            | H : Safe _ (Syntax.WriteAt ?ARR ?IDX _) ?ST |- _ => eapply Safe_WriteAt_safe_access in H; simpl in H
            | H : Safe _ (Syntax.ReadAt _ ?ARR ?IDX;: _) ?ST |- _ => generalize H; eapply Safe_ReadAt_k_safe_access in H; simpl in H
            | H : Safe _ (Syntax.WriteAt ?ARR ?IDX _;: _) ?ST |- _ => generalize H; eapply Safe_WriteAt_k_safe_access in H; simpl in H
            | H : Safe _ (Syntax.Len _ ?ARR;: _) ?ST |- _ => generalize H; eapply Safe_Len_k_in in H; simpl in H
          end
      end; [ clear H_eval .. | cond_gen ]
  end.

Definition get_arr (arrs : arrays) addr := snd arrs addr.

Definition add_arr arrs addr ls := (fst arrs %+ addr, WDict.upd (snd arrs) addr ls).

Definition remove_arr (arrs : arrays) addr := (fst arrs %- addr, snd arrs).

Lemma star_comm : forall a b, a * b ===> b * a.
  clear; intros; sepLemma.
Qed.

Lemma star_cancel_left : forall a b c, b ===> c -> a * b ===> a * c.
  clear; intros; sepLemma.
Qed.

Lemma star_cancel_right : forall a b c, b ===> c -> b * a ===> c * a.
  clear; intros; sepLemma.
Qed.

(* starS_equiv has been added to Sets.v. This lemma can be deleted from here after updating bedrock repo *)
Ltac to_himp := repeat intro.

Ltac from_himp := match goal with
                    | [ |- interp ?specs (?p ?x ?y ---> ?q ?x ?y) ] =>
                      generalize dependent y; generalize dependent x; generalize dependent specs;
                        change (p ===> q)
                  end.

Lemma starS_equiv : forall P a b, a %= b -> starS P a ===> starS P b.
  clear.
  intros.
  unfold starS.
  to_himp.
  apply existsL.
  intros.
  apply existsR with x.
  from_himp.
  eapply star_cancel_right.
  sepLemma.
Qed.

Lemma heap_equiv : forall a b, a %%= b -> heap a ===> heap b.
  intros.
  destruct a; destruct b.
  unfold equiv in *.
  simpl in H.
  openhyp.
  unfold heap.
  eapply Himp_trans.
  eapply starS_equiv.
  eauto.
  eapply starS_weaken.
  intros.
  unfold array_ptr.
  rewrite H0.
  eapply Himp_refl.
  eauto.
Qed.

Lemma equiv_symm : forall a b, a %%= b -> b %%= a.
  clear; unfold equiv, WMake.equiv; simpl; intros; firstorder.
Qed.

Hint Resolve equiv_symm.

Definition trigger A (_ : A) := True.

Lemma array_ptr_array_with_size : forall d ls p, array_ptr (WDict.upd d p ls) p = array_with_size ls p.
  clear; intros; unfold array_ptr; rewrite WDict.sel_upd_eq; eauto.
Qed.

Lemma heap_bwd : forall arrs, trigger arrs -> (Ex arr_ptr, Ex old_arrs, Ex new_arr, [| arrs %%= add_arr old_arrs arr_ptr new_arr |] * [| ~ arr_ptr %in fst old_arrs |] * (heap old_arrs * array_with_size new_arr arr_ptr)) ===> heap arrs.
  clear; intros.
  cancel auto_ext.
  post_step.
  simpl in x.
  destruct x0.
  simpl in H1.
  eapply Himp_trans.
  Focus 2.
  eapply heap_equiv.
  eauto.
  unfold add_arr; simpl.
  eapply Himp_trans.
  Focus 2.
  eapply starS_add_bwd.
  eauto.
  rewrite array_ptr_array_with_size.
  eapply Himp_trans.
  eapply star_comm.
  eapply star_cancel_right.
  eapply starS_weaken.
  intros.
  unfold array_ptr.
  rewrite WDict.sel_upd_ne.
  eapply Himp_refl.
  eauto.
Qed.

Ltac trigger_bwd Hprop :=
  match Hprop with
    context [ heap ?ARRS ] =>
    assert (trigger ARRS) by (unfold trigger; trivial)
  end.

Lemma equiv_refl : forall a, a %%= a.
  clear; unfold equiv; intros; firstorder.
Qed.
Hint Resolve equiv_refl.

Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

Hint Resolve in_not_in_ne.

Local Notation delete := Syntax.Free.

Lemma heap_fwd : forall arrs arr, arr %in fst arrs -> heap_to_split arrs arr ===> Ex new_arrs, [| new_arrs = remove_arr arrs arr |] * array_with_size (get_arr arrs arr) arr * heap new_arrs.
  clear; intros.
  cancel auto_ext.
  unfold heap_to_split, heap, arrays in *.
  destruct arrs.
  simpl in *.
  eapply Himp_trans.
  eapply starS_del_fwd.
  eauto.
  replace (array_ptr d arr) with (array_with_size (d arr) arr) by eauto.
  eapply star_comm.
Qed.

Lemma Safe_free_in : forall fs ptr v, Safe fs (delete ptr) v -> fst v [ptr] %in fst (snd v).
  inversion 1; subst; eauto.
Qed.
Hint Resolve Safe_free_in.

Lemma RunsTo_RunsToRelax : forall fs s v1 v2,
  fs -:- v1 -- s --> v2 ->
  fs ~:~ v1 ~~ s ~~> v2.
  clear; unfold RunsToRelax; intro; descend; eauto.
Qed.
Hint Resolve RunsTo_RunsToRelax.

Lemma heap_fwd_access : forall arrs arr idx, safe_access arrs arr idx -> heap_tag arrs arr idx ===> Ex new_arrs, [| new_arrs = remove_arr arrs arr |] * [| (idx < natToW (length (get_arr arrs arr)))%word |] * array_with_size (get_arr arrs arr) arr * heap new_arrs.
  clear; intros.
  cancel auto_ext.
  unfold safe_access in *; simpl in *; openhyp; eauto.
  unfold heap_tag, heap, arrays in *.
  destruct arrs.
  eapply Himp_trans.
  eapply starS_del_fwd.
  unfold safe_access in *; simpl in *; openhyp; eauto.
  unfold get_arr; simpl.
  replace (array_ptr d arr) with (array_with_size (d arr) arr) by eauto.
  eapply star_comm.
Qed.

Lemma array_with_size_fwd : forall ls p, array_with_size ls p ===> let len := length ls in ([| p <> $8 /\ freeable (p ^- $8) (len + 2) /\ goodSize (len + 2) |] * (p ^- $8) =?> 1 * (p ^- $4) =*> natToW len * array ls p)%Sep.
  clear; intros; unfold array_with_size; sepLemma.
Qed.

Lemma array_with_size_bwd : forall ls p, let len := length ls in ([| p <> $8 /\ freeable (p ^- $8) (len + 2) /\ goodSize (len + 2) |] * (p ^- $8) =?> 1 * (p ^- $4) =*> natToW len * array ls p)%Sep ===> array_with_size ls p.
  clear; intros; unfold array_with_size; sepLemma.
Qed.

Definition hints_array_access_bwd : TacPackage.
  prepare tt (heap_bwd, array_with_size_bwd).
Defined.

Ltac apply_save_in lemma hyp := generalize hyp; eapply lemma in hyp; intro.

Ltac assert_sp P Q H_sp :=
  match P with
    context [ locals _ _ _ ?P_SP ] =>
    match Q with
      context [ locals _ _ _ ?Q_SP] =>
      assert (Q_SP = P_SP) as H_sp
    end
  end.

Ltac set_heap_goal :=
  match goal with
    |- context [ heap ?ARRS ] => set_all ARRS
  end.

Ltac set_heap_hyp :=
  match goal with
    H : context [ heap ?ARRS ] |- _ => set_all ARRS
  end.

Ltac set_array_hyp :=
  match goal with
    H : context [ array ?ARR ?PTR ] |- _ => set_all ARR; set_all PTR
  end.

Lemma not_in_remove_arr : forall arr arrs, ~ arr %in fst (remove_arr arrs arr).
  intros; unfold remove_arr; simpl; eauto.
Qed.

Hint Resolve not_in_remove_arr.

Lemma Safe_write_access : forall fs arr idx val vs arrs, 
  Safe fs (Syntax.WriteAt arr idx val) (vs, arrs) ->
  safe_access arrs (exprDenote arr vs) (exprDenote idx vs).
  intros; inv_Safe_clear; eauto.
Qed.
Hint Resolve Safe_write_access.

Lemma Safe_write_k : forall fs a i e k v, let s := a[i] *<- e in Safe fs (s;: k) v -> Safe fs k (denote_sem s v).
  clear; simpl; destruct v; inversion 1; eauto.
Qed.

Definition hints_heap_bwd : TacPackage.
  prepare tt heap_bwd.
Defined.

Definition hints_heap_fwd : TacPackage.
  prepare heap_fwd tt.
Defined.

Definition hints : TacPackage.
  prepare (heap_fwd, heap_fwd_access, array_with_size_fwd) tt.
Defined.

Definition funcsOk (stn : settings) (fs : W -> option Callee) : PropX W (settings * state) := (
  (Al i : W, Al Precond, Al P : callTransition -> Prop, [| fs i = Some (Foreign Precond P) |]
>>>>>>> other
    ---> (i, stn) @@@ (st ~> ExX, Ex vs, Ex a, Ex res,
<<<<<<< local
      ![^[locals ("rp" :: S_RESERVED :: ArgVars ispec) vs res st#Sp * is_heap a * mallocHeap 0] * #0] st
      /\ [| res = wordToNat (vs S_RESERVED) /\ Safe fs (Body ispec) (vs, a) |]
=======
      ![^[locals ("rp" :: "__reserved" :: "__arg" :: nil) vs res st#Sp * heap a * mallocHeap 0] * #0] st
      /\ [| res = wordToNat (vs "__reserved") /\ Precond (sel vs "__arg") a |]
>>>>>>> other
      /\ (st#Rp, stn) @@@ (st' ~> Ex vs', Ex a',
        [| st'#Sp = st#Sp |]
        /\ ![^[locals ("rp" :: S_RESERVED :: ArgVars ispec) vs' res st'#Sp * is_heap a' * mallocHeap 0] * #1] st'
        /\ [| RunsTo fs (Body ispec) (vs, a) (vs', a') /\ st'#Rv = sel vs' (RetVar ispec) |] )))
)%PropX.

Definition inv vars s : assert := 
  st ~> Ex fs, funcsOk (fst st) fs
  /\ ExX, Ex v, Ex res,
  ![^[locals ("rp" :: vars) (fst v) res st#Sp * is_heap (snd v) * mallocHeap 0] * #0] st
  /\ [| res = wordToNat (sel (fst v) S_RESERVED) /\ Safe fs s v |]
  /\ (sel (fst v) "rp", fst st) @@@ (st' ~> Ex v',
    [| st'#Sp = st#Sp |]
    /\ ![^[locals ("rp" :: vars) (fst v') res st'#Sp * is_heap (snd v') * mallocHeap 0] * #1] st'
    /\ [| RunsToRelax fs s v v' |]).

Definition good_name name := prefix name "!" = false.

Definition vars_require vars s := 
  List.incl (footprint s) vars
  /\ List.incl (tempVars (depth s)) vars
  /\ List.Forall good_name (footprint s)
  /\ ~ In "rp" vars
  /\ nth_error vars 0 = Some S_RESERVED.

Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

Section Compiler.

  Variable vars : list string.

  Section Specifications.

    Variable s k : Statement.

    Definition precond := inv vars (s;: k).

    Definition postcond := inv vars k.

    Definition verifCond pre := imply pre precond :: vars_require vars (s;: k) :: nil.

  End Specifications.

  Variable imports : LabelMap.t assert.
  Variable imports_global : importsGlobal imports.
  Variable modName : string.

  Require Import CompileExpr.

  Definition exprCmd := CompileExpr.exprCmd imports_global modName vars.

  Definition Seq2 := @Seq_ _ imports_global modName.

  Definition Strline := Straightline_ imports modName.

  Definition Skip := Straightline_ imports modName nil.

  Fixpoint Seq ls :=
    match ls with
      | nil => Skip
      | a :: ls' => Seq2 a (Seq ls')
    end.

  Definition SaveRv var := Strline (IL.Assign (variableSlot var vars) (RvLval (LvReg Rv)) :: nil).

  Local Notation "v [( e )]" := (exprDenote e (fst v)) (no associativity, at level 60).
  
  Definition loop_inv cond body k : assert := 
    let s := While cond body;: k in
    st ~> Ex fs, funcsOk (fst st) fs /\ ExX, Ex v, Ex res,
    ![^[locals ("rp" :: vars) (fst v) res st#Sp * is_heap (snd v) * mallocHeap 0] * #0] st
    /\ [| res = wordToNat (sel (fst v) S_RESERVED) /\ Safe fs s v |]
    /\ [| st#Rv = v[(cond)] |]
    /\ (sel (fst v) "rp", fst st) @@@ (st' ~> Ex v',
      [| st'#Sp = st#Sp |]
      /\ ![^[locals ("rp" :: vars) (fst v') res st'#Sp * is_heap (snd v') * mallocHeap 0] * #1] st'
      /\ [| RunsToRelax fs s v v' |]).

  Definition afterCall k : assert :=
    st ~> Ex fs, funcsOk (fst st) fs /\ ExX, Ex v : Semantics.st, Ex res,
    let old_sp := st#Sp ^- natToW (4 * (1 + length vars)) in
    ![^[locals ("rp" :: vars) (fst v) res old_sp * is_heap (snd v) * mallocHeap 0 * [| res = wordToNat (sel (fst v) S_RESERVED) /\ Safe fs k v |] ] * #0] st
    /\ (sel (fst v) "rp", fst st) @@@ (st' ~> Ex v',
      [| st'#Sp = old_sp |]
      /\ ![^[locals ("rp" :: vars) (fst v') res st'#Sp * is_heap (snd v') * mallocHeap 0] * #1] st'
      /\ [| RunsToRelax fs k v v' |]).

  Fixpoint compile_exprs exprs base :=
    match exprs with
      | nil => nil
      | x :: xs => exprCmd x base :: SaveRv (tempOf base) :: compile_exprs xs (S base)
    end.

  Fixpoint put_args base target n :=
    match n with
      | 0 => nil
      | S n' => IL.Assign (LvMem (Indir Rv (natToW target))) (RvLval (variableSlot (tempOf base) vars)) :: put_args (1 + base) (4 + target) n'
    end.

  Definition CheckStack n cmd :=
    Structured.If_ imports_global 
      (RvImm (natToW n)) IL.Le (RvLval (variableSlot S_RESERVED vars))
      cmd
      (Structured.Diverge_ imports modName).

  Definition SaveRet var :=
    match var with
      | None => Skip
      | Some x => SaveRv x
    end.

  Fixpoint compile s k :=
    match s with
      | Syntax.Skip => Skip
      | Syntax.Seq a b => Seq2 
          (compile a (Syntax.Seq b k))
          (compile b k)
      | Syntax.If cond t f => Seq2
        (exprCmd cond 0)
        (Structured.If_ imports_global 
          (RvLval (LvReg Rv)) IL.Ne (RvImm $0) 
          (compile t k) 
          (compile f k)) 
      | While cond body => Seq2
        (exprCmd cond 0)
        (Structured.While_ imports_global 
          (loop_inv cond body k)
          (RvLval (LvReg Rv)) IL.Ne (RvImm $0)
          (Seq2
            (compile body (Syntax.Seq (Syntax.While cond body) k))
            (exprCmd cond 0)))
      | Syntax.Call var f args => let init_frame := 2 + length args in 
        CheckStack init_frame (Seq (
          exprCmd f 0
          :: SaveRv (tempOf 0)
          :: nil
          ++ compile_exprs args 1
          ++ Strline (
            IL.Binop Rv Sp Plus (natToW (4 * (1 + List.length vars)))
            :: IL.Binop (LvMem (Indir Rv $4)) (RvLval (variableSlot S_RESERVED vars)) Minus (RvImm (natToW init_frame))
            :: nil
            ++ put_args 1 8 (length args)
            ++ IL.Assign Rv (RvLval (variableSlot (tempOf 0) vars))
            :: IL.Binop Sp Sp Plus (natToW (4 * (1 + List.length vars))) 
            :: nil)
          :: Structured.ICall_ _ _ Rv (afterCall k)
          :: Strline (IL.Binop Sp Sp Minus (natToW (4 * (1 + List.length vars))) :: nil)
          :: SaveRet var
          :: nil
        ))
    end.

  Require Import SemanticsExprLemmas.
  Require Import SemanticsLemmas.

  Lemma star_diff_ptrs : forall specs st other p1 p2, interp specs (![p1 =?>1 * p2 =?> 1 * other] st) -> p1 <> p2.
    rewrite sepFormula_eq.
    propxFo.
    subst.
    unfold smem_get_word in *.
    simpl in *.
    case_eq (smem_get p2 x3).
    intros.
    clear H6.
    case_eq (smem_get p2 x6).
    clear H9.
    intros.
    destruct H2.
    subst.
    destruct H5.
    subst.
    destruct H4.
    subst.
    Require Import Bootstrap.
    eapply disjoint_get_fwd in H2.
    eauto.
    erewrite join_Some by eassumption.
    discriminate.
    erewrite join_Some by eassumption.
    discriminate.
    intros.
    rewrite H0 in H9.
    discriminate.
    intros.
    rewrite H in H6.
    discriminate.
  Qed.

  Hint Resolve star_diff_ptrs.

  Ltac hiding tac :=
    (let P := fresh "P" in
      match goal with
        | [ H : Safe ?fs _ _ |- _ ] => set (P := Safe fs) in *
        | [ H : ?fs ~:~ _ ~~ _ ~~> _ |- _ ] => set (P := RunsToRelax fs) in *
      end;
      hiding tac;
      subst P) || tac.

  Ltac rearrange_stars HEAD :=
    match goal with
      H : interp ?SPECS (![?P] ?ST) |- _ =>
        let OTHER := fresh in 
          evar (OTHER : HProp); 
          assert (interp SPECS (![HEAD * OTHER] ST));
            unfold OTHER in *; clear OTHER;
              [ hiding ltac:(step auto_ext) | .. ]
    end.

  Infix "=~*>" := (ptsto32 nil) (at level 30).

  Import MHeap.MSet.

  Ltac auto_apply :=
    match goal with
      H : _ |- _ => eapply H
    end.

  Ltac open_Some := 
    match goal with
      H : Some _ = Some _ |- _ => injection H; clear H; intros
    end.

  Ltac condition_solver :=  
    match goal with
      H : evalCond _ _ _ _ _ = Some ?T |- wneb _ _ = ?T => 
      unfold evalCond in *; simpl in *; open_Some; rewriter_r; f_equal
    end.

  Open Scope nat.

  Hint Rewrite sum_S : arith.
  Hint Resolve S_le_lt.
  Hint Resolve sel_upd_firstn.
  Hint Resolve firstn_S_upd.
  Hint Resolve VariableLemmas.noChange.
  Hint Resolve Max.le_max_l Max.le_max_r.
  Hint Extern 12 => rv_solver.
  Hint Extern 12 => sp_solver.
  Hint Resolve le_plus_lt lt_max_l lt_max_r.
  Hint Resolve plus_le.
  Hint Resolve lt_le_S plus_lt.

  Hint Resolve le_max_l_trans.
  Hint Resolve le_max_r_trans.
  Hint Extern 0 (_ <= _) => progress max_le_solver.
  Hint Extern 0 (List.incl _ _) => progress incl_app_solver.

  Hint Resolve in_eq In_incl.
  Hint Resolve List.incl_cons incl_cons_l incl_cons_r List.incl_refl incl_nil incl_tl incl_array.
  Hint Resolve incl_app incl_appl incl_appr.
  Hint Resolve List.incl_tran.
  Hint Resolve disjoint_trans_lr.
  Hint Resolve changedVariables_upd.
  Hint Resolve unchanged_in_except_disjoint unchanged_in_except_upd unchanged_in_except_shrink.
  Hint Constructors or.
  Hint Resolve sel_upd_eq.

  Hint Constructors RunsTo.
  Hint Constructors runs_loop_partially.
  Hint Resolve unchanged_exprDenote.
  Hint Resolve changedVariables_upd_bwd.
  Hint Resolve unchanged_incl.
  Hint Resolve two_merge_equiv.
  Hint Resolve changed_in_upd_same.

  Hint Extern 12 (unchanged_in _ _ _) => use_changed_unchanged.
  Hint Extern 12 (unchanged_in _ _ _) => use_changed_unchanged'.
  Hint Extern 12 (changed_in _ _ _) => use_changed_trans2.
  Hint Extern 12 (changed_in _ _ _) => use_changed_incl.
  Hint Extern 12 => condition_solver'.
  Hint Extern 12 (unchanged_in _ _ _) => use_unchanged_in_symm.
  Hint Extern 12 (changed_in _ _ _) => use_changed_in_symm.

  Hint Resolve runs_loop_partially_finish.
  Hint Resolve exprDenote_disjoint.
  Hint Resolve RunsTo_footprint.

  Hint Extern 12 (_ = _) => condition_solver.

  Ltac use_unchanged_exprDenote :=
    match goal with
      |- exprDenote ?E _ = exprDenote ?E _ => eapply unchanged_exprDenote; solve [eauto]
    end.
  Hint Extern 12 => use_unchanged_exprDenote.

  Hint Resolve incl_tempChunk2.

  Ltac inv_Safe :=
    match goal with
      H : Safe _ _ _ |- _ => inversion H
    end.

  Ltac break_st := unfold st in *; repeat break_pair; simpl in *.

  Ltac use_Safe_immune :=
    match goal with
      H : RunsTo _ _ _ _, H2 : context [RunsTo _ _ _ _ -> Safe _ _ _] |- _ => eapply H2 in H; break_st; eapply Safe_immune
    end.

  Ltac change_RunsTo :=
    match goal with
      H : RunsTo _ _ (?VS1, ?ARRS) _, H2 : changed_in ?VS2 ?VS1 _ |- _ => 
        generalize H; eapply RunsTo_immune with (vs1' := (VS2, ARRS)) in H; intros
    end.

  Definition equiv (a b : Heap) := fst a %= fst b /\ forall e, e %in fst a -> snd a e = snd b e.

  Infix "%%=" := equiv (at level 70, no associativity).

  Lemma disjoint_cons : forall A a (e : A) b, ~In e a -> disjoint a b -> disjoint a (e :: b).
    unfold disj; intros; simpl; intuition; eauto.
  Qed.

  Lemma disjoint_disj : forall A (a : list A) b, disjoint a b -> disj a b.
    unfold disj, disj; eauto.
  Qed.

  Lemma del_not_in : forall s e, ~ e %in s %- e.
    unfold mem, del; intros; intuition.
  Qed.

  Ltac is_reg t r :=
    match t with
      | _ # r => idtac
      | Regs _ r => idtac
    end.

  Ltac sp_solver' := 
    match goal with
      |- ?A = ?B => is_reg A Sp; is_reg B Sp; pattern_r; rewriter_r
    end.

  Hint Extern 12 => sp_solver'.

  Ltac use_disjoint_trans :=
    match goal with
      H : disjoint ?A ?B |- disjoint ?C _ =>
        match A with context [ C ] =>
          eapply (@disjoint_trans_lr _ A B C _ H); [ | eapply List.incl_refl ]
        end 
    end.

  Hint Resolve del_not_in.
  Hint Resolve temp_in_array.
  Hint Resolve temps_not_in_array.
  Hint Resolve true_false_contradict.

  Ltac to_tempOf :=
    replace "!!" with (tempOf 1) in * by eauto;
      replace "!" with (tempOf 0) in * by eauto.

  Lemma del_add : forall s e, e %in s -> s %- e %+ e %= s.
    clear; intros.
    set (s %- e).
    eapply equiv_symm.
    eapply del_to_add.
    eauto.
    unfold s0; eauto.
  Qed.

  Hint Resolve le_n_S.

  Ltac use_disjoint_trans' :=
    match goal with
      H : disjoint ?A ?B |- disjoint ?C _ =>
        match A with context [ C ] =>
          eapply (@disjoint_trans_lr _ A B C _ H)
        end 
    end.

  Hint Resolve Safe_cond_true Safe_cond_false.

  Ltac decide_constructor :=
    match goal with
      H : evalCond _ _ _ _ _ = Some ?B |- RunsTo (Syntax.If _ _ _) _ _ =>
        match B with
          | true => econstructor 6
          | false => econstructor 7
        end
    end.

  Hint Extern 1 => decide_constructor.

  Hint Resolve runs_loop_partially_body_safe.

  Hint Resolve Safe_immune.

  Ltac tempOf_solver :=
    match goal with
      H : List.incl (tempVars _) ?VARS |- In (tempOf ?N) ?VARS =>
        eapply In_incl; [eapply temp_in_array with (n := S N); omega | eapply incl_tran with (2 := H) ]
    end.

  Hint Extern 1 => tempOf_solver.

  Ltac incl_tran_tempVars :=
    match goal with
      H : List.incl (tempVars _) ?VARS |- List.incl (tempVars _) ?VARS => eapply incl_tran with (2 := H)
    end.

  Hint Extern 1 => incl_tran_tempVars.

  Ltac clear_step := try clear_imports; step auto_ext.

  Ltac in_solver :=
    match goal with
      H : Safe _ _ (_, ?ARRS) |- _ %in fst ?ARRS => rewriter; inv_Safe
    end.

  Hint Extern 1 => in_solver.

  Ltac use_Safe_immune2 :=
    match goal with
      | H : Safe _ ?S_H (?VS1, ?ARRS), H2 : changed_in ?VS1 ?VS2 _ |- Safe _ ?S_G (?VS2, ?ARRS) =>
        match S_H with
          context [ S_G ] => eapply (@Safe_immune _ S_G VS1 VS2 ARRS); [ | simpl; use_changed_unchanged; use_disjoint_trans']
        end
      | H : Safe _ (Syntax.Seq ?A ?B) ?V, H2 : RunsTo _ ?A ?V ?V' |- Safe _ ?B _ => break_st; rewriter; eapply Safe_immune
      | H : Safe _ (While ?E ?B) _, H2 : runs_loop_partially ?E ?B _ _ |- Safe _ ?B _ => break_st; rewriter; eapply Safe_immune; [ eapply (@runs_loop_partially_body_safe _ _ _ _ _ H2) | ]; [ try use_Safe_immune2 | .. ]
    end.

  Lemma Safe_seq_first : forall fs a b v, Safe fs (Syntax.Seq a b) v -> Safe fs a v.
    intros; inv_Safe; eauto.
  Qed.

  Hint Resolve Safe_seq_first.

  Lemma unchanged_in_refl : forall vs vars, unchanged_in vs vs vars.
    unfold unchanged_in; eauto.
  Qed.

  Hint Resolve unchanged_in_refl.

  Lemma Safe_seq_second : forall fs a b v v', Safe fs (Syntax.Seq a b) v -> RunsTo fs a v v' -> Safe fs b v'.
    intros; inv_Safe; use_Safe_immune; eauto.
  Qed.

  Hint Resolve Safe_seq_second.

  Ltac change_RunsTo_arrs :=
    match goal with
      H : RunsTo _ ?S (?VS, ?ARRS1) _ |- RunsTo _ ?S (?VS, ?ARRS2) _ => replace ARRS2 with ARRS1
    end.

  Hint Extern 1 => change_RunsTo_arrs.

  Ltac extend_runs_loop_partially :=
    match goal with
      H : runs_loop_partially _ ?E ?B ?V (?VS, _), H2 : RunsTo _ ?B (?VS, _) ?V'' |- runs_loop_partially _ ?E ?B ?V _ =>
        eapply (@LoopPartialStep _ _ _ _ _ V'' H)
    end.

  Ltac pre_descend := first [change_RunsTo | auto_apply_in runs_loop_partially_finish; [change_RunsTo | ..] ]; open_hyp; break_st.

  Ltac arrays_eq_solver :=
    match goal with
      |- ?A = _ =>
      match type of A with
        Heap => simpl in *; congruence
      end
    end.

  Ltac choose_changed_unchanged :=
    match goal with
      H : disjoint ?A ?B |- unchanged_in _ _ ?C =>
        match A with
          context [ C ] => eapply (@changed_unchanged _ _ B _)
        end
    end.

  Ltac iter_changed_discharger := first [eassumption | eapply changedVariables_incl; [eassumption | ..] | eapply changedVariables_upd_fwd | eapply changedVariables_incl; [eapply changedVariables_upd_fwd | ..] ].

  Ltac iter_changed := repeat first [iter_changed_discharger | eapply changed_trans_l].

  Ltac format_solver :=
    match goal with
      |- _ = exprDenote _ _ ^+ $4 ^* exprDenote _ _ =>
      rewriter; erewrite changed_in_inv by eauto; rewrite sel_upd_eq by eauto; rewriter; repeat (f_equal; try (eapply unchanged_exprDenote; choose_changed_unchanged; iter_changed))
    end.

  Opaque List.incl.

  Lemma changed_in_upd_eq : forall vs1 vs2 vars s val1 val2,
    changed_in vs1 vs2 vars ->
    val2 = val1 ->
    changed_in (upd vs1 s val1) (upd vs2 s val2) vars.
    intros; rewriter; eauto.
  Qed.

  Hint Resolve changed_in_upd_eq.

  Ltac use_changed_in_upd_same :=
    match goal with
      |- changed_in (upd _ ?S _) (upd _ ?S _) _ => eapply changed_in_upd_same; iter_changed
    end.

  Ltac auto_unfold :=
    repeat match goal with
             t := _ |- _ => unfold t in *; clear t
           end.

  Hint Resolve del_add.

  Hint Resolve equiv_symm.

  Ltac max_2_plus :=
    match goal with
      |- (max _ _ >= 2 + _)%nat => simpl
    end.

  Hint Extern 1 => max_2_plus.

  Ltac tempOf_neq :=
    match goal with
      |- ~ (tempOf _ = tempOf _) => discriminate
    end.

  Hint Extern 1 => tempOf_neq.

  Ltac not_in_solver :=
    match goal with 
      H : ?ARRS = _ |- ~ _ %in fst ?ARRS => rewriter
    end.

  Ltac no_question_mark :=
    match goal with
      |- ?T => match T with T => idtac end
    end.

  Ltac upd_chain_solver :=
    match goal with
      H1 : changed_in _ _ _, H2 : changed_in (upd _ _ _) _ _, H3 : changed_in (upd _ _ _) _ _ |- changed_in _ _ _ => no_question_mark; simpl; iter_changed
    end.

  Ltac rv_length_solver :=
    match goal with
      H : Regs ?ST Rv = natToW (length _) |- Regs ?ST Rv = natToW (length _) => rewriter
    end.

  Hint Extern 1 => rv_length_solver.

  Ltac arrays_eq_solver2 :=
    match goal with
      H : ?A = _ |- ?A = _ =>
        match type of A with
          Heap => rewriter
        end
    end.

  Hint Resolve RunsToRelax_loop_false.

  Hint Constructors Safe.
  Lemma Safe_cond_true_k : forall fs e t f k v, 
    Safe fs (Syntax.If e t f;: k) v ->
    wneb (v[(e)]) $0 = true ->
    Safe fs (t;: k) v.
    inversion 1; intros; econstructor; eauto.
  Qed.
  Hint Resolve Safe_cond_true_k.
  Lemma Safe_cond_false_k : forall fs e t f k v, 
    Safe fs (Syntax.If e t f;: k) v ->
    wneb (v[(e)]) $0 = false ->
    Safe fs (f;: k) v.
    inversion 1; intros; econstructor; eauto.
  Qed.
  Hint Resolve Safe_cond_false_k.

  Hint Extern 1 => use_disjoint_trans''.

  Ltac change_rp :=
    match goal with
      H : ?SPECS (sel ?VS1 "rp") = Some _ |- ?SPECS (sel ?VS2 "rp") = Some _ =>
        replace (sel VS2 "rp") with (sel VS1 "rp") by (symmetry; eapply changed_in_inv; [ eauto | ]; eapply in_tran_not; [ | eauto ]; eapply incl_tran; [ | eassumption ]; eauto)
    end.
  Local Notation "'tmps' s" := (tempVars (depth s)) (at level 60).
  Local Notation "'etmps' s" := (tempVars (edepth s)) (at level 60).
  Local Notation agree_in := unchanged_in.
  Local Notation agree_except := changed_in.
  Local Notation "b [ vars => c ]" := (merge c b vars) (no associativity, at level 60).
  Infix "==" := VariableLemmas.equiv.
  Local Notation "v1 =~= v2 [^ except ]" := (st_agree_except v1 v2 except) (no associativity, at level 60).

  Local Notation "fs -:- v1 -- s --> v2" := (RunsTo fs s v1 v2) (no associativity, at level 60).

  Hint Resolve Max.max_lub.

  Lemma st_agree_except_refl : forall v ex, v =~= v [^ex].
    unfold st_agree_except; eauto.
  Qed.
  Hint Resolve st_agree_except_refl.

  Hint Resolve RunsToRelax_cond_true'.
  Hint Resolve RunsToRelax_cond_false'.
  Hint Resolve RunsToRelax_cond_true RunsToRelax_cond_false.

  Hint Unfold st_agree_except.

  Local Notation "v [ e ]" := (exprDenote e v) (no associativity, at level 60).
  Lemma in_not_in_ne : forall A ls (a b : A), In a ls -> ~ In b ls -> a <> b.
    intuition.
  Qed.

  Lemma Safe_assoc_left : forall fs a b c v, Safe fs (a;: b;: c) v -> Safe fs (a;: (b;: c)) v.
    clear; intros; inv_Safe; subst; inversion H; subst; econstructor; [ | intros; econstructor ].
    eauto.
    eauto.
    eauto.
  Qed.
  Ltac true_not_false :=
    match goal with
      H1 : ?A = true, H2 : ?A = false |- _ => eapply Bool.eq_true_false_abs in H1; intuition
    end.
  Hint Extern 1 => true_not_false.
  Lemma Safe_loop_true : forall fs e b v,
    Safe fs (While e b) v ->
    wneb (v[(e)]) $0 = true ->
    Safe fs (b;: While e b) v.
    intros.
    inv_Safe.
    unfold statement0 in *.
    rewrite <- H2 in *.
    eauto.
    eauto.
  Qed.
  Hint Resolve Safe_loop_true.
  Hint Resolve RunsTo_loop_true.
  Lemma Safe_loop_true_k : forall fs e b k v, 
    Safe fs (While e b;: k) v ->
    wneb (v[(e)]) $0 = true ->
    Safe fs (b;: (While e b;: k)) v.
    intros.
    inv_Safe.
    subst.
    inversion H3; try (unfold vals in *; congruence).
    subst b.
    subst v.
    econstructor.
    eauto.
    intros.
    econstructor; eauto.
  Qed.
  Hint Resolve Safe_loop_true_k.
  Local Notation agree_except_trans := changedVariables_trans.

  Hint Resolve RunsToRelax_seq_bwd.

  Hint Resolve RunsToRelax_loop_true.

  Hint Resolve RunsToRelax_loop_true_k.

  Hint Resolve Safe_assoc_left.

  Hint Resolve RunsToRelax_skip.

  Lemma mult_S_distr : forall a b, a * S b = a + a * b.
    intros; ring.
  Qed.

  Opaque star. (* necessary to use eapply_cancel *)

  Ltac eapply_cancel h specs st := let HP := fresh in let Hnew := fresh in
    evar (HP : HProp); assert (interp specs (![HP] st)) as Hnew;
      [ | eapply h in Hnew; [ | clear Hnew .. ] ]; unfold HP in *; clear HP; 
        [ solve [try clear_imports; repeat hiding ltac:(step auto_ext) ] | .. ].

  Ltac transit := 
    match goal with
      | H_interp : interp _ _, H : _ |- _ => eapply H in H_interp; clear H
      | H_interp : interp ?SPECS (![_] ?ST), H : context [interp _ (![_] ?ST) -> _] |- _ => eapply_cancel H SPECS ST; clear H H_interp
    end.

  Ltac try_post :=
    try match goal with
      H_interp : interp _ ?P |- _ =>
        match P with
          | context [ Exists ] => post
        end
    end.

  Lemma pack_pair' : forall A B (x : A * B), (let (x, _) := x in x, let (_, y) := x in y) = x.
    destruct x; simpl; intuition.
  Qed.

  Lemma fold_second : forall A B (p : A * B), (let (_, y) := p in y) = snd p.
    destruct p; simpl; intuition.
  Qed.

  Lemma fold_first : forall A B (p : A * B), (let (x, _) := p in x) = fst p.
    destruct p; simpl; intuition.
  Qed.

  Ltac post_step := repeat first [ rewrite pack_pair' in * | rewrite fold_second in * | rewrite fold_first in *].

  Ltac not_mem_rv INST := 
    match INST with
      | context [LvMem ?LOC] =>
        match LOC with
          | context [Rv] => fail 2
          | _ => idtac
        end
      | _ => idtac
    end.

  Ltac pre_eval_auto := 
    repeat 
      match goal with
        | H_eval : evalInstrs _ ?ST ?INST = _, H_interp : interp _ (![?P] (_, ?ST)) |- _ =>
          match INST with
            context [ Rv ] => 
            match goal with
              H_rv : Regs ST Rv = _ |- _ => not_mem_rv INST; post_step; generalize dependent H_rv
            end
          end
        | H_eval : evalInstrs _ ?ST ?INST = _, H_interp : interp _ (![?P] (_, ?ST)) |- _ =>
          match P with
            context [ is_heap _ ?HEAP ] => 
            match goal with
              H_heap : HEAP = _ |- _ => post_step; generalize dependent H_heap
            end
          end
      end.

  Ltac evaluate_hints hints :=
    match goal with
      H : evalInstrs _ ?ST _ = _ |- _ => generalize dependent H; evaluate hints; intro; evaluate auto_ext
    end.

  Ltac my_evaluate hints :=
    match goal with
      | H: interp _ (![_](_, ?ST)), H_eval: evalInstrs _ ?ST ?INST = _ |- _  =>
        match INST with
          | context [LvMem (Reg Rv) ] => evaluate_hints hints
          | _ => pre_eval_auto; evaluate hints
        end
    end.

  Ltac simpl_sp :=
    repeat match goal with
             H : (_, _) # Sp = _ |- _ => simpl in H
           end.

  Ltac fold_length := 
    change (fix length (l : list string) : nat :=
      match l with
        | nil => 0
        | _ :: l' => S (length l')
      end) with (@length string) in *.

  Lemma fold_4S : forall n, (S (S (S (S (4 * n))))) = (4 + (4 * n)).
    eauto.
  Qed.

  Ltac not_exist t :=
    match goal with
      | H : t |- _ => fail 1
      | |- _ => idtac
    end.

  Ltac assert_new t := not_exist t; assert t.

  Ltac assert_new_as t name := not_exist t; assert t as name.

  Definition heap_tag layout arrs (_ _ : W) := is_heap layout arrs.

  Ltac set_all t := let name := fresh "t" in set (name := t) in *.

  Ltac clear_bad H_interp s :=
    repeat 
      match goal with
        | H : context [changed_in _ _ _] |- _ => generalize H; clear H
        | H : Regs ?ST Rv = _  |- _ => not_eq ST s; generalize H; clear H
        | H : context [Safe _ _ _] |- _ => not_eq H H_interp; generalize H; clear H
      end.

  Ltac simpl_interp :=
    match goal with
      | H: interp _ (![_](_, ?ST)), H_eval: evalInstrs _ ?ST _ = _ |- _  =>
        simpl in H; try rewrite fold_4S in H
    end.

  Ltac pre_eval :=
    match goal with
      | H: interp _ (![_](_, ?ST)), H_eval: evalInstrs _ ?ST _ = _ |- _  =>
        try clear_imports; HypothesisParty H; prep_locals; clear_bad H ST;
          simpl_interp; simpl_sp; try rewrite fold_4S in *
    end.

  Ltac post_eval := intros; try fold (@length W) in *; post_step; try fold_length; try rewrite fold_4S in *.

  Definition heap_to_split layout arrs (_ : W) := is_heap layout arrs.

  Ltac cond_gen := try
    match goal with
      | H_interp : interp _ (![_](_, ?ST)), H_eval : evalInstrs _ ?ST ?INST = _ |- _ =>
        match INST with
          | context [variablePosition ?vars ?s] => assert_new (In s vars)
          | context [variableSlot ?s ?vars] => assert_new (In s vars)
        end; [ clear H_eval .. | cond_gen ]
    end.

  Lemma star_comm : forall a b, a * b ===> b * a.
    clear; intros; sepLemma.
  Qed.

  Lemma star_cancel_left : forall a b c, b ===> c -> a * b ===> a * c.
    clear; intros; sepLemma.
  Qed.

  Lemma star_cancel_right : forall a b c, b ===> c -> b * a ===> c * a.
    clear; intros; sepLemma.
  Qed.

  Lemma equiv_symm : forall a b, a %%= b -> b %%= a.
    clear; unfold equiv, MHeap.MSet.equiv; simpl; intros; firstorder.
  Qed.

  Hint Resolve equiv_symm.

  Definition trigger A (_ : A) := True.

  Ltac trigger_bwd Hprop :=
    match Hprop with
      context [ is_heap _ ?ARRS ] =>
      assert (trigger ARRS) by (unfold trigger; trivial)
    end.

  Lemma equiv_refl : forall a, a %%= a.
    clear; unfold equiv; intros; firstorder.
  Qed.
  Hint Resolve equiv_refl.

  Hint Resolve in_not_in_ne.

  Hint Resolve RunsTo_RunsToRelax.

  Ltac apply_save_in lemma hyp := generalize hyp; eapply lemma in hyp; intro.

  Ltac assert_sp P Q H_sp :=
    match P with
      context [ locals _ _ _ ?P_SP ] =>
      match Q with
        context [ locals _ _ _ ?Q_SP] =>
        assert (Q_SP = P_SP) as H_sp
      end
    end.

  Ltac set_heap_goal :=
    match goal with
      |- context [ is_heap _ ?ARRS ] => set_all ARRS
    end.

  Ltac set_heap_hyp :=
    match goal with
      H : context [ is_heap _ ?ARRS ] |- _ => set_all ARRS
    end.

  Ltac set_array_hyp :=
    match goal with
      H : context [ array ?ARR ?PTR ] |- _ => set_all ARR; set_all PTR
    end.

  Lemma not_in_remove_arr : forall arr arrs, ~ arr %in fst (MHeap.remove arrs arr).
    intros; unfold MHeap.remove; simpl; eauto.
  Qed.

  Hint Resolve not_in_remove_arr.

  Hint Resolve in_tran_not.

  Lemma vars_require_imply : forall vars s1 s2, 
    vars_require vars s1 -> 
    List.incl (footprint s2) (footprint s1) ->
    depth s2 <= depth s1 ->
    vars_require vars s2.
    admit.
    (* clear; unfold vars_require; intros; openhyp; descend; eauto. *)
  Qed.

  Local Notation "'e_vars_require'" := CompileExpr.expr_vars_require.

  Lemma vars_require_imply_e : forall vars s e base, vars_require vars s -> List.incl (varsIn e) (footprint s) -> (base + edepth e <= depth s)%nat -> e_vars_require vars e base.
    admit.
    (* clear; unfold vars_require, CompileExpr.expr_vars_require; simpl; intuition; eauto. *)
  Qed.

  Ltac unfold_copy_vars_require :=
    match goal with
      H : vars_require _ _ |- _ => generalize H; unfold vars_require in H; simpl in H; intro; openhyp
    end.

  Ltac protect_hyps :=
    repeat 
      match goal with
        | H : agree_except _ _ _ |- _ => generalize dependent H
        | H : vars_require _ _ |- _ => generalize dependent H
        | H : Regs _ Rv = _ |- _ => generalize dependent H
        | H : _ %in _ |- _ => generalize dependent H
        | H : Safe _ _ _ |- _ => generalize dependent H
        | H : RunsToRelax _ _ _ _ |- _ => generalize dependent H
      end.

  Ltac changed_unchanged_disjoint :=
    match goal with
      H : disjoint ?A ?B |- agree_in _ _ _ => eapply changed_unchanged with (changed := B)
    end.

  Ltac changed_in_inv_disjoint := 
    match goal with
      H : disjoint ?A ?B |- _ = _ => eapply changed_in_inv with (vars := B)
    end.

  Ltac change_rp' :=
    match goal with
      H : ?SPECS (sel ?VS1 "rp") = Some _ |- ?SPECS (sel ?VS2 "rp") = Some _ =>
        replace (sel VS2 "rp") with (sel VS1 "rp"); [ | symmetry; changed_in_inv_disjoint; [ | eapply in_tran_not; [ | eassumption ] ] ]
    end.

  Ltac equiv_solver :=
    match goal with
      |- _ %%= MHeap.upd ?ARRS _ _ => auto_unfold; no_question_mark; rewriter; unfold MHeap.upd, MHeap.remove, equiv; simpl; to_tempOf; split; [ | intros; repeat f_equal; erewrite changed_in_inv by eauto; rewrite sel_upd_ne by eauto; erewrite changed_in_inv by eauto; rewrite sel_upd_eq by eauto]
    end.

  Ltac set_vs_hyp :=
    match goal with
      H : context [ locals _ ?VS _ _ ] |- _ => set_all VS
    end.

  Ltac equiv_solver2 :=
    match goal with
      |- _ %%= MHeap.upd ?ARRS _ _ => auto_unfold; no_question_mark; rewriter; unfold MHeap.upd, MHeap.remove, equiv; simpl; to_tempOf; split; [ | intros; repeat f_equal]
    end.

  Lemma upd_sel_equiv : forall d i i', MHeap.sel (MHeap.upd d i (MHeap.sel d i)) i' = MHeap.sel d i'.
    clear; intros; destruct (weq i i').
    rewrite MHeap.sel_upd_eq; congruence.
    rewrite MHeap.sel_upd_ne; congruence.
  Qed.

  Ltac upd_chain_solver2 :=
    match goal with
      H1 : changed_in _ _ _, H2 : changed_in (upd _ _ _) _ _ |- changed_in _ _ _ => no_question_mark; simpl; iter_changed
    end.

  Ltac vars_require_solver :=
    match goal with
      | H : vars_require _ _ |- vars_require _ _ => eapply vars_require_imply; repeat (simpl; eauto)
      | H : vars_require _ _ |- e_vars_require _ _ _ => eapply vars_require_imply_e; repeat (simpl; eauto)
    end.

  Ltac RunsToRelax_solver :=
    match goal with
      H : _ ~:~ _ ~~ ?S ~~> ?ST |- _ ~:~ _ ~~ ?S ~~> ?ST =>
        eapply RunsToRelax_immune; [ eassumption | unfold st_agree_except; repeat split .. | ]
    end.

  Ltac Safe_cond_solver :=
    match goal with
      H : Safe _ (Syntax.If _ _ _;: _) (?ST1, _) |- Safe _ _ _ =>
        eapply Safe_immune with (vs1 := ST1); [ | use_changed_unchanged; simpl; eapply disjoint_trans_lr]
    end.

  Ltac RunsToRelax_seq_solver :=
    match goal with
      H : _ ~:~ _ ~~ _;: (_;: _) ~~> _ |- _ ~:~ _ ~~ _;: _;: _ ~~> _ =>
        eapply RunsToRelax_assoc_left; simpl
    end.

  Ltac rv_solver' :=
    match goal with
      | H:Regs ?ST Rv = _ |- Regs ?ST Rv = _ => pattern_l; rewriter
      | H:Regs ?ST Rv = _ |- _ = Regs ?ST Rv => pattern_r; rewriter
      | H:_ = Regs ?ST Rv |- Regs ?ST Rv = _ => pattern_l; rewriter_r
      | H:_ = Regs ?ST Rv |- _ = Regs ?ST Rv => pattern_r; rewriter_r
    end.

  Ltac rp_upd_solver :=
    match goal with
      |- ?A = Some _ =>
      match A with
        context [ upd ] =>
        match A with
          context [ "rp" ] =>
          rewrite sel_upd_ne; [ change_rp' | eapply in_not_in_ne ]
        end
      end
    end.

  Local Notation agree_except_symm := changedVariables_symm.

  Ltac RunsToRelax_Stuff_solver :=
    eapply RunsToRelax_seq_bwd; [ | eassumption | eauto ];
      eapply RunsToRelax_immune; [ eapply RunsTo_RunsToRelax; econstructor; eauto | .. ];
        [ | unfold st_agree_except; repeat split; simpl | ];
        unfold st_agree_except; simpl; intuition eauto.

  Ltac do_RunsToRelax_Read_Write_solver := eapply RunsToRelax_seq_bwd; [ | eassumption | ..]; [ eapply RunsToRelax_immune; [ eapply RunsTo_RunsToRelax; econstructor; eauto | .. ]; [ | unfold st_agree_except; repeat split; simpl; eapply agree_except_symm | ] | ].

  Ltac freeable_goodSize_solver :=
    match goal with
      | |- freeable _ _ => auto_unfold; rewrite upd_length in *
      | |- goodSize _ => auto_unfold; rewrite upd_length in *
    end.

  Ltac equiv_solver2' :=
    match goal with
      |- _ %%= MHeap.upd _ _ _ =>
      equiv_solver2; [ | unfold MHeap.sel; symmetry; eapply upd_sel_equiv ]
    end.

  Ltac pre_eauto := try first [
    use_disjoint_trans' |
    use_Safe_immune2 |
    extend_runs_loop_partially |
    use_changed_in_eval |
    arrays_eq_solver |
    format_solver |
    use_changed_in_upd_same |
    not_in_solver |
    equiv_solver |
    upd_chain_solver |
    arrays_eq_solver2
    ].

  Lemma mult_S_distr_inv : forall a b, a + a * b = a * S b.
    intros; ring.
  Qed.

  Lemma wplus_wminus : forall (a b : W), a ^+ b ^- b = a.
    intros; words.
  Qed.

  Ltac change_locals ns' avail' :=
    match goal with
      H : context[locals ?ns ?vs ?avail ?p] |- _ =>
        let offset := eval simpl in (4 * List.length ns) in
          change (locals ns vs avail p) with (locals_call ns vs avail p ns' avail' offset) in H; assert (ok_call ns ns' avail avail' offset)%nat
    end.

  Ltac change_sp :=
    match goal with
      Hinterp : interp _ (![ ?P ] (_, ?ST)), Heval : evalInstrs _ ?ST _ = _ |- _ =>
        match P with
          context [ Regs ?ST2 Sp ] => not_eq ST ST2; replace (Regs ST2 Sp) with (Regs ST Sp) in Hinterp by words
        end
    end.

  Ltac generalize_sp :=
    repeat match goal with
             H : Regs _ Sp = Regs _ Sp |- _ => generalize dependent H
           end.

  Ltac agree_in_solver :=
    match goal with
      |- agree_in _ _ _ => changed_unchanged_disjoint; [ iter_changed; incl_app_solver | .. ]
    end.

  Ltac use_Safe_immune' :=
    match goal with
      H : Safe _ ?S (_, ?A) |- Safe _ ?S (_, ?A) =>
        eapply Safe_immune; [ eassumption | .. ]; agree_in_solver
    end.

  Ltac ok_call_solver :=
    match goal with
      |- ok_call _ _ _ _ _ =>
      repeat split; simpl; eauto; NoDup
    end.

  Ltac myPost := autorewrite with sepFormula in *; unfold substH in *; simpl in *.

  Ltac clear_or :=
    repeat match goal with 
             H : _ \/ _ |- _ => clear H 
           end.

  Ltac simpl_vars :=
    repeat match goal with 
             | H : context [footprint _] |- _ => progress simpl in H
             | H : context [tmps _] |- _ => progress simpl in H
           end.

  Lemma ignore_premise : forall pc state specs (P Q : PropX pc state),
    interp specs Q
    -> interp specs (P ---> Q).
    intros; apply Imply_I; apply interp_weaken; assumption.
  Qed.

  Ltac step_himp_helper :=
    match goal with
      |- himp _ ?A ?B =>
      match B with
        context [locals ?VARS ?VS1 _ ?SP1] =>
        match A with
          context [locals VARS ?VS2 _ ?SP2] =>
          match A with
            context [locals ?VARS2 _ _ ?SP3] =>
            not_eq VARS VARS2; replace SP1 with SP2; replace SP3 with (SP2 ^+ natToW (4 * length VARS)); replace VS1 with VS2
          end
        end
      end
    end.

  Ltac sel_eq_solver :=
    match goal with
      |- sel _ ?V = sel _ ?V => symmetry; changed_in_inv_disjoint
    end.

  Ltac pre_eauto2 := try first [
    ok_call_solver |
    use_Safe_immune2 |
    (format_solver; incl_app_solver) |
    equiv_solver |
    vars_require_solver |
    RunsToRelax_solver | 
    rp_upd_solver |
    change_rp' |
    rv_solver' |
    Safe_cond_solver |
    RunsToRelax_seq_solver |
    freeable_goodSize_solver |
    changed_unchanged_disjoint |
    equiv_solver2' |
    use_Safe_immune' |
    sel_eq_solver
    ].

  Lemma four_out : forall n, 4 * (S (S (S n))) = 4 * 3 + 4 * n.
    intros; omega.
  Qed.

  Ltac eval_instrs hints :=
    match goal with
      | H: interp _ (![_](_, ?ST)), H_eval: evalInstrs _ ?ST _ = _ |- _  =>
        cond_gen; [ .. | let P := fresh "P" in
          try match goal with
                | [ _ : context[Safe ?fs _ _] |- _ ] => set (P := Safe fs) in *
              end;
          pre_eval;
          try match goal with
                | [ H : _ = Regs ?X Rv, H' : _ = Regs ?X Rv |- _ ] => generalize dependent H'
              end;
          my_evaluate hints;
          try subst P;
            post_eval; clear H_eval]
    end.

  Ltac clear_specs :=
    repeat
      match goal with
        | H : interp ?SPECS_H _ |- context [simplify ?SPECS _ _] => not_eq SPECS_H SPECS; clear H
        | H : interp ?SPECS_H _ |- context [interp ?SPECS _] => not_eq SPECS_H SPECS; clear H
      end.

  Ltac pre_eval_statement := intros; open_hyp; try_post.

  Ltac eval_statement := pre_eval_statement; transit; open_hyp; try_post.

  Ltac eval_step hints := first[eval_statement | try clear_imports; eval_instrs hints].

  Lemma Safe_skip : forall fs k v,
    Safe fs (skip;: k) v
    -> Safe fs k v.
    inversion 1; auto.
  Qed.

  Hint Resolve Safe_skip.

  Hint Extern 1 (agree_in _ _ _) => progress simpl.

  Lemma Safe_loop_false : forall fs e b v k,
    Safe fs (While e b;: k) v ->
    wneb (v[(e)]) $0 = false ->
    Safe fs k v.
    intros; inv_Safe; eauto.
  Qed.

  Hint Resolve Safe_loop_false.

  Ltac changed_in_inv_vars := 
    match goal with
      H : disjoint ?A ?B, H2 : List.incl ?A ?VARS |- _ = _ => eapply changed_in_inv with (vars := VARS)
    end.

  Ltac incl_arg_vars_solver :=
    match goal with
      H : List.incl ?FP ("__arg" :: ?VARS) |- List.incl (?S :: nil) ("__arg" :: ?VARS) => 
        match FP with
          context [S] => eapply incl_tran; [ | eassumption ]
        end
    end.

  Ltac temp_solver :=
    match goal with
      | H : List.incl (tempVars ?N) _ |- List.incl (tempChunk _ _) _ => eapply incl_tran with (m := tempVars N); [eapply incl_tempChunk2; simpl | ]
      | H : List.incl (tempVars ?N) _ |- List.incl (tempOf _ :: nil) _ => eapply incl_tran with (m := tempVars N)
    end.

  Ltac sel_eq_solver2 :=
    match goal with
      |- sel _ ?V = sel _ ?V => symmetry; changed_in_inv_vars; iter_changed; try temp_solver; try eapply in_tran_not; try incl_arg_vars_solver
    end.

  Ltac replace_reserved :=
    match goal with
      H : context [sel ?VS1 S_RESERVED] |- context [sel ?VS2 S_RESERVED] =>
        not_eq VS1 VS2; replace (sel VS2 S_RESERVED) with (sel VS1 S_RESERVED) in *
    end.

  Ltac le_eq_reserved_solver :=
    match goal with
      | |- _ <= wordToNat (sel _ S_RESERVED) => replace_reserved; [ omega | sel_eq_solver2 ]
      | |- _ = wordToNat (sel _ S_RESERVED) => replace_reserved; [ omega | sel_eq_solver2 ]
    end.

  Ltac change_rp'' :=
    try eassumption;     
      match goal with
        H : ?SPECS (sel ?VS1 "rp") = Some _ |- ?SPECS (sel ?VS2 "rp") = Some _ =>
          replace (sel VS2 "rp") with (sel VS1 "rp"); [ | symmetry; changed_in_inv_disjoint; [ | eapply in_tran_not; [ | eauto ] ] ]; [ | iter_changed; try (apply incl_tempChunk2; simpl) | ]
      end.

  Ltac decide_cond t f :=
    match goal with
      | H : _ = Some true |- _ => t
      | H : _ = Some false |- _ => f
    end.

  Ltac decide_cond_safe := decide_cond ltac:(eapply Safe_cond_true_k) ltac:(eapply Safe_cond_false_k).

  Ltac Safe_cond_solver2 :=
    match goal with
      H : Safe _ (Syntax.If _ _ _;: _) (?ST1, _) |- Safe _ _ _ =>
        eapply Safe_immune with (vs1 := ST1); [ decide_cond_safe | use_changed_unchanged; simpl; eapply disjoint_trans_lr]
    end.

  Ltac Safe_loop_solver :=
    match goal with
      |- Safe _ (_ ;: (While _ _ ;: _)) _ => decide_cond ltac:(eapply Safe_loop_true_k) ltac:(eapply Safe_loop_false)
    end.

  Ltac pre_eauto3 := try first [
    ok_call_solver |
    use_Safe_immune2 |
    (format_solver; incl_app_solver) |
    equiv_solver |
    vars_require_solver |
    RunsToRelax_solver | 
    rp_upd_solver |
    change_rp'' |
    rv_solver' |
    Safe_cond_solver2 |
    RunsToRelax_seq_solver |
    freeable_goodSize_solver |
    changed_unchanged_disjoint |
    equiv_solver2' |
    use_Safe_immune' |
    sel_eq_solver2 |
    le_eq_reserved_solver | 
    Safe_loop_solver
    ].

  Ltac smack := to_tempOf; pre_eauto3; info_eauto 7.

  Ltac var_solver :=
    try apply unchanged_in_upd_same; smack; try apply changed_in_upd_same;
      try (upd_chain_solver2; simpl; incl_app_solver); try (apply incl_tempChunk2; simpl); info_eauto 8.

  Ltac pick_vs :=
    (*try match goal with
          | [ x : (settings * state)%type |- _ ] => destruct x; simpl in *
        end;*)
    match goal with
      H : interp ?SPECS (![?P] ?ST) |- context [ (![_] ?ST)%PropX ] =>
        match P with
          context [ locals _ ?VS _ _ ] => let a := fresh in evar (a : Heap); (exists (VS, a)); unfold a in *; clear a
        end
    end.

  Ltac unfold_eval := unfold precond, postcond, inv, expr_runs_to, runs_to_generic in *.

  Ltac preamble := 
    wrap0; unfold_eval; unfold_copy_vars_require; myPost;
    repeat eval_step hints;
      repeat match goal with
               | [ |- vcs _ ] => wrap0;
                 try match goal with
                       | [ x : (settings * state)%type |- _ ] => destruct x
                     end; try eval_step hints;
                 try match goal with
                       | [ H : context[expr_runs_to] |- _ ] =>
                         unfold expr_runs_to, runs_to_generic in H; simpl in H
                     end; try eval_step hints
             end; smack;
      match goal with
        | [ x : (vals * Heap)%type |- _ ] => destruct x; simpl in *
        | [ x : st |- _ ] => destruct x; simpl in *
      end;
      myPost; try (unfold_eval; clear_imports; eval_step auto_ext; var_solver);
        try match goal with
              | [ fs : W -> option Callee
                  |- exists x : W -> option Callee, _ ] =>
                exists fs;
                  match goal with
                    | [ |- _ /\ _ ] => split; [ split; assumption | ]
                  end
            end;
        try match goal with
              | [ |- exists a0 : _ -> PropX _ _, _ ] => eexists
            end;
        pick_vs; descend; try (eauto 2; try solve [ eapply Safe_immune; [ eauto 2 | eauto 8 ] ]);
          clear_or.

  Ltac middle :=
    match goal with
      | [ |- context[is_heap _ ?a] ] => set_heap_goal; try reflexivity
      | [ |- interp _ (![_] _) ] => clear_imports; replace_reserved; [ repeat hiding ltac:(step auto_ext) | .. ]
      | _ => var_solver
    end.

  Ltac do_step := descend; try clear_imports;
    try match goal with
          | [ H : _ ~:~ _ ~~ _ ~~> _ |- interp _ (![_] _ ---> ![_] _)%PropX ] => clear H
        end;
    try match goal with
          | [ |- himp _ ?pre ?post ] =>
            match pre with
              | context[locals _ _ _ ?sp1] =>
                match post with
                  | context[locals _ _ _ ?sp2] =>
                    replace sp2 with sp1 by words
                end
            end
        end;
    hiding ltac:(step auto_ext).

  Ltac stepper := try replace_reserved; [ clear_or; repeat do_step | .. ].

  Ltac solver :=
    match goal with
      | _ => RunsToRelax_Stuff_solver
      | _ => smack
    end.

  Ltac finale := stepper; solver.

  Ltac t := preamble; middle; finale.

  Opaque mult.
  Opaque is_heap.

  Ltac discharge_fs :=
    match goal with
      | [ fs : W -> option Callee
          |- exists x : W -> option Callee, _ ] =>
        exists fs;
          match goal with
            | [ |- _ /\ _ ] => split; [ split; assumption | ]
          end
               end;
          match goal with
            | [ |- exists a0 : _ -> PropX _ _, _ ] => eexists
          end.

  Lemma vars_require_disjoint : forall vars s b n, vars_require vars s -> disjoint (footprint s) (tempChunk b n).
    admit.
  Qed.

  Hint Resolve vars_require_disjoint.

  Lemma vars_require_seq_assoc_left : forall vars s1 s2 k, vars_require vars (s1 ;: s2 ;: k) -> vars_require vars (s1 ;: (s2 ;: k)).
    admit.
  Qed.

  Hint Resolve vars_require_seq_assoc_left.

  Lemma vars_require_seq_part : forall vars s1 s2 k, vars_require vars (s1 ;: s2 ;: k) -> vars_require vars (s2 ;: k).
    admit.
  Qed.

  Hint Resolve vars_require_seq_part.

  Hint Resolve RunsToRelax_assoc_left.

  Lemma vars_require_disjoint_tempVars : forall vars s n, vars_require vars s -> disjoint (footprint s) (tempVars n).
    admit.
  Qed.

  Hint Resolve vars_require_disjoint_tempVars.

  Lemma pack_pair : forall A B (p : A * B), (fst p, snd p) = p.
    intuition.
  Qed.

  Lemma Safe_pair : forall fs s p, Safe fs s p -> Safe fs s (fst p, snd p).
    admit.
  Qed.

  Hint Resolve Safe_pair.

  Lemma reserved_not_in_tempChunk : forall b n, ~ In S_RESERVED (tempChunk b n).
    admit.
  Qed.

  Hint Resolve reserved_not_in_tempChunk.

  Lemma rp_not_in_tempChunk : forall b n, ~ In "rp" (tempChunk b n).
    admit.
  Qed.

  Hint Resolve rp_not_in_tempChunk.

  Lemma vars_require_if_part_true : forall vars e t f k, vars_require vars (Syntax.If e t f ;: k) -> vars_require vars (t ;: k).
    admit.
  Qed.

  Hint Resolve vars_require_if_part_true.

  Lemma vars_require_if_part_false : forall vars e t f k, vars_require vars (Syntax.If e t f ;: k) -> vars_require vars (f ;: k).
    admit.
  Qed.

  Hint Resolve vars_require_if_part_false.

  Lemma vars_require_if_cond : forall vars e t f k, vars_require vars (Syntax.If e t f ;: k) -> e_vars_require vars e 0.
    admit.
  Qed.

  Hint Resolve vars_require_if_cond.

  Ltac replace_sel := try eassumption;     
    match goal with
      H : context [sel ?VS1 ?V] |- context [sel ?VS2 ?V] =>
        not_eq VS1 VS2; replace (sel VS2 V) with (sel VS1 V) in *; try symmetry
    end.

  Hint Resolve changed_in_inv.

  Ltac do_wrap :=
    match goal with
      | [ |- vcs _ ] => wrap0
    end.

  Ltac do_unfold_eval :=
    match goal with
      | [ H : context[expr_runs_to] |- _ ] => unfold_eval
    end.

  Lemma post_ok : forall (s k : Statement) (pre : assert) (specs : codeSpec W (settings * state))
    (x : settings * state),
    vcs (verifCond s k pre) ->
    interp specs (Postcondition (compile s k pre) x) ->
    interp specs (postcond k x).

    unfold verifCond, imply; induction s.

    (* skip *)
    wrap0; unfold_eval; repeat (first [do_wrap | do_unfold_eval | eval_step auto_ext]).
    discharge_fs; descend; try clear_imports; repeat hiding ltac:(step auto_ext); eauto.

    (* seq *)
    wrap0; unfold_eval; repeat (first [do_wrap | do_unfold_eval | eval_step auto_ext]).
    discharge_fs; descend; try clear_imports; repeat hiding ltac:(step auto_ext); eauto.
    eauto.

    (* if-true *)
    wrap0; unfold_eval; repeat (first [do_wrap | do_unfold_eval | eval_step auto_ext]).
    discharge_fs.
    rewrite pack_pair in *.
    pick_vs.
    descend; try clear_imports; repeat hiding ltac:(step auto_ext); post_step.
    simpl; replace_sel; eauto.
    eapply Safe_immune; eauto.
    simpl; replace_sel; eauto.
    eauto 6.
    eauto.
    eauto.

    (* if-false *)
    wrap0; unfold_eval; repeat (first [do_wrap | do_unfold_eval | eval_step auto_ext]).
    discharge_fs.
    rewrite pack_pair in *.
    pick_vs.
    descend; try clear_imports; repeat hiding ltac:(step auto_ext); post_step.
    simpl; replace_sel; eauto.
    eapply Safe_immune; eauto.
    simpl; replace_sel; eauto.
    eauto 6.
    eauto.
    eauto.

    (* while *)
    wrap0; unfold_eval; repeat (first [do_wrap | do_unfold_eval | eval_step auto_ext]).
    myPost.
    discharge_fs; descend; try clear_imports; repeat hiding ltac:(step auto_ext); eauto.

    (* call *)
    admit.

  Qed.

  Ltac unfold_wrap0 := unfold verifCond, imply, CompileExpr.expr_verifCond in *.

  Ltac clear_himp :=
    match goal with
      | [ H : _ ~:~ _ ~~ _ ~~> _ |- interp _ (![_] _ ---> ![_] _)%PropX ] => clear H
    end.

  Ltac stepper' := 
    match goal with
      |- context [locals _ _ _ _] => try replace_reserved; [ clear_or; descend; try clear_imports; try clear_himp; repeat hiding ltac:(step auto_ext) | .. ]
    end.

  Ltac destruct_st :=
    match goal with
      | [ x : (vals * Heap)%type |- _ ] => destruct x; simpl in *
      | [ x : st |- _ ] => destruct x; simpl in *
    end;
    try match goal with
          | [ x : (settings * state)%type |- _ ] => destruct x; simpl in *
        end.

  Ltac smack2 := pre_eauto3; simpl; info_eauto 8.

  Ltac eval_step2 hints :=
    match goal with
      | Hinterp : interp _ (![ ?P ] (_, ?ST)), Heval : evalInstrs _ ?ST ?INSTRS = _ |- _ =>
        match INSTRS with
          | context [ IL.Binop _ (RvLval (LvReg Sp)) Plus _ ] =>
            change_locals ("rp" :: S_RESERVED :: "__arg" :: nil) 0; [ clear Heval |repeat rewrite <- mult_plus_distr_l in *; change_sp; generalize_sp; eval_step hints ]
        end
      | _ => eval_step hints
    end.

  Lemma verifCond_ok : forall s k (pre : assert),
    vcs (verifCond s k pre) -> vcs (VerifCond (compile s k pre)).

    unfold verifCond, imply; induction s.

    (* skip *)
    wrap0; clear_imports; evaluate auto_ext.

    (* seq *)
    wrap0.
    auto_apply; wrap0; unfold_eval; clear_imports.
    repeat eval_step auto_ext.
(*here*)
    try stepper'; solver.

    auto_apply; wrap0; pre_eauto3; auto_apply_in post_ok; wrap0; unfold_wrap0; wrap0; pre_eauto3; unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step hints; try stepper'; solver.

    (* if *)
    wrap0.
    unfold_eval; clear_imports; repeat eval_step hints; try stepper'; solver.
    clear_imports; evaluate auto_ext.

    (* true case *)
    auto_apply; wrap0; pre_eauto3; unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step auto_ext; destruct_st; descend; [ propxFo | propxFo | instantiate (2 := (_, _)); simpl; stepper | .. ]; try stepper'; solver.

    (* false case *)
    auto_apply; wrap0; pre_eauto3; unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step auto_ext; destruct_st; descend; [ propxFo | propxFo | instantiate (2 := (_, _)); simpl; stepper | .. ]; try stepper'; solver.

    (* while *)
    wrap0.
    unfold_eval; clear_imports; repeat eval_step hints; try stepper'; solver.

    unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step auto_ext; destruct_st; descend; [ propxFo | propxFo | instantiate (2 := (_, _)); simpl; stepper | .. ]; try stepper'; smack2.

    clear_imports; unfold evalCond in *; unfold evalRvalue in *; intuition.

    auto_apply_in post_ok.
    unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step auto_ext; destruct_st; descend; [ propxFo | propxFo | instantiate (2 := (_, _)); simpl; stepper' | .. ]; try stepper'; smack2.

    unfold_wrap0; wrap0; pre_eauto3; unfold_eval; clear_imports; unfold_copy_vars_require; post; descend; try stepper'; solver.

    auto_apply; wrap0; pre_eauto3; unfold_eval; clear_imports; unfold_copy_vars_require; post; descend; try stepper'; solver.

    unfold_wrap0 ; wrap0; auto_apply_in post_ok.
    unfold_eval; clear_imports; post; try stepper'; solver.

    unfold_wrap0; wrap0; pre_eauto3; unfold_eval; clear_imports; unfold_copy_vars_require; post; descend; try stepper'; solver.

    (* malloc *)
    wrap0; unfold CompileMalloc.verifCond; wrap0.

    (* free *)
    wrap0; unfold CompileFree.verifCond; wrap0.

    (* len *)
    wrap0; unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step hints; try stepper'; solver.

    (* call *)
    wrap0.

    unfold_eval; clear_imports; unfold_copy_vars_require; myPost; repeat eval_step2 auto_ext; try stepper'; solver.
    unfold_eval; clear_imports; unfold_copy_vars_require; myPost; repeat eval_step2 auto_ext; try stepper'; solver.
    unfold_eval; clear_imports; unfold_copy_vars_require; myPost; repeat eval_step2 auto_ext; try stepper'; solver.
    unfold_eval; clear_imports; unfold_copy_vars_require; myPost; repeat eval_step2 auto_ext; try stepper'; solver.
    unfold_eval; clear_imports; unfold_copy_vars_require; myPost; repeat eval_step2 auto_ext; try stepper'; solver.
    2: unfold_eval; clear_imports; unfold_copy_vars_require; myPost; repeat eval_step2 auto_ext; try stepper'; solver.
    2: unfold_eval; clear_imports; unfold_copy_vars_require; myPost; repeat eval_step2 auto_ext; try stepper'; solver.

    unfold_eval; clear_imports; unfold_copy_vars_require; myPost.
    eval_step2 auto_ext.
    eval_step2 auto_ext.
    eval_step2 auto_ext.
    2: solver.
    solver.
    2: solver.
    eval_step2 auto_ext.
    2: solver.
    eval_step2 auto_ext.
    solver.

    change (locals ("rp" :: S_RESERVED :: "__arg" :: vars) (upd x10 (tempOf 1) (Regs x0 Rv)) x7 (Regs x0 Sp))
      with (locals_call ("rp" :: S_RESERVED :: "__arg" :: vars) (upd x10 (tempOf 1) (Regs x0 Rv)) x7
        (Regs x0 Sp)
        ("rp" :: S_RESERVED :: "__arg" :: nil) (x7 - 3)
        (S (S (S (S (S (S (S (S (S (S (S (S (4 * Datatypes.length vars)))))))))))))) in *.
    assert (ok_call ("rp" :: S_RESERVED :: "__arg" :: vars) ("rp" :: S_RESERVED :: "__arg" :: nil)
      x7 (x7 - 3)
      (S (S (S (S (S (S (S (S (S (S (S (S (4 * Datatypes.length vars))))))))))))))%nat.
    split.
    simpl; omega.
    split.
    simpl; omega.
    split.
    NoDup.
    simpl; omega.
    
    rename H15 into Hi.
    rename H16 into H15.
    rename H17 into H16.
    rename H18 into H17.
    rename H19 into H18.
    rename H20 into H19.
    rename H21 into H20.
    rename H22 into H21.
    rename H23 into H22.
    rename H24 into H23.
    rename H25 into H24.
    rename H26 into H25.
    rename H27 into H26.
    rename H28 into H27.
    rename H29 into H28.
    rename H30 into H29.
    rename H31 into H30.
    rename H32 into H31.

    inversion H18; clear H18; subst.
    inversion H34; clear H34; subst.
    (*here*)
    specialize (Imply_sound (H3 _ _ _ ) (Inj_I _ _ H32)); propxFo.
    repeat match goal with
             | [ H : context[exprDenote] |- _ ] => generalize dependent H
             | [ H : context[Build_callTransition] |- _ ] => generalize dependent H
             | [ H : agree_except _ _ _ |- _ ] => generalize dependent H
           end.
    change (string -> W) with vals in *.
    generalize dependent H31.
    simpl in H25.
    evaluate auto_ext.
    intro.

    Lemma fold_4S' : forall n, S (S (S (S (S (S (S (S (S (S (S (S (4 * n)))))))))))) = 4 * S (S (S n)).
      intros; omega.
    Qed.
    
    rewrite fold_4S' in *.

    cond_gen.
    solver.
    let P := fresh "P" in
      match goal with
        | [ _ : context[Safe ?fs _ _] |- _ ] => set (P := Safe fs) in *
      end.
    assert (~In "rp" (S_RESERVED :: "__arg" :: vars)) by (simpl; intuition).
    prep_locals.
    replace (Regs x0 Sp) with (Regs x Sp) in * by congruence.
    generalize dependent H31.
    intro.
    generalize dependent x1.
    evaluate auto_ext.
    intros; descend.
    rewrite H9.
    descend.
    erewrite changed_in_inv by solver.
    descend.
    rewrite H41.
    simpl.
    eauto.
    step auto_ext.
    simpl fst in *.
    assert (sel vs S_RESERVED = sel x10 S_RESERVED) by solver.
    simpl in H17.
    assert (vs [e0] = upd x9 (tempOf 0) (Regs x2 Rv) [e0]).
    transitivity (x9 [e0]).
    symmetry; eapply sameDenote; try eassumption.
    generalize H4; clear; intros; solver.
    symmetry; eapply sameDenote.
    instantiate (1 := tempVars 1).
    generalize H4; clear; intros; solver.
    eapply changedVariables_upd'.
    eauto.
    solver.
    descend.

    generalize H7 H14; repeat match goal with
                                | [ H : _ |- _ ] => clear H
                              end; intros.
    step auto_ext.
    unfold upd; simpl.
    rewrite wordToNat_wminus.
    do 2 f_equal; auto.
    rewrite <- H43.
    simpl in H5.
    pre_nomega.
    change (wordToNat (natToW 3)) with 3; omega.
    unfold sel, upd; simpl.
    rewrite H39.
    unfold arg_v in H35.
    rewrite H44 in H35.
    eassumption.
    step auto_ext.
    eapply existsR.
    apply andR.
    apply andR.
    apply Imply_I; apply interp_weaken;
      do 3 (apply Forall_I; intro); eauto.
    apply Imply_I; apply interp_weaken;
      do 2 (apply Forall_I; intro); eauto.
    change (fst (vs, arrs)) with vs in *.
    descend.
    clear Hi H37 H25.
    repeat match goal with
             | [ H : _ \/ _ |- _ ] => clear H
             | [ H : not _ |- _ ] => clear H
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
           end.
    step auto_ext.
    rewrite (create_locals_return ("rp" :: S_RESERVED :: "__arg" :: nil)
      (wordToNat (sel vs S_RESERVED) - 3) ("rp" :: S_RESERVED :: "__arg" :: vars)
      (wordToNat (sel vs S_RESERVED))
      (S (S (S (S (S (S (S (S (S (S (S (S (4 * Datatypes.length vars)))))))))))))).
    assert (ok_return ("rp" :: S_RESERVED :: "__arg" :: vars) ("rp" :: S_RESERVED :: "__arg" :: nil)
      (wordToNat (sel vs S_RESERVED)) (wordToNat (sel vs S_RESERVED) - 3)
      (S (S (S (S (S (S (S (S (S (S (S (S (4 * Datatypes.length vars))))))))))))))
      by (split; simpl; omega).
    assert (Safe x4 k (upd x10 "!." (upd x9 "." (Regs x2 Rv) [e0]), x13)).
    eapply Safe_immune.
    apply H36.
    econstructor.
    eauto.
    eauto.
    unfold upd in H12; simpl in H12; congruence.

    Lemma agree_in_upd : forall vs vs' ls x v,
      agree_in vs vs' ls
      -> ~In x ls
      -> agree_in vs (upd vs' x v) ls.
      unfold agree_in; intros.
      destruct (string_dec x x0); subst; descend; eauto.
    Qed.

    apply agree_in_upd.
    solver.
    apply changedVariables_symm.
    eapply ChangeVar_tran'.
    apply changedVariables_symm; eassumption.
    apply changedVariables_symm; eassumption.
    solver.
    solver.
    solver.
    intro Hin.
    specialize (H4 _ (in_or_app _ _ _ (or_intror _ Hin))).
    apply H4.
    solver.

    generalize dependent (Safe x4 k); intros.
    clear H12 H32 H33 H40.
    instantiate (2 := (_, _)); simpl.
    rewrite fold_4S' in *.
    instantiate (3 := upd x10 "!." (upd x9 "." (Regs x2 Rv) [e0])).
    hiding ltac:(step auto_ext).
    congruence.
    repeat match goal with
             | [ H : Regs _ _ = _ |- _ ] => rewrite H
           end.
    repeat (rewrite wminus_wplus || rewrite wplus_wminus).
    hiding ltac:(step auto_ext).
    descend.
    replace (sel x10 "rp") with (sel vs "rp").
    eauto.
    erewrite <- (@changed_in_inv x10).
    2: apply changedVariables_symm; eassumption.
    descend.
    eapply changed_in_inv.
    apply changedVariables_symm; eassumption.

    Lemma rp_tempOf : forall n, tempOf n = "rp"
      -> False.
      induction n; simpl; intuition.
    Qed.

    Lemma rp_tempChunk : forall k n,
      ~In "rp" (tempChunk n k).
      induction k; simpl; intuition.
      apply in_app_or in H; intuition idtac.
      eauto.
      simpl in *; intuition.
      eapply rp_tempOf; eauto.
    Qed.

    eauto using rp_tempChunk.
    eauto using rp_tempChunk.
    descend; step auto_ext.
    descend; step auto_ext.
    descend; step auto_ext.
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H
           end; apply wplus_wminus.
    clear H15 H12 H40 H32 H33.
    descend; step auto_ext.
    eapply RunsToRelax_seq_bwd; [ | eauto | eauto ].
    eexists (_, _).
    split.
    econstructor.
    eauto.
    eauto.
    unfold upd in H12; simpl in H12.
    rewrite H39 in H12; rewrite <- H44 in H12; eauto.
    simpl.
    split; auto.
    solver.

    eapply changedVariables_upd'.
    2: solver.
    apply changedVariables_symm.
    eapply ChangeVar_tran'.
    apply changedVariables_symm; eassumption.
    apply changedVariables_symm; eassumption.
    solver.
    solver.
    solver.

    (* Switch to case for internal function calls. *)
    
    specialize (Imply_sound (Hi _ _) (Inj_I _ _ H32)); propxFo.
    repeat match goal with
             | [ H : context[exprDenote] |- _ ] => generalize dependent H
             | [ H : context[Build_callTransition] |- _ ] => generalize dependent H
             | [ H : agree_except _ _ _ |- _ ] => generalize dependent H
           end.
    change (string -> W) with vals in *.
    generalize dependent H31.
    simpl in H25.
    evaluate auto_ext.
    intro.
    rewrite fold_4S' in *.

    cond_gen.
    solver.
    let P := fresh "P" in
      match goal with
        | [ _ : context[Safe ?fs _ _] |- _ ] => set (P := Safe fs) in *
      end.
    assert (~In "rp" (S_RESERVED :: "__arg" :: vars)) by (simpl; intuition).
    prep_locals.
    replace (Regs x0 Sp) with (Regs x Sp) in * by congruence.
    generalize dependent H31.
    intro.
    generalize dependent x1.
    evaluate auto_ext.
    intros; descend.
    rewrite H9.
    descend.
    erewrite changed_in_inv by solver.
    descend.
    rewrite H41.
    simpl.
    eauto.
    step auto_ext.
    simpl fst in *.
    assert (sel vs S_RESERVED = sel x10 S_RESERVED) by solver.
    simpl in H17.
    assert (vs [e0] = upd x9 (tempOf 0) (Regs x2 Rv) [e0]).
    transitivity (x9 [e0]).
    symmetry; eapply sameDenote; try eassumption.
    generalize H4; clear; intros; solver.
    symmetry; eapply sameDenote.
    instantiate (1 := tempVars 1).
    generalize H4; clear; intros; solver.
    eapply changedVariables_upd'.
    eauto.
    solver.
    descend.

    generalize H7 H14; repeat match goal with
                                | [ H : _ |- _ ] => clear H
                              end; intros.
    step auto_ext.
    unfold upd; simpl.
    rewrite wordToNat_wminus.
    do 2 f_equal; auto.
    rewrite <- H43.
    simpl in H5.
    pre_nomega.
    change (wordToNat (natToW 3)) with 3; omega.
    apply H35.
    unfold sel, upd; simpl.
    unfold arg_v; congruence.
    step auto_ext.
    eapply existsR.
    apply andR.
    apply andR.
    apply Imply_I; apply interp_weaken;
      do 3 (apply Forall_I; intro); eauto.
    apply Imply_I; apply interp_weaken;
      do 2 (apply Forall_I; intro); eauto.
    change (fst (vs, arrs)) with vs in *.
    descend.
    clear Hi H35 H37 H25.
    repeat match goal with
             | [ H : _ \/ _ |- _ ] => clear H
             | [ H : not _ |- _ ] => clear H
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
           end.
    step auto_ext.
    destruct H12.
    rewrite (create_locals_return ("rp" :: S_RESERVED :: "__arg" :: nil)
      (wordToNat (sel vs S_RESERVED) - 3) ("rp" :: S_RESERVED :: "__arg" :: vars)
      (wordToNat (sel vs S_RESERVED))
      (S (S (S (S (S (S (S (S (S (S (S (S (4 * Datatypes.length vars)))))))))))))).
    assert (ok_return ("rp" :: S_RESERVED :: "__arg" :: vars) ("rp" :: S_RESERVED :: "__arg" :: nil)
      (wordToNat (sel vs S_RESERVED)) (wordToNat (sel vs S_RESERVED) - 3)
      (S (S (S (S (S (S (S (S (S (S (S (S (4 * Datatypes.length vars))))))))))))))
      by (split; simpl; omega).
    assert (Safe x4 k (upd x10 "!." (upd x9 "." (Regs x2 Rv) [e0]), x13)).
    eapply Safe_immune.
    apply H36.
    econstructor 14.
    eauto.
    2: eauto.
    unfold sel, upd; simpl.
    congruence.

    apply agree_in_upd.
    solver.
    apply changedVariables_symm.
    eapply ChangeVar_tran'.
    apply changedVariables_symm; eassumption.
    apply changedVariables_symm; eassumption.
    solver.
    solver.
    solver.
    intro Hin.
    specialize (H4 _ (in_or_app _ _ _ (or_intror _ Hin))).
    apply H4.
    solver.

    generalize dependent (Safe x4 k); intros.
    clear H12 H40 H32 H33.
    instantiate (2 := (_, _)); simpl.
    rewrite fold_4S' in *.
    instantiate (3 := upd x10 "!." (upd x9 "." (Regs x2 Rv) [e0])).
    hiding ltac:(step auto_ext).
    congruence.
    repeat match goal with
             | [ H : Regs _ _ = _ |- _ ] => rewrite H
           end.
    repeat (rewrite wminus_wplus || rewrite wplus_wminus).
    hiding ltac:(step auto_ext).
    simpl.
    descend.
    replace (sel x10 "rp") with (sel vs "rp").
    eauto.
    erewrite <- (@changed_in_inv x10).
    2: apply changedVariables_symm; eassumption.
    descend.
    eapply changed_in_inv.
    apply changedVariables_symm; eassumption.

    eauto using rp_tempChunk.
    eauto using rp_tempChunk.

    descend; step auto_ext.
    descend; step auto_ext.
    descend; step auto_ext.
    descend; step auto_ext.
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H
           end; apply wplus_wminus.
    clear H15 H12 H40 H32 H33.
    descend; step auto_ext.

    eapply RunsToRelax_seq_bwd; [ | eauto | eauto ].
    eexists (_, _).
    split.
    econstructor 14.
    eauto.
    2: eauto.
    unfold sel, upd; simpl; congruence.
    split; auto.
    solver.

    simpl.
    eapply changedVariables_upd'.
    2: solver.
    apply changedVariables_symm.
    eapply ChangeVar_tran'.
    apply changedVariables_symm; eassumption.
    apply changedVariables_symm; eassumption.
    solver.
    solver.
    solver.
  Qed.

  Definition statementCmd (s k : Statement) := Wrap imports imports_global modName (compile s k) (fun _ => postcond k) (verifCond s k imports) (@post_ok s k) (@verifCond_ok s k).

End Compiler.

