Require Import AutoSep Wrap Arith.
Import DefineStructured.
Require Import ExprLemmas.
Require Import VariableLemmas.
Require Import GeneralTactics.
Require Import SyntaxExpr SemanticsExpr.
Require Import Syntax Semantics.
Import Safety.

Set Implicit Arguments.

Infix ";:" := Syntax.Seq (left associativity, at level 110).

Infix "<-" := Syntax.Assignment (at level 90, no associativity).

Require DepthExpr.

Local Notation edepth := DepthExpr.depth.

Fixpoint depth statement :=
  match statement with
    | Syntax.Skip => 0
    | Syntax.Seq a b => max (depth a) (depth b) 
    | Conditional cond t f => max (edepth cond) (max (depth t) (depth f))
    | Loop cond body => max (edepth cond) (depth body)
    | Syntax.Assignment _ expr => edepth expr
    | Syntax.Call _ f args => 0 (*max (edepth f) (max (1 + edepth arg) 2)*)
  end.

Definition starD (f : W -> ADTValue -> HProp) (d : Heap) : HProp.
  admit.
Defined.

Definition is_heap layout (adts : Heap) : HProp := starD (fun w adt => layout adt w) adts.

Require Import Malloc.

Definition arg_names fspec := tempVars (length (fst (Signature fspec))).

Definition S_RESERVED := "!reserved".

Definition funcsOk layout (stn : settings) (fs : W -> option Callee) : PropX W (settings * state) := 
(
  (Al i : W, Al fspec, [| fs i = Some (Foreign fspec) |]
    ---> (i, stn) @@@ (st ~> ExX, Ex vs, Ex a, Ex res,
      ![^[locals ("rp" :: S_RESERVED :: arg_names fspec) vs res st#Sp * is_heap layout a * mallocHeap 0] * #0] st
      /\ [| res = wordToNat (vs S_RESERVED) /\ exists args args' ret, match_heap a (sels vs (arg_names fspec)) args /\ Pred fspec {| Args := args; After := args'; Ret := ret |} |]
      /\ (st#Rp, stn) @@@ (st' ~> Ex vs', Ex a',
        [| st'#Sp = st#Sp |]
        /\ ![^[locals ("rp" :: S_RESERVED :: arg_names fspec) vs' res st'#Sp * is_heap layout a' * mallocHeap 0] * #1] st'
        /\ [| exists args args' ret, match_heap a (sels vs (arg_names fspec)) args /\ Pred fspec {| Args := args; After := args'; Ret := ret |} |] ))) 
  /\
  (Al i : W, Al ispec, [| fs i = Some (Internal ispec) |]
    ---> (i, stn) @@@ (st ~> ExX, Ex vs, Ex a, Ex res,
      ![^[locals ("rp" :: S_RESERVED :: fst (InOutVars ispec)) vs res st#Sp * is_heap layout a * mallocHeap 0] * #0] st
      /\ [| res = wordToNat (vs S_RESERVED)
        /\ Safe fs (Body ispec) (vs, a) |]
      /\ (st#Rp, stn) @@@ (st' ~> Ex vs', Ex a',
        [| st'#Sp = st#Sp |]
        /\ ![^[locals ("rp" :: S_RESERVED :: fst (InOutVars ispec)) vs' res st'#Sp * is_heap layout a' * mallocHeap 0] * #1] st'
        /\ [| exists vs'', RunsTo fs (Body ispec) (vs, a) (vs'', a') /\ st'#Rv = sel vs'' (snd (InOutVars ispec)) |] )))
)%PropX.

Definition RunsToRelax fs s v v_new := 
  exists v', RunsTo fs s v v' 
    /\ changed_in (fst v') (fst v_new) (tempVars (depth s))
    /\ snd v_new = snd v'.

Local Notation "fs ~:~ v1 ~~ s ~~> v2" := (RunsToRelax fs s v1 v2) (no associativity, at level 60).

Definition inv layout vars s : assert := 
  st ~> Ex fs, funcsOk layout (fst st) fs
  /\ ExX, Ex v, Ex res,
  ![^[locals ("rp" :: vars) (fst v) res st#Sp * is_heap layout (snd v) * mallocHeap 0] * #0] st
  /\ [| res = wordToNat (sel (fst v) S_RESERVED) /\ Safe fs s v |]
  /\ (sel (fst v) "rp", fst st) @@@ (st' ~> Ex v',
    [| st'#Sp = st#Sp |]
    /\ ![^[locals ("rp" :: vars) (fst v') res st'#Sp * is_heap layout (snd v') * mallocHeap 0] * #1] st'
    /\ [| RunsToRelax fs s v v' |]).

Require Import Footprint.

Definition well_formatted_cito_name name := prefix name "!" = false.

Definition vars_require vars s := 
  List.incl (footprint s) vars
  /\ List.incl (tempVars (depth s)) vars
  /\ List.Forall well_formatted_cito_name (footprint s)
  /\ ~ In "rp" vars
  /\ nth_error vars 0 = Some S_RESERVED.

Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

Section Compiler.

  Variable layout : ADTValue -> W -> HProp.
  Variable vars : list string.

  Section Specifications.

    Variable s k : Statement.

    Definition precond := inv layout vars (s;: k).

    Definition postcond := inv layout vars k.

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

  Definition SaveRv var := Strline (Assign (variableSlot var vars) (RvLval (LvReg Rv)) :: nil).

  Local Notation "v [( e )]" := (exprDenote e (fst v)) (no associativity, at level 60).
  
  Definition loop_inv cond body k : assert := 
    let s := Loop cond body;: k in
    st ~> Ex fs, funcsOk layout (fst st) fs /\ ExX, Ex v, Ex res,
    ![^[locals ("rp" :: vars) (fst v) res st#Sp * is_heap layout (snd v) * mallocHeap 0] * #0] st
    /\ [| res = wordToNat (sel (fst v) S_RESERVED) /\ Safe fs s v |]
    /\ [| st#Rv = v[(cond)] |]
    /\ (sel (fst v) "rp", fst st) @@@ (st' ~> Ex v',
      [| st'#Sp = st#Sp |]
      /\ ![^[locals ("rp" :: vars) (fst v') res st'#Sp * is_heap layout (snd v') * mallocHeap 0] * #1] st'
      /\ [| RunsToRelax fs s v v' |]).

  Inductive exposeArray : Prop := ExposeArray.
  Hint Constructors exposeArray.

  Definition afterCall k : assert :=
    st ~> Ex fs, funcsOk layout (fst st) fs /\ ExX, Ex v : Semantics.st, Ex res,
    let old_sp := st#Sp ^- natToW (4 * (1 + length vars)) in
    ![^[locals ("rp" :: vars) (fst v) res old_sp * is_heap layout (snd v) * mallocHeap 0 * [| res = wordToNat (sel (fst v) S_RESERVED) /\ Safe fs k v |] ] * #0] st
    /\ (sel (fst v) "rp", fst st) @@@ (st' ~> Ex v',
      [| st'#Sp = old_sp |]
      /\ ![^[locals ("rp" :: vars) (fst v') res st'#Sp * is_heap layout (snd v') * mallocHeap 0] * #1] st'
      /\ [| RunsToRelax fs k v v' |]).

  Fixpoint compile_exprs exprs base :=
    match exprs with
      | nil => nil
      | x :: xs => exprCmd x base :: SaveRv (tempOf base) :: compile_exprs xs (S base)
    end.

  Fixpoint put_args base target n :=
    match n with
      | 0 => nil
      | S n' => Assign (LvMem (Indir Rv (natToW target))) (RvLval (variableSlot (tempOf base) vars)) :: put_args (1 + base) (4 + target) n'
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
      | Conditional cond t f => Seq2
        (exprCmd cond 0)
        (Structured.If_ imports_global 
          (RvLval (LvReg Rv)) IL.Ne (RvImm $0) 
          (compile t k) 
          (compile f k)) 
      | Loop cond body => Seq2
        (exprCmd cond 0)
        (Structured.While_ imports_global 
          (loop_inv cond body k)
          (RvLval (LvReg Rv)) IL.Ne (RvImm $0)
          (Seq2
            (compile body (Syntax.Seq (Syntax.Loop cond body) k))
            (exprCmd cond 0)))
      | Syntax.Assignment var expr => Seq (
          exprCmd expr 0 ::
          SaveRv var :: 
          nil)
      | Syntax.Call var f args => CheckStack (2 + length args) (Seq (
        exprCmd f 0
        :: SaveRv (tempOf 0)
        :: nil
        ++ compile_exprs args 1
        ++ Strline (
          IL.Binop Rv Sp Plus (natToW (4 * (1 + List.length vars)))
          :: IL.Binop (LvMem (Indir Rv $4)) (RvLval (variableSlot S_RESERVED vars)) Minus (RvImm $3)
          :: nil
          ++ put_args 1 8 (length args)
          ++ Assign Rv (RvLval (variableSlot (tempOf 0) vars))
          :: IL.Binop Sp Sp Plus (natToW (4 * (1 + List.length vars))) 
          :: nil)
        :: Structured.ICall_ _ _ Rv (afterCall k)
        :: Strline (IL.Binop Sp Sp Minus (natToW (4 * (1 + List.length vars))) :: nil)
        :: SaveRet var
        :: nil
        ))
    end.

Require Import SemanticsExprLemmas SemanticsLemmas.
Require Import MyMalloc MyFree.
Import WMake.

  Opaque heap.

  Ltac unfold_eval := unfold precond, postcond, inv, expr_runs_to, runs_to_generic, vars, MIN_RESERVED in *.

  Lemma add_remove : forall a v, v %in fst a -> a %%= add_arr (remove_arr a v) v (get_arr a v).
    intros; hnf; simpl; intuition (unfold WDict.upd);
      try match goal with
            | [ |- context[if ?E then _ else _] ] => destruct E; subst
          end; auto using WMake.equiv_symm, del_add.
  Qed.

  Hint Immediate add_remove.

  Lemma add_remove' : forall a v i, safe_access a v i -> a %%= add_arr (remove_arr a v) v (get_arr a v).
    inversion 1; eauto.
  Qed.

  Hint Immediate add_remove'.

  Lemma Safe_skip : forall fs k v a,
    Safe fs (skip;: k) (v, a)
    -> Safe fs k (v, a).
    inversion 1; auto.
  Qed.

  Hint Immediate Safe_skip.

  Hint Extern 1 (agree_in _ _ _) => progress simpl.

  Lemma Safe_loop_false : forall fs e b v k,
    Safe fs (Loop e b;: k) v ->
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

  Ltac sel_eq_solver :=
    match goal with
      |- sel _ ?V = sel _ ?V => symmetry; changed_in_inv_vars; iter_changed; try temp_solver; try eapply in_tran_not; try incl_arg_vars_solver
    end.

  Ltac le_eq_reserved_solver :=
    match goal with
      | |- _ <= wordToNat (sel _ "__reserved") => replace_reserved; [ omega | sel_eq_solver ]
      | |- _ = wordToNat (sel _ "__reserved") => replace_reserved; [ omega | sel_eq_solver ]
    end.

  Ltac change_rp' :=
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

  Ltac Safe_cond_solver :=
    match goal with
      H : Safe _ (Conditional _ _ _;: _) (?ST1, _) |- Safe _ _ _ =>
        eapply Safe_immune with (vs1 := ST1); [ decide_cond_safe | use_changed_unchanged; simpl; eapply disjoint_trans_lr]
    end.

  Ltac Safe_loop_solver :=
    match goal with
      |- Safe _ (_ ;: (Loop _ _ ;: _)) _ => decide_cond ltac:(eapply Safe_loop_true_k) ltac:(eapply Safe_loop_false)
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
    RunsToRelax_assign_solver |
    Safe_assign_solver | 
    RunsToRelax_Read_Write_solver |
    freeable_goodSize_solver |
    changed_unchanged_disjoint |
    himp_length_solver |
    equiv_solver2' |
    use_Safe_immune' |
    sel_eq_solver |
    tempOf_in_ext_solver |
    le_eq_reserved_solver | 
    Safe_loop_solver
    ].

  Ltac smack := to_tempOf; pre_eauto2; info_eauto 7.

  Ltac var_solver :=
    try apply unchanged_in_upd_same; smack; try apply changed_in_upd_same;
      try (upd_chain_solver2; simpl; incl_app_solver); try (apply incl_tempChunk2; simpl); info_eauto 8.

  Ltac do_prep_rp H VARS :=
    match VARS with
      | context ["__reserved"] => fail 1
      | _ => eapply aug_rp_not_in in H
    end.

  Ltac prep_rp :=
    match goal with 
      | H : In "rp" ?VARS -> False |- _ => do_prep_rp H VARS
      | H : ~ In "rp" ?VARS |- _ => do_prep_rp H VARS
    end.

  Ltac old_eval_step hints := eval_step hints.

  Ltac eval_step hints := try prep_rp; old_eval_step hints.

  Ltac pick_vs :=
    (*try match goal with
          | [ x : (settings * state)%type |- _ ] => destruct x; simpl in *
        end;*)
    match goal with
      H : interp ?SPECS (![?P] ?ST) |- context [ (![_] ?ST)%PropX ] =>
        match P with
          context [ locals _ ?VS _ _ ] => let a := fresh in evar (a : arrays); (exists (VS, a)); unfold a in *; clear a
        end
    end.

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
        | [ x : (vals * arrays)%type |- _ ] => destruct x; simpl in *
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
        pick_vs; descend; try (pick_Safe || (eauto 2; try solve [ eapply Safe_immune; [ eauto 2 | eauto 8 ] ]));
          clear_or.

  Ltac middle :=
    match goal with
      | [ |- context[heap ?a] ] => set_heap_goal;
        match goal with
          | [ _ : exposeArray |- context[heap ?a] ] =>
            assert (trigger a) by constructor; replace_reserved; [ clear_or;
              hiding ltac:(step hints_array_access_bwd); (simpl; eauto); smack; hiding ltac:(step auto_ext) | ]
          | [ _ : exposeArray, t1 := _ |- context[heap ?a] ] =>
            assert (trigger a) by constructor; clear_or;
              hiding ltac:(step hints_array_access_bwd); (simpl; eauto; try subst t1; subst;
                try match goal with
                      | [ |- context[match ?E with pair x _ => x end] ] =>
                        change (match E with pair x _ => x end) with (fst E)
                    end;
                match goal with
                  | _ => apply add_remove
                  | [ H : _ |- _ ] => apply Safe_write_k in H; simpl in H;
                    match type of H with
                      | Safe _ _ (_, ?a) => instantiate (1 := a)
                    end;
                    repeat match goal with
                             | [ x := _ |- _ ] => subst x
                           end;
                    unfold add_arr, remove_arr, equiv, get_arr; simpl; split; [
                      var_solver
                      | intros;
                        repeat (erewrite changed_in_inv; [ | eassumption | var_solver ]; descend); fail ]
                  | _ => eauto
                end)
        end; try reflexivity
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
      | [ _ : exposeArray |- _ ] => do_RunsToRelax_Read_Write_solver; (simpl; eauto); var_solver
      | _ => RunsToRelax_Stuff_solver
      | _ => smack
    end.

  Ltac finale := stepper; solver.

  Ltac t := preamble; middle; finale.

  Opaque mult.

  Lemma post_ok : forall (s k : Statement) (pre : assert) (specs : codeSpec W (settings * state))
    (x : settings * state),
    vcs (verifCond s k imports pre) ->
    interp specs (Postcondition (compile s k pre) x) ->
    interp specs (postcond k x).
    unfold verifCond, imply; induction s.

    (* assignment *)
    abstract t.

    (* ReadAt *)
    abstract t.

    (* WriteAt *)
    abstract t.

    (* seq *)
    abstract t.

    (* skip *)
    abstract t.

    (* conditional *)
    abstract t.

    (* loop *)
    abstract t.

    (* malloc *)
    abstract t.

    (* free *)
    abstract t.

    (* len *)
    abstract t.

    (* call *)
    abstract t.
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
      | [ x : (vals * arrays)%type |- _ ] => destruct x; simpl in *
      | [ x : st |- _ ] => destruct x; simpl in *
    end;
    try match goal with
          | [ x : (settings * state)%type |- _ ] => destruct x; simpl in *
        end.

  Ltac smack2 := pre_eauto2; simpl; info_eauto 8.

  Ltac eval_step2 hints :=
    match goal with
      | Hinterp : interp _ (![ ?P ] (_, ?ST)), Heval : evalInstrs _ ?ST ?INSTRS = _ |- _ =>
        match INSTRS with
          | context [ IL.Binop _ (RvLval (LvReg Sp)) Plus _ ] =>
            change_locals ("rp" :: "__reserved" :: "__arg" :: nil) 0; [ clear Heval |repeat rewrite <- mult_plus_distr_l in *; change_sp; generalize_sp; eval_step hints ]
        end
      | _ => eval_step hints
    end.

  Lemma verifCond_ok : forall s k (pre : assert),
    vcs (verifCond s k imports pre) -> vcs (VerifCond (compile s k pre)).

    unfold verifCond, imply; induction s.

    (* assignment *)
    wrap0; unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step hints; try stepper'; solver.

    (* ReadAt *)
    wrap0; unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step hints; try stepper'; solver.

    (* WriteAt *)
    wrap0; unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step hints; try stepper'; solver.

    (* seq *)
    wrap0.
    auto_apply; wrap0; pre_eauto2; unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step hints; try stepper'; solver.

    auto_apply; wrap0; pre_eauto2; auto_apply_in post_ok; wrap0; unfold_wrap0; wrap0; pre_eauto2; unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step hints; try stepper'; solver.

    (* skip *)
    wrap0; clear_imports; evaluate auto_ext.

    (* conditional *)
    wrap0.
    unfold_eval; clear_imports; repeat eval_step hints; try stepper'; solver.
    clear_imports; evaluate auto_ext.

    (* true case *)
    auto_apply; wrap0; pre_eauto2; unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step auto_ext; destruct_st; descend; [ propxFo | propxFo | instantiate (2 := (_, _)); simpl; stepper | .. ]; try stepper'; solver.

    (* false case *)
    auto_apply; wrap0; pre_eauto2; unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step auto_ext; destruct_st; descend; [ propxFo | propxFo | instantiate (2 := (_, _)); simpl; stepper | .. ]; try stepper'; solver.

    (* loop *)
    wrap0.
    unfold_eval; clear_imports; repeat eval_step hints; try stepper'; solver.

    unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step auto_ext; destruct_st; descend; [ propxFo | propxFo | instantiate (2 := (_, _)); simpl; stepper | .. ]; try stepper'; smack2.

    clear_imports; unfold evalCond in *; unfold evalRvalue in *; intuition.

    auto_apply_in post_ok.
    unfold_eval; clear_imports; unfold_copy_vars_require; repeat eval_step auto_ext; destruct_st; descend; [ propxFo | propxFo | instantiate (2 := (_, _)); simpl; stepper' | .. ]; try stepper'; smack2.

    unfold_wrap0; wrap0; pre_eauto2; unfold_eval; clear_imports; unfold_copy_vars_require; post; descend; try stepper'; solver.

    auto_apply; wrap0; pre_eauto2; unfold_eval; clear_imports; unfold_copy_vars_require; post; descend; try stepper'; solver.

    unfold_wrap0 ; wrap0; auto_apply_in post_ok.
    unfold_eval; clear_imports; post; try stepper'; solver.

    unfold_wrap0; wrap0; pre_eauto2; unfold_eval; clear_imports; unfold_copy_vars_require; post; descend; try stepper'; solver.

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

    change (locals ("rp" :: "__reserved" :: "__arg" :: vars) (upd x10 (tempOf 1) (Regs x0 Rv)) x7 (Regs x0 Sp))
      with (locals_call ("rp" :: "__reserved" :: "__arg" :: vars) (upd x10 (tempOf 1) (Regs x0 Rv)) x7
        (Regs x0 Sp)
        ("rp" :: "__reserved" :: "__arg" :: nil) (x7 - 3)
        (S (S (S (S (S (S (S (S (S (S (S (S (4 * Datatypes.length vars)))))))))))))) in *.
    assert (ok_call ("rp" :: "__reserved" :: "__arg" :: vars) ("rp" :: "__reserved" :: "__arg" :: nil)
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
    specialize (Imply_sound (H3 _ _) (Inj_I _ _ H32)); propxFo.
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
    assert (~In "rp" ("__reserved" :: "__arg" :: vars)) by (simpl; intuition).
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
    assert (sel vs "__reserved" = sel x10 "__reserved") by solver.
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
    unfold arg_v in H37.
    rewrite H44 in H37.
    eassumption.
    step auto_ext.
    eapply existsR.
    apply andR.
    apply andR.
    apply Imply_I; apply interp_weaken;
      do 2 (apply Forall_I; intro); eauto.
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
    rewrite (create_locals_return ("rp" :: "__reserved" :: "__arg" :: nil)
      (wordToNat (sel vs "__reserved") - 3) ("rp" :: "__reserved" :: "__arg" :: vars)
      (wordToNat (sel vs "__reserved"))
      (S (S (S (S (S (S (S (S (S (S (S (S (4 * Datatypes.length vars)))))))))))))).
    assert (ok_return ("rp" :: "__reserved" :: "__arg" :: vars) ("rp" :: "__reserved" :: "__arg" :: nil)
      (wordToNat (sel vs "__reserved")) (wordToNat (sel vs "__reserved") - 3)
      (S (S (S (S (S (S (S (S (S (S (S (S (4 * Datatypes.length vars))))))))))))))
      by (split; simpl; omega).
    assert (Safe x4 k (upd x10 "!." (upd x9 "." (Regs x2 Rv) [e0]), x13)).
    eapply Safe_immune.
    apply H36.
    econstructor.
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
    assert (~In "rp" ("__reserved" :: "__arg" :: vars)) by (simpl; intuition).
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
    assert (sel vs "__reserved" = sel x10 "__reserved") by solver.
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
      do 2 (apply Forall_I; intro); eauto.
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
    rewrite (create_locals_return ("rp" :: "__reserved" :: "__arg" :: nil)
      (wordToNat (sel vs "__reserved") - 3) ("rp" :: "__reserved" :: "__arg" :: vars)
      (wordToNat (sel vs "__reserved"))
      (S (S (S (S (S (S (S (S (S (S (S (S (4 * Datatypes.length vars)))))))))))))).
    assert (ok_return ("rp" :: "__reserved" :: "__arg" :: vars) ("rp" :: "__reserved" :: "__arg" :: nil)
      (wordToNat (sel vs "__reserved")) (wordToNat (sel vs "__reserved") - 3)
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
Definition array_ptr lists p : HProp := array_with_size (lists p) p.

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

Hint Resolve in_tran_not.

Lemma vars_require_imply : forall vars s1 s2, 
  vars_require vars s1 -> 
  List.incl (footprint s2) (footprint s1) ->
  depth s2 <= depth s1 ->
  vars_require vars s2.
  clear; unfold vars_require; intros; openhyp; descend; eauto.
Qed.

Local Notation "'e_vars_require'" := CompileExpr.expr_vars_require.

Lemma vars_require_imply_e : forall vars s e base, vars_require vars s -> List.incl (varsIn e) (footprint s) -> (base + edepth e <= depth s)%nat -> e_vars_require ("__reserved" :: "__arg" :: vars) e base.
  clear; unfold vars_require, CompileExpr.expr_vars_require; simpl; intuition; eauto.
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
      | H : safe_access _ _ _ |- _ => generalize dependent H
      | H : _ %in _ |- _ => generalize dependent H
      | H : Safe _ _ _ |- _ => generalize dependent H
      | H : RunsToRelax _ _ _ _ |- _ => generalize dependent H
    end.

Ltac step_array_access := 
  match goal with
    H_interp : interp ?SPECS (![?P] ?ST) |- interp ?SPECS (![?Q] ?ST) => let H_sp := fresh in 
      assert_sp P Q H_sp; [ .. | protect_hyps; generalize H_interp H_sp; clear; intros; trigger_bwd Q; set_array_hyp; set_heap_goal; step hints_array_access_bwd; post_step ]
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
    |- _ %%= add_arr ?ARRS _ _ => auto_unfold; no_question_mark; rewriter; unfold add_arr, remove_arr, equiv; simpl; to_tempOf; split; [ | intros; repeat f_equal; erewrite changed_in_inv by eauto; rewrite sel_upd_ne by eauto; erewrite changed_in_inv by eauto; rewrite sel_upd_eq by eauto]
  end.

Lemma Safe_read_access : forall fs var arr idx vs arrs, 
  Safe fs (Syntax.ReadAt var arr idx) (vs, arrs) ->
  safe_access arrs (exprDenote arr vs) (exprDenote idx vs).
  intros; inv_Safe_clear; eauto.
Qed.
Hint Resolve Safe_read_access.

Lemma Safe_read_k : forall fs var a i k v, let s := Syntax.ReadAt var a i in Safe fs (s;: k) v -> Safe fs k (denote_sem s v).
  clear; simpl; destruct v; inversion 1; eauto.
Qed.

Ltac set_vs_hyp :=
  match goal with
    H : context [ locals _ ?VS _ _ ] |- _ => set_all VS
  end.

Ltac equiv_solver2 :=
  match goal with
    |- _ %%= add_arr ?ARRS _ _ => auto_unfold; no_question_mark; rewriter; unfold add_arr, remove_arr, equiv; simpl; to_tempOf; split; [ | intros; repeat f_equal]
  end.

Lemma upd_sel_equiv : forall d i i', WDict.upd d i (d i) i' = d i'.
  clear; intros; destruct (weq i i').
  rewrite WDict.sel_upd_eq; congruence.
  rewrite WDict.sel_upd_ne; congruence.
Qed.

Ltac upd_chain_solver2 :=
  match goal with
    H1 : changed_in _ _ _, H2 : changed_in (upd _ _ _) _ _ |- changed_in _ _ _ => no_question_mark; simpl; iter_changed
  end.

Lemma Safe_len_in : forall fs var arr vs arrs, 
  Safe fs (Syntax.Len var arr) (vs, arrs) ->
  vs[arr] %in fst arrs.
  intros; inv_Safe_clear; eauto.
Qed.
Hint Resolve Safe_len_in.

Lemma Safe_len_k : forall fs var a k v, let s := Syntax.Len var a in Safe fs (s;: k) v -> Safe fs k (denote_sem s v).
  clear; simpl; destruct v; inversion 1; eauto.
Qed.

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
    H : Safe _ (Conditional _ _ _;: _) (?ST1, _) |- Safe _ _ _ =>
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

Ltac RunsToRelax_assign_solver :=
  match goal with
    H : _ ~:~ _ ~~ ?K ~~> _ |- _ ~:~ _ ~~ _ <- _;: ?K ~~> _ =>
      eapply RunsToRelax_assign; [ eassumption | unfold st_agree_except | ]; simpl
  end.

Ltac Safe_assign_solver :=
  match goal with
    H : Safe _ (_ <- _;: ?K) _ |- Safe _ ?K _ =>
      eapply Safe_immune; [ eapply Safe_assign; eassumption | eapply changed_unchanged; [ rewriter; use_changed_in_upd_same | ] ]
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

Ltac RunsToRelax_Read_Write_solver :=
  match goal with
    | |- _ ~:~ _ ~~ _ [ _ ] *<- _;: _ ~~> _ => do_RunsToRelax_Read_Write_solver
    | |- _ ~:~ _ ~~ Syntax.ReadAt _ _ _;: _ ~~> _ => do_RunsToRelax_Read_Write_solver
    | |- _ ~:~ _ ~~ Syntax.Len _ _;: _ ~~> _ => do_RunsToRelax_Read_Write_solver
  end.

Ltac freeable_goodSize_solver :=
  match goal with
    | |- freeable _ _ => auto_unfold; rewrite upd_length in *
    | |- goodSize _ => auto_unfold; rewrite upd_length in *
  end.

Ltac himp_length_solver :=
  match goal with
    |- (himp _ (_ =*> natToW (length ?A)) (_ =*> natToW (length ?B)))%Sep =>
    unfold B; repeat hiding ltac:(step hints_array_access_bwd)
  end.

Ltac equiv_solver2' :=
  match goal with
    |- _ %%= add_arr _ _ _ =>
    equiv_solver2; [ | unfold get_arr; symmetry; eapply upd_sel_equiv ]
  end.

Ltac pick_Safe := 
  match goal with
    | H : Safe _ (_ [ _ ] *<- _;: ?K) _ |- Safe _ ?K _ =>
      eapply Safe_write_k in H; eapply Safe_immune; [ eassumption | ]
    | H : Safe _ (Syntax.ReadAt _ _ _;: ?K) _ |- Safe _ ?K _ =>    
      eapply Safe_read_k in H; eapply Safe_immune; [ eassumption | ]
    | H : Safe _ (Syntax.Len _ _;: ?K) _ |- Safe _ ?K _ =>    
      eapply Safe_len_k in H; eapply Safe_immune; [ eassumption | ]
    | H : Safe _ (Syntax.Assignment _ _;: ?K) _ |- Safe _ ?K _ =>    
      eapply Safe_assign in H; eapply Safe_immune; [ eassumption | ]
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
  arrays_eq_solver2 |
  RunsTo_Malloc
  ].

Lemma mult_S_distr_inv : forall a b, a + a * b = a * S b.
  intros; ring.
Qed.

Lemma wplus_wminus : forall (a b : W), a ^+ b ^- b = a.
  intros; words.
Qed.

Ltac rewrite_expr :=
  match goal with
    | H : context [exprDenote ?E ?VS1] |- context [exprDenote ?E ?VS2] => not_eq VS1 VS2; rewrite (@unchanged_exprDenote _ VS1 VS2)
  end.

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
    repeat split; simpl; unfold MIN_RESERVED in *; eauto; NoDup
  end.

Ltac myPost := autorewrite with sepFormula in *; unfold substH in *; simpl in *.

Lemma aug_rp_not_in : forall vars, ~ In "rp" vars -> ~ In "rp" ("__reserved" :: "__arg" :: vars).
  simpl; intuition.
Qed.

Ltac prep_rp :=
  match goal with 
    H : ~ In "rp" ?VARS |- _ =>
      match VARS with
        | context ["__reserved"] => fail 1
        | _ => eapply aug_rp_not_in in H
      end
  end.

Hint Resolve heap_star_not_in.

Ltac rearrange_heap :=
  match goal with
    H : interp ?SPECS (![?P] ?ST) |- _ =>
      match P with
        context [ heap ?ARRS ] =>
        match P with 
          context [ array_with_size ?LS ?PTR ] =>
          rearrange_stars (heap ARRS * array_with_size LS PTR)%Sep
        end
      end
  end.

Lemma not_in_reserved_arg : forall vars, ~ In "__reserved" vars -> ~ In "__reserved" ("__arg" :: vars).
  simpl; intuition.
Qed.

Hint Resolve not_in_reserved_arg.

Lemma Safe_Malloc_goodSize : forall fs var size v, Safe fs (Syntax.Malloc var size) v -> let size_v := exprDenote size (fst v) in goodSize (wordToNat size_v + 2).
  inversion 1; subst; eauto.
Qed.

Hint Resolve Safe_Malloc_goodSize.

Lemma Safe_malloc_goodSize : forall fs var size vs arrs, Safe fs (Syntax.Malloc var size) (vs, arrs) -> let size_v := exprDenote size vs in goodSize (wordToNat size_v + 2).
  intros; eapply (@Safe_Malloc_goodSize _ _ _ (vs, arrs)); eauto.
Qed.

Hint Resolve Safe_malloc_goodSize.

Ltac clear_or :=
  repeat match goal with 
           H : _ \/ _ |- _ => clear H 
         end.

Ltac simpl_vars :=
  repeat match goal with 
           | H : context [footprint _] |- _ => progress simpl in H
           | H : context [tmps _] |- _ => progress simpl in H
         end.

Ltac tempOf_in_ext_solver :=
  match goal with
    |- In (tempOf _) ("__reserved" :: "__arg" :: ?VARS) =>
    eapply In_incl with (ls1 := VARS)
  end.

Ltac replace_reserved :=
  match goal with
    H : context [sel ?VS1 "__reserved"] |- context [sel ?VS2 "__reserved"] =>
      not_eq VS1 VS2; replace (sel VS2 "__reserved") with (sel VS1 "__reserved") in *
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
  RunsToRelax_assign_solver |
  Safe_assign_solver | 
  RunsToRelax_Read_Write_solver |
  freeable_goodSize_solver |
  changed_unchanged_disjoint |
  himp_length_solver |
  equiv_solver2' |
  use_Safe_immune' |
  sel_eq_solver |
  tempOf_in_ext_solver
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



Module CompileMalloc.
Section CompileMalloc.

  Variable vars : list string.
  Variable var : string.
  Variable size : Expr.
  Variable k : Statement.

  Definition postcond := inv vars k.

  Definition s_k := var <- new size;: k.

  Definition precond := inv vars s_k.

  (* cope with an [evaluate] failure *)
  Definition length_require A ls vs := @length A ls = wordToNat (vs[size]).

  Definition vars := "__reserved" :: "__arg" :: vars.

  Definition afterCall : assert :=
    st ~> Ex fs, funcsOk (fst st) fs /\ ExX, Ex v : Semantics.st, Ex ls, Ex res,
    let old_sp := st#Sp ^- natToW (4 * 3 + 4 * length vars) in
    let addr := st#Rv in
    ![^[locals ("rp" :: vars) (fst v) res old_sp * heap (snd v) * mallocHeap 0 * array_with_size ls addr * [| length_require ls (fst v) /\ res = wordToNat (sel (fst v) "__reserved") /\ MIN_RESERVED <= res /\ Safe fs s_k v |] ] * #0] st
    /\ (sel (fst v) "rp", fst st) @@@ (st' ~> Ex v',
      [| st'#Sp = old_sp |]
      /\ ![^[locals ("rp" :: vars) (fst v') res st'#Sp * heap (snd v') * mallocHeap 0] * #1] st'
      /\ [| RunsToRelax fs s_k v v' |]).

  Variable imports : LabelMap.t assert.
  Variable imports_global : importsGlobal imports.
  Variable modName : string.

  Definition verifCond pre :=
    (LabelMap.find (elt:=assert) ("my_malloc"!"malloc")%SP imports = Some (Precondition my_mallocS None))
    :: imply pre precond :: vars_require vars s_k :: nil.

  Definition Seq2 := @Seq_ _ imports_global modName.

  Definition Strline := Straightline_ imports modName.

  Definition Skip := Straightline_ imports modName nil.

  Fixpoint Seq ls :=
    match ls with
      | nil => Skip
      | a :: ls' => Seq2 a (Seq ls')
    end.

  Definition SaveRv var := Strline (Assign (variableSlot var vars) (RvLval (LvReg Rv)) :: nil).

  Definition exprCmd := CompileExpr.exprCmd imports_global modName vars.

  Definition body := Seq (
    exprCmd size 0
    :: SaveRv (tempOf 0)
      :: Strline (
        IL.Binop Rv Sp Plus (natToW (4 * 3 + 4 * List.length vars))
        :: Assign (LvMem (Indir Rv (natToW 4))) (RvLval (variableSlot (tempOf 0) vars))
        :: IL.Binop Sp Sp Plus (natToW (4 * 3 + 4 * List.length vars))
        :: nil)
      :: Structured.Call_ imports_global modName ("my_malloc"!"malloc")%SP afterCall
      :: Strline (
        IL.Binop Sp Sp Minus (natToW (4 * 3 + 4 * List.length vars))
        :: nil)
      :: SaveRv var
        :: nil).

  Opaque mult.

  Opaque variablePosition.

  Opaque heap.

  Ltac unfold_eval := unfold precond, postcond, inv, expr_runs_to, runs_to_generic, vars, MIN_RESERVED in *.

  Lemma post_ok : forall (pre : assert) (specs : codeSpec W (settings * state))
    (x : settings * state),
    vcs (verifCond pre) ->
    interp specs (Postcondition (body pre) x) -> interp specs (postcond x).

    unfold verifCond, imply.
    wrap0.

    unfold_eval; unfold_copy_vars_require; clear_imports; myPost; prep_rp; repeat eval_step auto_ext.
    eauto.

    destruct x5.
    simpl in *.
    descend.
    propxFo.
    propxFo.
    instantiate (2 := (_, add_arr a (Regs x2 Rv) x6)).
    simpl in *.
    match goal with
      |- interp _ ?Q => trigger_bwd Q
    end.
    hiding ltac:(step hints_heap_bwd).
    post_step.
    rearrange_heap; auto_apply_in heap_star_not_in; eauto.
    rewriter.
    simpl.
    rewrite sel_upd_ne.
    eauto.
    eauto.
    eauto.
    rewriter.
    inv_Safe.
    subst.
    auto_apply.
    econstructor.
    rearrange_heap; auto_apply_in heap_star_not_in; eauto.
    auto_apply_in Safe_seq_first.
    eauto.
    eauto.
    simpl; rewrite sel_upd_ne; eauto.
    step auto_ext.
    clear_or.
    step auto_ext.
    step auto_ext.
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H
           end.
    assumption.
    hiding ltac:(step auto_ext).
    unfold s_k in *.
    eapply RunsToRelax_seq_bwd.
    2 : eauto.
    rewriter.
    eapply RunsTo_RunsToRelax.
    unfold add_arr.
    econstructor.
    rearrange_heap; auto_apply_in heap_star_not_in; eauto.
    auto_apply_in Safe_seq_first.
    eauto.
    eauto.
    simpl.
    eauto.

  Qed.

  Ltac eval_step2 hints := unfold locals_call in *; 
    match goal with
      | Hinterp : interp _ (![ ?P ] (_, ?ST)), Heval : evalInstrs _ ?ST ?INSTRS = _ |- _ =>
        match INSTRS with
          | context [ IL.Binop _ (RvLval (LvReg Sp)) Plus _ ] =>
            change_locals ("rp" :: "n" :: nil) 8; [ clear Heval |repeat rewrite <- mult_plus_distr_l in *; simpl in *; change_sp; generalize_sp; eval_step hints ]
        end
      | _ => eval_step hints
    end.

  Lemma verifCond_ok : forall pre : assert, vcs (verifCond pre) -> vcs (VerifCond (body pre)).

    unfold verifCond, imply.
    wrap0; try match goal with
                 | [ H : _ = Some _ |- _ ] => rewrite H
               end; clear_imports.
    Focus 4.
    intros; post; unfold_eval; unfold_copy_vars_require; prep_rp;
      repeat eval_step2 auto_ext; to_tempOf; pre_eauto2; eauto.

    eexists.
    eexists.
    split.
    clear_or.
    post.
    hiding ltac:(step auto_ext).
    unfold s_k in *.
    rewriter.
    auto_apply_in Safe_seq_first.
    eauto.
    destruct x4.
    simpl in *.
    descend.
    eauto.
    unfold afterCall.
    step auto_ext.
    step auto_ext.

    apply ignore_premise.
    propxFo.

    instantiate (6 := (_, _)).
    simpl.
    instantiate (3 := upd x7 "." (v[size])).
    hiding ltac:(step auto_ext).
    Focus 4.
    unfold vars in *.
    step_himp_helper.
    unfold MIN_RESERVED in *.
    replace_reserved.
    hiding ltac:(step auto_ext).

    to_tempOf; pre_eauto2; eauto.

    f_equal; eauto.
    rewriter; rewrite <- mult_plus_distr_l; rewrite wplus_wminus; eauto.
    f_equal; eauto.

    unfold length_require.
    to_tempOf.
    rewriter; symmetry; f_equal; eapply exprDenote_disjoint.
    eauto.
    eapply disjoint_trans_lr.
    eauto.
    eauto.
    incl_app_solver; eauto.

    replace_reserved.
    eauto.
    to_tempOf; pre_eauto2; eauto.

    eapply Safe_immune.
    eauto.
    simpl in *.
    to_tempOf.
    eapply changed_unchanged.
    eauto.
    eapply disjoint_trans_lr.
    eauto.
    eauto.
    incl_app_solver; eauto.

    simpl.
    rewrite sel_upd_ne by intuition.
    change_rp.
    eauto.

    do 4 step auto_ext; [ repeat match goal with
                                                 | [ H : _ = _ |- _ ] => rewrite H
                                               end; rewrite four_out; words
      | instantiate (1 := (_, _)); simpl; replace (sel x7 "__reserved") with (sel v "__reserved") in *; [hiding ltac:(step auto_ext) | .. ] | .. ]; destruct x12; pre_eauto2; simpl; to_tempOf; eauto; iter_changed; incl_app_solver; eauto.

    unfold_eval; eval_step auto_ext; descend; repeat hiding ltac:(step auto_ext); pre_eauto2.
    unfold_eval; unfold_copy_vars_require; prep_rp; repeat eval_step2 auto_ext; to_tempOf; pre_eauto2; info_eauto.
    unfold_eval; unfold_copy_vars_require; prep_rp; repeat eval_step2 auto_ext; to_tempOf; pre_eauto2; info_eauto.
    post; unfold_eval; unfold_copy_vars_require; prep_rp; repeat eval_step2 auto_ext; to_tempOf; pre_eauto2; info_eauto.
    post; unfold_eval; unfold_copy_vars_require; prep_rp; repeat eval_step2 auto_ext; to_tempOf; pre_eauto2; info_eauto.
    post; unfold_eval; unfold_copy_vars_require; prep_rp; repeat eval_step2 auto_ext; to_tempOf; pre_eauto2; info_eauto.
  Qed.

  Definition compile := Wrap imports imports_global modName body (fun _ => postcond) verifCond post_ok verifCond_ok.

End CompileMalloc.
End CompileMalloc.

Module CompileFree.
Section CompileFree.

  Variable vars : list string.
  Variable ptr : Expr.
  Variable k : Statement.

  Definition postcond := inv vars k.

  Definition s_k := delete ptr;: k.

  Definition precond := inv vars s_k.

  Definition vars := "__reserved" :: "__arg" :: vars.

  Definition afterCall : assert :=
    st ~> Ex fs, funcsOk (fst st) fs /\ ExX, Ex v : Semantics.st, Ex res,
    let old_sp := st#Sp ^- natToW (4 * (1 + length vars)) in
    let ptr_v := v[(ptr)] in
    ![^[locals ("rp" :: vars) (fst v) res old_sp * heap (remove_arr (snd v) ptr_v) * mallocHeap 0 * [| res = wordToNat (sel (fst v) "__reserved") /\ MIN_RESERVED <= res /\ Safe fs s_k v |] ] * #0] st
    /\ (sel (fst v) "rp", fst st) @@@ (st' ~> Ex v',
      [| st'#Sp = old_sp |]
      /\ ![^[locals ("rp" :: vars) (fst v') res st'#Sp * heap (snd v') * mallocHeap 0] * #1] st'
      /\ [| RunsToRelax fs s_k v v' |]).

  Variable imports : LabelMap.t assert.
  Variable imports_global : importsGlobal imports.
  Variable modName : string.

  Definition verifCond pre :=
    (LabelMap.find (elt:=assert) ("my_free"!"free")%SP imports = Some (Precondition my_freeS None))
    :: imply pre precond :: vars_require vars s_k :: nil.

  Definition Seq2 := @Seq_ _ imports_global modName.

  Definition Strline := Straightline_ imports modName.

  Definition Skip := Straightline_ imports modName nil.

  Fixpoint Seq ls :=
    match ls with
      | nil => Skip
      | a :: ls' => Seq2 a (Seq ls')
    end.

  Definition SaveRv var := Strline (Assign (variableSlot var vars) (RvLval (LvReg Rv)) :: nil).

  Definition exprCmd := CompileExpr.exprCmd imports_global modName vars.

  Definition body := Seq (
    exprCmd ptr 0
    :: SaveRv (tempOf 0)
    :: Strline (
      IL.Binop Rv Sp Plus (natToW (4 * (1 + List.length vars)))
      :: Assign (LvMem (Indir Rv (natToW 4))) (RvLval (variableSlot (tempOf 0) vars))
      :: IL.Binop Sp Sp Plus (natToW (4 * (1 + List.length vars)))
      :: nil)
    :: Structured.Call_ imports_global modName ("my_free"!"free")%SP afterCall
    :: Strline (
      IL.Binop Sp Sp Minus (natToW (4 * (1 + List.length vars)))
      :: nil)
    :: nil).

  Opaque mult.

  Opaque variablePosition.

  Opaque heap.

  Lemma Safe_s_k_first : forall fs v a, Safe fs s_k (v, a)
    -> v[ptr] %in fst a.
    intros.
    apply Safe_seq_first in H.
    inversion H; auto.
  Qed.

  Hint Immediate Safe_s_k_first.

  Lemma Safe_s_k_second : forall fs v a, Safe fs s_k (v, a)
    -> Safe fs k (v, (fst a %- (v [ptr]), snd a)).
    intros.
    eapply Safe_seq_second; eauto.
  Qed.

  Hint Immediate Safe_s_k_second.

  Ltac unfold_eval := unfold precond, postcond, inv, expr_runs_to, runs_to_generic, vars, MIN_RESERVED in *.

  Lemma post_ok : forall (pre : assert) (specs : codeSpec W (settings * state))
    (x : settings * state),
    vcs (verifCond pre) ->
    interp specs (Postcondition (body pre) x) -> interp specs (postcond x).

    unfold verifCond, imply.
    wrap0.
    unfold_eval; unfold_copy_vars_require; clear_imports; myPost; prep_rp; repeat eval_step auto_ext.

    destruct x4; simpl in *.
    descend.
    eauto.
    hiding ltac:(step auto_ext).
    instantiate (2 := (_, _)).
    simpl.
    hiding ltac:(step auto_ext).
    eauto.
    eauto.
    unfold remove_arr; eauto.
    eauto.
    step auto_ext.
    step auto_ext.
    step auto_ext.
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H
           end; assumption.
    hiding ltac:(step auto_ext).
    unfold s_k in *.
    unfold remove_arr in *.
    eapply RunsToRelax_seq_bwd; eauto.
  Qed.

  Ltac eval_step2 hints := unfold locals_call in *; 
    match goal with
      | Hinterp : interp _ (![ ?P ] (_, ?ST)), Heval : evalInstrs _ ?ST ?INSTRS = _ |- _ =>
        match INSTRS with
          | context [ IL.Binop _ (RvLval (LvReg Sp)) Plus _ ] =>
            change_locals ("rp" :: "ptr" :: nil) 8; [ clear Heval |repeat rewrite <- mult_plus_distr_l in *; simpl in *; change_sp; generalize_sp; eval_step hints ]
        end
      | _ => eval_step hints
    end.

  Lemma verifCond_ok : forall pre : assert, vcs (verifCond pre) -> vcs (VerifCond (body pre)).

    unfold verifCond, imply.
    wrap0; try match goal with
                 | [ H : _ = Some _ |- _ ] => rewrite H
               end; clear_imports.
    Focus 4.
    intros; post; unfold_eval; unfold_copy_vars_require; prep_rp; repeat eval_step2 auto_ext; to_tempOf; pre_eauto2; info_eauto.

    destruct x4; simpl in *.
    descend.
    replace (heap a) with (heap_to_split a (v[ptr])) in * by eauto.
    assert (v[ptr] %in fst a) by eauto.
    hiding ltac:(step hints_heap_fwd).
    hiding ltac:(step hints_heap_fwd).
    eauto.
    unfold afterCall.
    step auto_ext.
    step auto_ext.
    
    apply ignore_premise; propxFo.

    unfold_eval.
    hiding ltac:(step auto_ext).
    Focus 3.
    unfold remove_arr.
    rewrite_expr.
    instantiate (1 := (_, _)).
    simpl.
    Ltac rewrite_upd_rv :=
      match goal with
        H : Regs ?ST Rv = _ |- context [ upd _ _ (Regs ?ST Rv) ] => rewrite H
      end.

    Ltac step_himp_helper :=
      match goal with
        |- himp _ ?A ?B =>
        match B with
          context [locals ?VARS ?VS1 _ ?SP1] =>
          match A with
            context [locals VARS ?VS2 _ ?SP2] =>
            match A with
              context [locals ?VARS2 _ _ ?SP3] =>
              not_eq VARS VARS2; rewrite_upd_rv; replace SP1 with SP2; replace SP3 with (SP2 ^+ natToW (4 * length VARS))
            end
          end
        end
      end.

    step_himp_helper.
    hiding ltac:(step auto_ext).
    instantiate (1 := upd x7 "." (v [ptr])).
    replace_reserved.
    hiding ltac:(step auto_ext).

    to_tempOf; pre_eauto2; info_eauto.
    iter_changed; eauto.
    words.
    to_tempOf; agree_in_solver; info_eauto.
    simpl.
    rewrite sel_upd_ne.
    replace_reserved.
    eauto.
    to_tempOf; pre_eauto2; info_eauto.
    intuition.
    to_tempOf; pre_eauto2; info_eauto.
    simpl; to_tempOf; pre_eauto2; info_eauto.

    destruct x11; do 3 step auto_ext; [ repeat match goal with
                                                 | [ H : _ = _ |- _ ] => rewrite H
                                               end; rewrite four_out; words |
    instantiate (1 := (_, _)); simpl; replace_reserved; [hiding ltac:(step auto_ext) | .. ] | .. ];
      pre_eauto2; simpl; to_tempOf; eauto; iter_changed; incl_app_solver; eauto.

    unfold_eval; eval_step auto_ext; descend; repeat hiding ltac:(step auto_ext); pre_eauto2.
    unfold_eval; unfold_copy_vars_require; prep_rp; repeat eval_step2 auto_ext; to_tempOf; pre_eauto2; info_eauto.
    unfold_eval; unfold_copy_vars_require; prep_rp; repeat eval_step2 auto_ext; to_tempOf; pre_eauto2; info_eauto.
    post; unfold_eval; unfold_copy_vars_require; prep_rp; repeat eval_step2 auto_ext; to_tempOf; pre_eauto2; info_eauto.
    post; unfold_eval; unfold_copy_vars_require; prep_rp; repeat eval_step2 auto_ext; to_tempOf; pre_eauto2; info_eauto.
  Qed.

  Definition compile := Wrap imports imports_global modName body (fun _ => postcond) verifCond post_ok verifCond_ok.

End CompileFree.
End CompileFree.

