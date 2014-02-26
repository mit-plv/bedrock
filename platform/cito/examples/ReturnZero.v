Set Implicit Arguments.

Require Import Link.
Require Import ExampleADT ExampleImpl.

Module Import LinkMake := Link.Make ExampleADT ExampleRepInv.

Require Import Notations2.

Open Scope stmt_scope.

Notation "$ n" := (natToW n).

Definition body := 
  "ret" <- $0.

Require Import SyntaxFunc.
Require Import List.

Definition return_zero : Func :=
  {|
    Name := "return_zero";
    Core := 
      {|
        ArgVars := nil;
        RetVar := "ret";
        Body := body
      |}
  |}.

Require Import SyntaxModule.

Definition return_zero_m : Module :=
  {|
    Name := "return_zero";
    Functions := return_zero :: nil
  |}.

Require Import GoodModule.

Notation MName := SyntaxModule.Name.
Notation FName := SyntaxFunc.Name.
Notation Funcs := SyntaxModule.Functions.

Require Import GoodFunc.

Require Import Program.Basics.

Infix "*" := compose.

Definition IsGoodModule (m : Module) :=
  IsGoodModuleName (MName m) /\
  List.Forall (GoodFunc * Core) (Funcs m) /\
  List.NoDup (List.map FName (Funcs m)).

Require Import GeneralTactics.
Require Import GoodFunction.

Definition to_good_functions (ls : list Func) : List.Forall (GoodFunc * Core) ls -> list GoodFunction.
  induction ls; simpl; intros.
  eapply nil.
  eapply cons.
  econstructor.
  instantiate (1 := a).
  eapply Forall_forall in H; intuition.
  unfold compose in *.
  eauto.
  eapply IHls.
  eapply Forall_forall.
  intros.
  eapply Forall_forall with (l := a :: ls) in H.
  eauto.
  intuition.
Defined.

Lemma to_good_functions_name : forall ls (h : List.Forall (GoodFunc * Core) ls), map (fun f : GoodFunction => FName f) (to_good_functions h) = map FName ls.
  induction ls; simpl; intros.
  eauto.
  f_equal; eauto.
Qed.

Definition to_good_module (m : Module) : IsGoodModule m -> GoodModule.
  intros.
  unfold IsGoodModule in *.
  openhyp.
  econstructor.
  eauto.
  instantiate (1 := to_good_functions H0).
  rewrite to_good_functions_name.
  eauto.
Defined.

Definition to_module (m : GoodModule) : Module := 
  {|
    SyntaxModule.Name := GoodModule.Name m;
    SyntaxModule.Functions := map GoodFunction.Fun (GoodModule.Functions m)
  |}.

Coercion to_module : GoodModule >-> Module.

Lemma return_zero_good_module : IsGoodModule return_zero_m.
  unfold IsGoodModule, return_zero_m; simpl.
  split.
  unfold IsGoodModuleName.
  simpl; eauto.
  split.
  econstructor.
  unfold compose, return_zero; simpl.
  unfold GoodFunc, body; simpl.
  repeat split; simpl; intuition eauto.
  Import SSUF.
  Import P.
  rewrite add_union_singleton.
  Require Import SetFacts.
  subset_solver.
  econstructor.
  econstructor.
  NoDup.
Qed.

Definition return_zero_gm := to_good_module return_zero_good_module.

Import StubsMake StubMake.
Require Import Label.
Import Label.LabelMap.

Definition return_zero_func_spec := func_spec (return_zero_gm :: nil) (empty _) ("return_zero", "return_zero") return_zero.

Notation extra_stack := 10.

Require Import Malloc.

Definition return_zero_topS := SPEC reserving (3 + extra_stack)
  PRE[_] mallocHeap 0
  POST[R] [| R = 0 |] * mallocHeap 0.

Definition return_zero_top := bimport [[ ("return_zero", "return_zero", return_zero_func_spec)]]
  bmodule "return_zero_top" {{
    bfunction "return_zero_top"("R") [return_zero_topS]
      "R" <-- Call "return_zero"!"return_zero"(extra_stack)
      [PRE[_, R] [| R = 0 |]
       POST[R'] [| R' = R |] ];;
      Return "R"
    end
  }}.

Import CompileFuncSpecMake.
Import InvMake.SemanticsMake.
Import InvMake2.
Import Inv.

Require Import Arith.
Require Import WordFacts.
Require Import CompileStmtTactics.

Lemma body_safe : forall env v, Safe env (Body return_zero) v.
  intros.
  unfold return_zero, Top.body.
  econstructor; eauto.
Qed.

Lemma body_runsto : forall env v v', RunsTo env (Body return_zero) v v' -> sel (fst v') (RetVar return_zero) = 0 /\ snd v' = snd v.
  intros.
  inversion_clear H.
  subst vs.
  simpl.
  split.
  rewrite sel_upd_eq; eauto.
  eauto.
Qed.

Ltac hiding tac :=
  clear_imports;
  ((let P := fresh "P" in
    match goal with
      | H : Safe ?fs _ _ |- _ => set (P := Safe fs) in *
      | H : RunsTo ?fs _ _ _ |- _ => set (P := RunsTo fs) in *
    end;
    hiding tac;
    subst P) || tac).

Theorem return_zero_top_ok : moduleOk return_zero_top.
  vcgen.
  post; sep_auto.

  post; sep_auto.

  post; sep_auto.

  etransitivity.
  Focus 2.
  eapply prelude_out with (ns' := "R" :: nil).
  simpl; omega.
  sep_auto.

  post; sep_auto.

  post.
  replace (locals _ _ _ _) with (locals_call ("rp" :: "R" :: nil) x1 12 
              (Regs x Sp) ("rp" :: "es" :: nil) 0 8) in H1 by eauto.
  assert (ok_call ("rp" :: "R" :: nil) ("rp" :: "es" :: nil) 12 0 8) by (split; [ simpl; omega
                        | split; [ simpl; omega
                          | split; [ NoDup
                            | reflexivity ] ] ]).
  hiding ltac:(evaluate auto_ext).
  unfold name_marker.
  hiding ltac:(step auto_ext).
  unfold spec_without_funcs_ok.
  post.
  descend.
  unfold is_state in *; simpl in *.
  unfold has_extra_stack in *; simpl in *.
  Opaque mult.
  unfold excessStack, reserved in *.
  Opaque allocated.
  simpl in *.
  rewrite H1 in *.
  hiding ltac:(step auto_ext).
  rewrite wplus_0 in *.
  Open Scope nat.
  replace (4 * 4) with (8 + 8) by eauto.
  rewrite natToW_plus in *.
  rewrite wplus_assoc in *.
  hiding ltac:(step auto_ext).

  set (h0 := locals nil _ _ _) in *.
  unfold locals in h0.
  unfold array in h0.
  simpl in h0.
  subst h0.

  set (h0 := array nil _) in *.
  unfold array in h0.
  simpl in h0.
  subst h0.

  instantiate (3 := (_, heap_empty)).
  simpl.

  set (h0 := is_heap heap_empty) in *.
  unfold is_heap, heap_empty in h0.
  simpl in h0.
  subst h0.

  hiding ltac:(step auto_ext).

  rewrite mult_0_l in *.
  rewrite wplus_0 in *.

  Transparent allocated.
  simpl.

  hiding ltac:(step auto_ext).

  set (lcl := locals ("rp" :: "R" :: nil) _ _ _).
  unfold locals, array.
  simpl.

  set (es := upd x3 "es" 10 "es").
  set (rprp := upd x3 "es" 10 "rp").

  replace es with ($10).

  hiding ltac:(step auto_ext).

  subst es.
  sep_auto.
  eapply body_safe.
  eauto.

  hiding ltac:(step auto_ext).
  hiding ltac:(step auto_ext).

  openhyp.
  destruct x6; simpl in *.

  Opaque allocated.
  unfold is_state in *; simpl in *.
  unfold has_extra_stack in *; simpl in *.
  rewrite mult_0_r in *.
  rewrite wplus_0 in *.

  set (h0 := locals nil _ _ _) in *.
  unfold locals in h0.
  unfold array in h0.
  simpl in h0.
  subst h0.

  set (h0 := array nil _) in *.
  unfold array in h0.
  simpl in h0.
  subst h0.

  replace h with (heap_empty).

  set (h0 := is_heap heap_empty) in *.
  unfold is_heap, heap_empty in h0.
  simpl in h0.
  subst h0.

  rewrite H13 in *.
  rewrite H1 in *.
  rewrite wplus_wminus in *.

  replace ((Regs x Sp ^+ natToW 8 ^+ $ (8)) =?> 10)%Sep with (excessStack (Regs x Sp) ("rp" :: "R" :: nil) 12 ("rp" :: "es" :: nil) 0).

  Transparent allocated.
  simpl.

  hiding ltac:(step auto_ext).

  eapply body_runsto in H11.
  openhyp.
  unfold return_zero in *; simpl in *.
  congruence.

  unfold locals, array.
  simpl.
  rewrite fold_4_mult_2 in *.
  instantiate (2 := upd (upd x1 "rp" x7) "es" x8).

  replace (upd (upd x1 "rp" x7) "es" x8 "rp") with x7.
  replace (upd (upd x1 "rp" x7) "es" x8 "es") with ($ x8).

  hiding ltac:(step auto_ext).

  sep_auto.
  sep_auto.

  unfold excessStack, reserved.
  Opaque allocated.
  simpl.
  replace (4 * 4) with (8 + 8) by eauto.
  rewrite natToW_plus in *.
  rewrite wplus_assoc in *.
  eauto.

  eapply body_runsto in H11.
  openhyp.
  simpl in *.
  eauto.

  eauto.

  repeat hiding ltac:(step auto_ext).

  words.

  eapply body_runsto in H11.
  openhyp.
  unfold return_zero in *; simpl in *.
  congruence.

  post; sep_auto.
  post; sep_auto.
  post; sep_auto.

  Grab Existential Variables.
  eauto.

Qed.

(* linking *)

Require Import GoodOptimizer ConstFolding ElimDead.

Definition opt := compose ConstFolding.opt ElimDead.opt.

Module Import GoodOptimizerMake := GoodOptimizer.Make ExampleADT.
Module Import ConstFoldingMake := ConstFolding.Make ExampleADT.
Module Import ElimDeadMake := ElimDead.Make ExampleADT.

Lemma opt_good : GoodOptimizer opt.
  unfold opt.
  eapply GoodOptimizer_trans.
  eapply ConstFoldingMake.good_optimizer.
  eapply ElimDeadMake.good_optimizer.
Qed.

Definition return_zero_impl := output (return_zero_gm :: nil) (empty _) opt_good.

Definition return_zero_all := link return_zero_top return_zero_impl.

Lemma disjoint_imports : LinkMake.LF.Disjoint (module_names (return_zero_gm :: nil))
                                              (imported_module_names (empty ForeignFuncSpec)).
  unfold imported_module_names.
  simpl.
  unfold LinkMake.LF.Disjoint; intros.
  intuition.
Qed.

Require Import GeneralTactics2.

Import LinkMake.LMF.P.F.
Import LinkModuleImplsMake.
Import StubMake.

Lemma to_good_module_name : forall (m : Module) (h : IsGoodModule m), GoodModule.Name (to_good_module h) = SyntaxModule.Name m.
  intros.
  destruct h.
  openhyp.
  unfold to_good_module; simpl in *.
  eauto.
Qed.

Import SSUF.P.FM.
Require Import StructuredModuleFacts.
Existing Instance BLMFU3.Compat_m_Proper.
Require Import ConvertLabelMap.
Import LMFU.
Import LMF.P.
Import LMFU3.

Close Scope nat.

Lemma to_good_functions_in : forall (ls : list Func) (h : List.Forall (GoodFunc * Core) ls) (f : Func), List.In f ls -> exists gf : GoodFunction, List.In gf (to_good_functions h) /\ (gf : Func)  = f.
  induction ls; simpl; intros.
  intuition.
  openhyp.
  subst.
  descend; split.
  left.
  eauto.
  simpl; eauto.
  eapply IHls in H.
  openhyp.
  descend; split.
  right.
  eauto.
  eauto.
Qed.

Lemma to_good_module_functions_in : forall (m : Module) (h : IsGoodModule m) (f : Func), List.In f (Funcs m) -> exists gf : GoodFunction, List.In gf (Functions (to_good_module h)) /\ (gf : Func) = f.
  intros.
  destruct h.
  openhyp.
  unfold to_good_module; simpl.
  assert (GoodFunc f).
  eapply Forall_forall in f0.
  2 : eauto.
  unfold Basics.compose in *.
  eauto.
  eapply to_good_functions_in in H.
  openhyp.
  descend; split; eauto.
Qed.

Import LF.

Lemma GoodModule_NoDup_impl_labels : forall (m : GoodModule) (mn : string), NoDup (List.map (fun f : GoodFunction => impl_label mn (FName f)) (Functions m)).
  intros.
  erewrite <- map_map.
  eapply Injection_NoDup.
  eapply impl_label_is_injection.
  destruct m0; simpl in *.
  eapply NoDupFuncNames.
Qed.

Lemma not_in_impls : forall modules lbl, IsGoodModuleName (fst lbl) -> ~ In lbl (LinkModuleImplsMake.total_exports modules).
  intros.
  nintro.
  unfold LinkModuleImplsMake.total_exports in *.
  eapply In_MapsTo in H0.
  openhyp.
  eapply update_all_elim in H0.
  openhyp.
  eapply in_map_iff in H0; openhyp; subst.
  unfold LinkModuleImplsMake.get_module_Exports in *.
  unfold LinkModuleImplsMake.LMF.to_map in *.
  eapply of_list_1 in H1.
  eapply InA_eqke_In in H1.
  eapply in_map_iff in H1; openhyp; subst.
  injection H0; intros; subst.
  simpl in *.
  unfold NameDecoration.impl_module_name in *.
  unfold IsGoodModuleName in *.
  simpl in *.
  intuition.
  eapply NoDupKey_NoDup_fst.
  rewrite map_map; simpl.
  eapply GoodModule_NoDup_impl_labels.
Qed.

Existing Instance to_blm_Equal_m_Proper.
Existing Instance CompatReflSym_Symmetric.
Existing Instance CompatReflSym_Reflexive.
Existing Instance Compat_m_Proper.
Existing Instance Disjoint_m_Symmetric.
Existing Instance mapi_m_Proper.
Existing Instance BLMFU3.CompatReflSym_Symmetric.

Theorem return_zero_all_ok : moduleOk return_zero_all.
  eapply linkOk.
  eapply return_zero_top_ok.
  eapply output_ok.
  intuition.
  NoDup.
  eapply disjoint_imports.
  intros; eapply empty_in_iff in H; intuition.
  eapply inter_is_empty_iff.
  setoid_rewrite output_module_names.
  simpl.
  unfold return_zero_gm.
  unfold impl_MName.
  repeat rewrite to_good_module_name.
  unfold return_zero_m; simpl.
  unfold NameDecoration.impl_module_name.
  unfold LinkMake.SSUF.Disjoint; intros.
  nintro.
  openhyp.
  eapply singleton_iff in H.
  subst.
  eapply union_iff in H0; openhyp.
  eapply add_iff in H; openhyp.
  simpl in *; intuition.
  eapply empty_iff in H; intuition.
  eapply add_iff in H; openhyp.
  simpl in *; intuition.
  eapply empty_iff in H; intuition.
  intuition.
  NoDup.
  eapply disjoint_imports.
  intros; eapply empty_in_iff in H; intuition.
  eapply importsOk_Compat.
  setoid_rewrite output_exports.
  unfold Imports, return_zero_top; simpl.
  rewrite importsMap_of_list.
  eapply to_blm_Compat.
  unfold LMFU3.Compat.
  intros.
  eapply In_MapsTo in H.
  openhyp.
  generalize H; intro.
  eapply find_1 in H1.
  rewrite H1.
  symmetry.
  eapply of_list_1 in H.
  eapply InA_eqke_In in H.
  simpl in H.
  openhyp.
  2 : intuition.
  injection H; intros; subst.
  eapply find_1.
  eapply update_mapsto_iff.
  right.
  split.
  unfold total_exports; simpl.
  unfold StubMake.LMFU3.update_all.
  simpl.
  eapply update_mapsto_iff.
  left.
  unfold get_module_Exports.
  unfold return_zero_func_spec.
  unfold StubMake.LMF.to_map.
  eapply of_list_1.
  eapply NoDupKey_NoDup_fst.
  rewrite map_map.
  simpl.
  eapply GoodModule_NoDup_labels.
  eapply InA_eqke_In.
  eapply in_map_iff.
  edestruct to_good_module_functions_in.
  instantiate (2 := return_zero).
  instantiate (1 := return_zero_m).
  unfold return_zero_m; simpl.
  eauto.
  openhyp.
  exists x.
  split.
  rewrite H3 in *.
  unfold return_zero_gm.
  repeat rewrite to_good_module_name in *.
  unfold return_zero_m; simpl.
  eauto.
  unfold return_zero_gm in *.
  eauto.
  eapply not_in_impls.
  unfold IsGoodModuleName; simpl.
  eauto.
  eapply NoDupKey_NoDup_fst; simpl; NoDup.
  eapply NoDupKey_NoDup_fst; simpl; NoDup.
  intuition.
  NoDup.
  eapply disjoint_imports.
  intros; eapply empty_in_iff in H; intuition.
  eapply importsOk_Compat.
  setoid_rewrite output_imports.
  unfold foreign_imports.
  setoid_rewrite mapi_empty.
  setoid_rewrite <- to_blm_empty.
  symmetry.
  eapply BLMFU3.Compat_empty.
  intuition.
  NoDup.
  eapply disjoint_imports.
  intros; eapply empty_in_iff in H; intuition.
  eapply importsOk_Compat.
  setoid_rewrite output_imports.
  unfold foreign_imports.
  setoid_rewrite mapi_empty.
  setoid_rewrite <- to_blm_empty.
  eapply BLMFU3.Compat_empty.
  intuition.
  NoDup.
  eapply disjoint_imports.
  intros; eapply empty_in_iff in H; intuition.
Qed.