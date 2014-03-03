Set Implicit Arguments.

Require Import Notations2.

Notation "$ n" := (natToW n) : stmt_scope.

Require Import SyntaxFunc.
Require Import List.

Notation "'cfunction' name () b 'end'" :=
  {|
    Name := name;
    Core := 
      {|
        ArgVars := nil;
        RetVar := "ret";
        Body := b%stmt
      |}
  |} (no associativity, at level 95, name at level 0, only parsing) : Citofuncs_scope.

Notation "'cfunction' name ( x1 , .. , xN ) b 'end'" :=
  {|
    Name := name;
    Core := 
      {|
        ArgVars := cons x1 (.. (cons xN nil) ..);
        RetVar := "ret";
        Body := b%stmt
      |}
  |} (no associativity, at level 95, name at level 0, only parsing) : Citofuncs_scope.

Notation "{{ x 'with' .. 'with' y }}" := (cons x .. (cons y nil) ..) (only parsing) : Citofuncs_scope.

Delimit Scope Citofuncs_scope with Citofuncs.

Require Import SyntaxModule.

Notation "'cmodule' name fs" :=
  {|
    Name := name;
    Functions := fs%Citofuncs
  |} (no associativity, at level 95, name at level 0, only parsing).

Definition f := (
  cfunction "return_zero"()
    "ret" <- $0
  end
)%Citofuncs.

Definition m := cmodule "return_zero" {{
  f
}}.

Require Import GoodModule.

Notation MName := SyntaxModule.Name.
Notation FName := SyntaxFunc.Name.
Notation Funcs := SyntaxModule.Functions.

Require Import GoodFunc.

Require Import Program.Basics.

Infix "*" := compose.

Require Import GeneralTactics.
Require Import GoodFunction.
Require Import IsGoodModule.

(* Should have a decider here for automatic syntactic checking *)

Ltac shakeup := hnf; simpl; intuition (auto; try congruence); hnf; simpl.

Ltac constructors :=
  repeat (match goal with
            | [ |- List.Forall _ _ ] => constructor
            | [ |- NoDup _ ] => constructor
            | [ |- WellFormed.args_not_too_long _ ] => constructor
          end; intros).

Ltac good_module := shakeup; repeat (constructors; shakeup).

Lemma good : IsGoodModule m.
  good_module.
Qed.

Definition gm := to_good_module good.

Require Import ExampleADT ExampleRepInv.
Require Import LinkSpec.
Module Import LinkSpecMake := Make ExampleADT.
Module Import LinkSpecMake2 := Make ExampleRepInv.

Notation "'cimport' lab 'cmodules' [[ m1 , .. , mN ]] 'definition' d" :=
  (func_spec (cons m1 (.. (cons mN nil) ..)) (empty _)
    (match lab%SP with
       | (mname, Global fname) => (mname, fname)
       | _ => ("uhoh", "uhoh")
     end) d)
  (no associativity, at level 95, lab at level 0).

Definition fspec :=
  cimport "return_zero"!"return_zero"
  cmodules [[ gm ]]
  definition f.

Notation extra_stack := 10.

Require Import Malloc.

Definition topS := SPEC reserving (3 + extra_stack)
  PRE[_] mallocHeap 0
  POST[R] [| R = 0 |] * mallocHeap 0.

Definition top := bimport [[ ("return_zero"!"return_zero", fspec) ]]
  bmodule "top" {{
    bfunction "top"("R") [topS]
      "R" <-- Call "return_zero"!"return_zero"(extra_stack)
      [PRE[_, R] [| R = 0 |]
       POST[R'] [| R' = R |] ];;
      Return "R"
    end
  }}.

Require Import Arith.
Require Import WordFacts.
Require Import CompileStmtTactics.

Lemma body_safe : forall env v, Safe env (Body f) v.
  econstructor; eauto.
Qed.

Lemma body_runsto : forall env v v', RunsTo env (Body f) v v'
  -> sel (fst v') (RetVar f) = 0 /\ snd v' = snd v.
  intros.
  inversion_clear H.
  subst vs.
  simpl.
  split.
  apply sel_upd_eq; auto.
  auto.
Qed.

Import InvMake.SemanticsMake.

Require Import MakeADT.
Module Import Made := Make(ExampleADT)(ExampleRepInv).

About fs_good_to_use.

Ltac hiding tac :=
  clear_imports;
  ((let P := fresh "P" in
    match goal with
      | H : Safe ?fs _ _ |- _ => set (P := Safe fs) in *
      | H : RunsTo ?fs _ _ _ |- _ => set (P := RunsTo fs) in *
      | H : fs_good_to_use ?a ?b ?c ?d |- _ => set (P := fs_good_to_use a b c d) in *
    end;
    hiding tac;
    subst P) || tac).


Theorem top_ok : moduleOk top.
  vcgen.

  sep_auto.
  sep_auto.
  sep_auto.

  Ltac prelude_out :=
    match goal with
      | [ |- himp _ (locals ?ns1 _ _ _) (locals ?ns2 _ _ _) ] =>
        let ns := peelPrefix ns2 ns1 in
          etransitivity; [ | eapply prelude_out with (ns' := ns); simpl; omega ];
          sep_auto
    end.

  prelude_out.

  sep_auto.

  post.
  Ltac call_cito args :=
    match goal with
      | [ H : context[locals ?ns ?vs ?res ?sp] |- _ ] =>
        let offset := eval simpl in (4 * length ns)%nat in
          change (locals ns vs res sp) with (locals_call ns vs res sp
            ("rp" :: "extra_stack" :: args) extra_stack offset) in H;
          assert (ok_call ns ("rp" :: "extra_stack" :: args) res extra_stack offset) by
            (split; [ simpl; omega
              | split; [ simpl; omega
                | split; [ NoDup
                  | reflexivity ] ] ])
    end.

  call_cito (@nil string).
  hiding ltac:(evaluate auto_ext).
  unfold name_marker.
  hiding ltac:(step auto_ext).
  unfold spec_without_funcs_ok.
  post.
  descend.

  Theorem is_state_in' : forall vs sp args e_stack F,
    locals ("rp" :: "extra_stack" :: args) vs e_stack sp
    * mallocHeap 0 * F
    ===> is_state sp (sel vs "rp") (wordToNat (sel vs "extra_stack")) e_stack nil
    (vs, heap_empty) (toArray args vs) * mallocHeap 0 * F.
    intros; sepLemma.
    etransitivity; [ | apply is_state_in ]; auto.
    sepLemma.
  Qed.

  eapply CompileExprs.change_hyp; [ |
    change (@nil W) with (toArray nil (upd x3 "extra_stack" 10)); apply is_state_in' ].
  autorewrite with sepFormula.
  hiding ltac:(step auto_ext).

  apply body_safe.
  hiding ltac:(step auto_ext).

  repeat ((apply existsL; intro) || (apply injL; intro) || apply andL); reduce.
  apply swap; apply injL; intro.
  openhyp.
  match goal with
    | [ x : State |- _ ] => destruct x; simpl in *
  end.

  Lemma replace_imp : forall specs P P' Q st,
    P ===> P'
    -> interp specs (![P'] st ---> Q)%PropX
    -> interp specs (![P] st ---> Q)%PropX.
    intros.
    eapply Imply_trans; try apply H0.
    rewrite sepFormula_eq.
    apply H.
  Qed.

  Import LinkMake.StubsMake.StubMake.LinkSpecMake2.CompileFuncSpecMake.InvMake.

  Opaque mult.

  Theorem is_state_out'' : forall sp rp args pairs vs e_stack e_stack',
    NoDup args
    -> ~List.In "rp" args
    -> ~List.In "extra_stack" args
    -> length args = length pairs
    -> is_state sp rp e_stack e_stack' nil
    (vs, make_heap pairs) (List.map fst pairs)
    ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp
    * is_heap (make_heap pairs) * [| sel vs' "extra_stack" = e_stack |]
    * [| saved_vars vs' args pairs |].
    unfold is_state, locals, Inv.has_extra_stack; simpl.
    intros.
    apply Himp_ex_c.
    exists (upd (upd (zip_vals args pairs) "extra_stack" e_stack) "rp" rp).
    selify.
    replace (S (S (length args)) * 4)%nat with (8 + 4 * length args)%nat by omega.
    rewrite map_length.
    rewrite <- H2.
    rewrite natToWord_plus.
    eapply Himp_trans; [ | do 4 (apply Himp_star_frame; [ | apply Himp_refl ]);
      apply Himp_star_frame; [ apply Himp_refl | apply ptsto32m'_out ] ].
    simpl.
    generalize (List.map fst pairs); intro.
    unfold array at 1; simpl.
    sepLemma.
    do 2 (apply saved_vars_irrel; auto).
    eauto using saved_vars_zip_vars.

    etransitivity; [ apply himp_star_comm | ].
    apply himp_star_frame.
    etransitivity; [ | apply Arrays.ptsto32m'_in ].
    etransitivity; [ | apply ptsto32m_shift_base ].
    unfold array.
    instantiate (1 := 8).
    simpl.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    reflexivity.
    auto.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    unfold natToW.
    sepLemma.
  Qed.

  Theorem is_state_out' : forall sp rp F vs e_stack e_stack',
    (is_state sp rp e_stack e_stack' nil
      (vs, heap_empty) nil * mallocHeap 0) * F
    ===> Ex vs', locals ("rp" :: "extra_stack" :: nil) vs' e_stack' sp
    * [| sel vs' "extra_stack" = e_stack|]
    * mallocHeap 0 * F.
    intros.
    change heap_empty with (make_heap nil).
    change (@nil W) with (List.map (@fst W ArgIn) nil).
    eapply Himp_trans; [ do 2 (apply Himp_star_frame; [ | apply Himp_refl ]); apply is_state_out'' | ]; eauto.
    instantiate (1 := 0); simpl; tauto.
    simpl; tauto.
    auto.
    sepLemma.
  Qed.

  apply body_runsto in H11; simpl in H11; intuition subst.
  eapply replace_imp.
  change 10 with (wordToNat (sel (upd x3 "extra_stack" 10) "extra_stack")).
  apply is_state_out'.
  hiding ltac:(step auto_ext).
  hiding ltac:(step auto_ext).
  rewrite H13.
  replace (Regs st Sp ^- natToW 8 ^+ natToW (4 * 2)) with (Regs st Sp).
  hiding ltac:(step auto_ext).
  Transparent mult.
  unfold natToW.
  simpl.
  words.
  step auto_ext.

  hiding ltac:(step auto_ext).
  descend; hiding ltac:(step auto_ext).
  descend; hiding ltac:(step auto_ext).
  words.
  descend; hiding ltac:(step auto_ext).

  sep_auto.
  sep_auto.
  sep_auto.
Qed.

(* linking *)

Require Import GoodOptimizer ConstFolding ElimDead.

Definition opt := compose ConstFolding.opt ElimDead.opt.

Module Import GoodOptimizerMake := GoodOptimizer.Make ExampleADT.
Module Import ConstFoldingMake := ConstFolding.Make ExampleADT.
Module Import ElimDeadMake := ElimDead.Make ExampleADT.

Lemma opt_good : GoodOptimizer opt.
  eapply GoodOptimizer_trans.
  eapply ConstFoldingMake.good_optimizer.
  eapply ElimDeadMake.good_optimizer.
Qed.

Require Import Link.
Module Import LinkMake := Link.Make ExampleADT ExampleRepInv.

Definition link_with_adts m := result (m :: nil) (empty _) opt_good.

Definition impl := link_with_adts gm.
Definition all := link top impl.

Require Import GeneralTactics2.

Import LinkMake.LMF.
Import LinkModuleImplsMake.

Import SSF.
Require Import StructuredModuleFacts.
Require Import ConvertLabelMap.
Import GLabelMapFacts.

Close Scope nat.

Import GLabelMap.

Ltac impl_ok :=
  eapply result_ok; [ intuition | NoDup | hnf; simpl; tauto
    | intros; match goal with
                | [ H : _ |- _ ] => eapply empty_in_iff in H; tauto
              end ].

Ltac link ok1 :=
  eapply linkOk; [ eapply ok1 | impl_ok
    | reflexivity
    | simpl; unfold CompileModuleMake.mod_name; unfold impl_module_name;
      simpl; link_simp; eauto
    | simpl; unfold CompileModuleMake.mod_name; unfold impl_module_name;
      simpl; unfold StubsMake.StubMake.bimports_diff_bexports;
        simpl; unfold StubsMake.StubMake.LinkSpecMake2.func_impl_export;
          simpl; unfold StubsMake.StubMake.LinkSpecMake2.impl_label;
            unfold impl_module_name; simpl; unfold CompileModuleMake.imports; simpl;
              link_simp; eauto
    | simpl; link_simp; eauto ].

Theorem all_ok : moduleOk all.
  link top_ok.
Qed.
