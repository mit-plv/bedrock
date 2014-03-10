Set Implicit Arguments.

Require Import MakeWrapper ExampleADT ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.

Require Import Notations4.
Module Import Notations4Make := Make ExampleADT.

Require Import Arith.
Import ProgramLogicMake.
Open Scope nat.

Definition DirectCall x f args := (LabelEx "_f" f ;; CallEx x "_f" args)%stmtex.

Notation "'DCall' f ()" := (DirectCall None f nil)
  (no associativity, at level 95, f at level 0) : stmtex_scope.

Notation "'DCall' f ( x1 , .. , xN )" := (DirectCall None f (@cons Expr x1 (.. (@cons Expr xN nil) ..))%expr)
  (no associativity, at level 95, f at level 0) : stmtex_scope.
 
Notation "x <-- 'DCall' f ()" := (DirectCall (Some x) f nil)
  (no associativity, at level 95, f at level 0) : stmtex_scope.

Notation "x <-- 'DCall' f ( x1 , .. , xN )" := (DirectCall (Some x) f (@cons Expr x1 (.. (@cons Expr xN nil) ..))%expr) (no associativity, at level 95, f at level 0) : stmtex_scope.

Notation "a ! b" := (a, b) (only parsing) : stmtex_scope.

Notation value := 42.

Definition body := (
  "c" <-- DCall "ADT"!"SimpleCell_new" ();;
  DCall "ADT"!"SimpleCell_write"("c", value);;
  "ret" <-- DCall "ADT"!"SimpleCell_read"("c");;
  DCall "ADT"!"SimpleCell_delete"("c")
  )%stmtex.

Definition f := (
  cfunction "use_cell"()
    body            
  end
)%Citofuncs.

Definition m := cmodule "use_cell" {{
  f
}}.

Lemma good : IsGoodModule m.
  good_module.
Qed.

Definition gm := to_good_module good.

Import LinkSpecMake2.

Notation " [[ ]] " := nil.
Notation " [[ x , .. , y ]] " := (cons x .. (cons y nil) ..).

Notation "name @ [ p ]" := (name%stmtex, p) (only parsing).

Require Import ExampleImpl.

Definition modules := [[ gm ]].
Definition imports := of_list [[ 
                                  "ADT"!"SimpleCell_new" @ [SimpleCell_newSpec],
                                  "ADT"!"SimpleCell_write" @ [SimpleCell_writeSpec],
                                  "ADT"!"SimpleCell_read" @ [SimpleCell_readSpec],
                                  "ADT"!"SimpleCell_delete" @ [SimpleCell_deleteSpec]
                              ]].

Definition fspec := func_spec modules imports ("use_cell"!"use_cell")%stmtex f.

Notation extra_stack := 100.

Definition topS := SPEC reserving (4 + extra_stack)
  PREonly[_] mallocHeap 0.

Notation input := 5.

Definition top := bimport [[ ("use_cell"!"use_cell", fspec), "sys"!"printInt" @ [printIntS],
                             "sys"!"abort" @ [abortS] ]]
  bmodule "top" {{
    bfunction "top"("R") [topS]
      "R" <-- Call "use_cell"!"use_cell"(extra_stack)
      [PREonly[_, R] [| R = value |] ];;

      Call "sys"!"printInt"("R")
      [PREonly[_] Emp ];;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Definition empty_precond : assert := fun _ v0 v => v0 = v.

Require Import WordFacts2 WordFacts5.
Import LinkSpecMake.

Lemma vcs_good : forall stn fs, stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> and_all (vc body empty_precond) (from_bedrock_label_map (Labels stn), fs stn).
  unfold empty_precond.
  Ltac cito_vcs body := unfold body; simpl;
    unfold imply_close, and_lift, interp; simpl(* ; *)
      (* firstorder cito'; auto *).

  cito_vcs body.
  intros; descend; intros; openhyp.
  cito'.
  econstructor.
  simpl.
  unfold from_bedrock_label_map.
  unfold stn_good_to_use in *.
  eapply H.
  unfold imports in *.
  right.
  eapply mem_in_iff.
  reflexivity.

  Ltac inversion_RunsTo :=
    change ProgramLogicMake.SemanticsMake.RunsTo with RunsTo in *;
    match goal with
      | H : RunsTo _ _ _ _ |- _ => inversion H; unfold_all; subst;simpl in *; clear H
    end.

  Ltac cito' :=
    repeat (subst; simpl; selify; autorewrite with sepFormula in *; repeat inversion_RunsTo;
      repeat match goal with
               | [ H : _ |- _ ] => rewrite H
             end).

  cito'.
  eapply SafeCallForeign; simpl.
  unfold from_bedrock_label_map in *.
  unfold fs_good_to_use in *.
  eapply H0.
  descend.
  eauto.
  right.
  descend.
  eauto.
  unfold imports.
  reflexivity.
  instantiate (1 := nil).
  eauto.
  Require Import Semantics.
  unfold good_inputs; descend; unfold disjoint_ptrs; simpl; eauto.
  simpl; eauto.

  econstructor.
  simpl.
  unfold from_bedrock_label_map.
  eapply H.
  unfold imports in *.
  right.
  eapply mem_in_iff.
  reflexivity.
  
  inversion H4; unfold_all; subst; simpl in *; clear H4.
  unfold from_bedrock_label_map in *.

  Lemma sel_upd_eq' : forall vs nm v nm', nm = nm' -> (upd vs nm v) nm' = v.
    intros; eapply sel_upd_eq; eauto.
  Qed.

  Lemma sel_upd_ne' : forall vs nm v nm', nm <> nm' -> (upd vs nm v) nm' = sel vs nm'.
    intros; eapply sel_upd_ne; eauto.
  Qed.

  Ltac sel_upd_simpl :=
    repeat 
      match goal with
        | H : _ |- _ => rewrite sel_upd_eq in H by reflexivity
        | H : _ |- _ => rewrite sel_upd_ne in H by discriminate
        | |- _ => rewrite sel_upd_eq by reflexivity
        | |- _ => rewrite sel_upd_ne by discriminate
        | H : _ |- _ => rewrite sel_upd_eq' in H by reflexivity
        | H : _ |- _ => rewrite sel_upd_ne' in H by discriminate
        | |- _ => rewrite sel_upd_eq' by reflexivity
        | |- _ => rewrite sel_upd_ne' by discriminate
      end.

  assert (fs0 stn w = Some (Foreign SimpleCell_newSpec)).
  eapply H0.
  descend.
  eauto.
  right.
  descend.
  eauto.
  unfold imports.
  reflexivity.
  inversion H3; unfold_all; subst; simpl in *; clear H3.
  sel_upd_simpl.
  rewrite H1 in H7; intuition.
  sel_upd_simpl.
  rewrite H1 in H7; injection H7; intros; subst.
  cito'.
  openhyp.
  subst.
  unfold decide_ret in *; simpl in *.
  eapply SafeCallForeign; simpl in *.
  sel_upd_simpl.
  eapply H0.
  descend.
  eauto.
  right.
  descend.
  eauto.
  unfold imports.
  reflexivity.
  sel_upd_simpl.
  instantiate (1 := [[ (addr, inr (Cell 0)), ($42, inl ($42)) ]]).
  eauto.
  unfold good_inputs.
  split.
  unfold word_adt_match.
  econstructor.
  simpl.
  Require Import WordMapFacts.
  eapply find_mapsto_iff.
  eapply add_mapsto_iff.
  eauto.
  econstructor.
  simpl.
  eauto.
  econstructor.
  unfold disjoint_ptrs.
  simpl.
  NoDup.
  simpl.
  descend; eauto.
(*here*)
  admit.
  admit.
  admit.
  admit.
  eauto.
Qed.

Local Hint Immediate vcs_good.

(*
Theorem final : forall n x r,
  ($0 >= n)%word
  -> x = r ^* fact_w n
  -> r = x.
  intros; subst.
  assert (n = $0) by (apply wordToNat_inj; nomega).
  subst.
  change (fact_w $0) with (natToW 1).
  words.
Qed.

Local Hint Resolve final.

Lemma body_runsto : forall stn fs v v', stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = fact_w (sel (fst v) "n") /\ snd v' = snd v.
  cito_runsto f empty_precond; eauto.
Qed.

Lemma body_safe : forall stn fs v, stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  cito_safe f body empty_precond.
Qed.
*)

Lemma body_safe : forall stn fs v, stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  admit.
Qed.

Lemma body_runsto : forall stn fs v v', stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = value /\ snd v' = snd v.
  admit.
Qed.

Require Import Inv.
Module Import InvMake := Make ExampleADT.
Module Import InvMake2 := Make ExampleRepInv.
Import Made.

Theorem top_ok : moduleOk top.
  vcgen.

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.

  post.
  call_cito 100 (@nil string).
  hiding ltac:(evaluate auto_ext).
  unfold name_marker.
  hiding ltac:(step auto_ext).
  unfold spec_without_funcs_ok.
  post.
  descend.
  eapply CompileExprs.change_hyp.
  Focus 2.
  apply (@is_state_in''' (upd x2 "extra_stack" 100)).
  autorewrite with sepFormula.
  clear H7 H8.
  hiding ltac:(step auto_ext).
  apply body_safe; eauto.
  hiding ltac:(step auto_ext).
  repeat ((apply existsL; intro) || (apply injL; intro) || apply andL); reduce.
  apply swap; apply injL; intro.
  openhyp.
  Import LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.
  match goal with
    | [ x : State |- _ ] => destruct x; simpl in *
  end.
  apply body_runsto in H9; simpl in H9; intuition subst.
  eapply replace_imp.
  change 100 with (wordToNat (sel (upd x2 "extra_stack" 100) "extra_stack")).
  apply is_state_out''''.
  NoDup.
  NoDup.
  NoDup.
  hiding ltac:(step auto_ext).
  hiding ltac:(step auto_ext).

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
Qed.

Import LinkMake.

Definition link_with_adts modules imports := result modules imports opt_good.

Definition all := link top (link_with_adts [[gm]] imports).

Theorem all_ok : moduleOk all.

  Require Import LinkFacts.
  Module Import LinkFactsMake := Make ExampleADT.

  Ltac impl_ok :=
    match goal with
      | |- moduleOk (link_with_adts ?Modules ?Imports ) =>
        let H := fresh in
        assert (GoodToLink_bool Modules Imports = true); 
          [ unfold GoodToLink_bool; simpl |
            eapply GoodToLink_bool_sound in H; openhyp; simpl in *; eapply result_ok; simpl in * ]
          ; eauto
    end.

  Import LinkModuleImplsMake.

  Ltac link0 ok1 :=
    eapply linkOk; [ eapply ok1 | impl_ok
      | reflexivity
      | simpl; unfold CompileModuleMake.mod_name; unfold impl_module_name;
        simpl; unfold StubsMake.StubMake.bimports_diff_bexports;
          simpl; unfold StubsMake.StubMake.LinkSpecMake2.func_impl_export;
            simpl; unfold StubsMake.StubMake.LinkSpecMake2.impl_label;
              unfold impl_module_name; simpl; unfold CompileModuleMake.imports; simpl;
                link_simp; eauto ..
                   ].

  link0 top_ok.
Qed.
