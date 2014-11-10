Set Implicit Arguments.

Require Import ExampleImpl.

Require Import MakeWrapper.
Require Import ExampleADT ExampleRepInv.
Module Import MakeWrapperMake := Make(ExampleADT)(ExampleRepInv).
Export MakeWrapperMake.

Require Import DFacade.
Require Import Notations.
Import Notations.OpenScopes.

Require Import Arith.
Open Scope nat.

Definition use_cell := 
  module
  import {
    "ADT"!"SimpleCell_new" ==> SimpleCell_newSpec;
    "ADT"!"SimpleCell_delete" ==> SimpleCell_deleteSpec
  }
  define {
    def "use_cell" = func() {
      "c" <-- call_ "ADT"!"SimpleCell_new" ();
      "ret" <-- call_ "ADT"!"SimpleCell_read"("c");
      "tmp" <-- call_ "ADT"!"SimpleCell_delete"("c")
    }
  }.

Require Import CompileDFModule.

Definition use_cell_gm := compile_to_gmodule use_cell "use_cell" eq_refl.

Import LinkSpecMake2.

Definition modules := { use_cell_gm }.
Definition imports := DFModule.Imports use_cell.

Require Import GoodModuleDec.

Definition dummy_gf : GoodFunction.
  refine (to_good_function f _).
  eapply is_good_func_sound.
  reflexivity.
Defined.    

Definition spec_op := hd dummy_gf (Functions use_cell_gm).

Definition spec_op_b := func_spec modules imports ("use_cell"!"use_cell") spec_op.

Notation extra_stack := 20.

Definition topS := SPEC reserving (4 + extra_stack)
  PREonly[_] mallocHeap 0.

Notation input := 5.

Definition top := bimport [[ ("use_cell"!"use_cell", spec_op_b), "sys"!"printInt" @ [printIntS],
                             "sys"!"abort" @ [abortS] ]]
  bmodule "top" {{
    bfunction "top"("R") [topS]
      "R" <-- Call "use_cell"!"use_cell"(extra_stack)
      [PREonly[_, R] [| R = 0 |] ];;

      Call "sys"!"printInt"("R")
      [PREonly[_] Emp ];;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Import LinkSpecMake.
Require Import LinkSpecFacts.
Module Import LinkSpecFactsMake := Make ExampleADT.
Import LinkSpecMake.

Require Import CompileDFacadeToCito.
Require Import WordMap.
Require Import StringMap.
Require Import GLabelMap.

Import WordMapFacts.FMapNotations.
Local Open Scope fmap_scope.

Lemma env_good_to_use_cenv_impls_env modules imports stn fs : env_good_to_use modules imports stn fs -> cenv_impls_env (from_bedrock_label_map (Labels stn), fs stn) (GLabelMap.map (@Axiomatic _) imports).
  admit.
Qed.

Lemma body_safe : forall stn fs v, env_good_to_use modules imports stn fs -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body spec_op) v.
Proof.
  intros.
  destruct v as [vs h].
  eapply compile_safe; try reflexivity; simpl in *.
  Focus 2.
  simpl.
  reflexivity.
  Focus 3.
  instantiate (1 := @WordMap.empty _).
  admit.
  Focus 2.
  rewrite StringMapFacts.empty_o; eauto.
  Focus 2.
  admit.
  Focus 2.
  eapply env_good_to_use_cenv_impls_env; eauto.
  simpl.
  admit. (* safe *)
Qed.

Lemma body_runsto : forall stn fs v v', env_good_to_use modules imports stn fs -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body spec_op) v v' -> Locals.sel (fst v') (RetVar spec_op) = 0 /\ snd v' == snd v.
Proof.
  intros.
  eapply compile_runsto in H0; try reflexivity; simpl in *.
  Focus 2.
  instantiate (1 := @WordMap.empty _).
  admit.
  Focus 2.
  instantiate (1 := @StringMap.empty _).
  admit.
  Focus 2.
  rewrite StringMapFacts.empty_o; eauto.
  Focus 2.
  eapply env_good_to_use_cenv_impls_env; eauto.
  admit. (* runsto *)
  admit. (* safe *)
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
  call_cito 20 (@nil string).
  hiding ltac:(evaluate auto_ext).
  unfold name_marker.
  hiding ltac:(step auto_ext).
  unfold spec_without_funcs_ok.
  post.
  descend.
  eapply CompileExprs.change_hyp.
  Focus 2.
  apply (@is_state_in''' (upd x2 "extra_stack" 20)).
  autorewrite with sepFormula.
  clear H7.
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
  Require Import GeneralTactics3.
  eapply_in_any body_runsto; simpl in *; intuition subst.
  eapply replace_imp.
  change 20 with (wordToNat (Locals.sel (upd x2 "extra_stack" 20) "extra_stack")).
  apply is_state_out'''''.
  NoDup.
  NoDup.
  NoDup.
  eauto.

  clear H7.
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

Definition all := link top (link_with_adts modules imports).

Theorem all_ok : moduleOk all.
  link0 top_ok.
Qed.
