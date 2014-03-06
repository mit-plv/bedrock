Set Implicit Arguments.

Require Import AutoSep.

Require Import Notations.

Definition s :=
([
      PRE[V] Emp
      POST[R] Emp ]
    While ("x" <> 0) {
      "tmp2" <- "x";;
      "tmp1" <- "x" + 4;;
      "x" <-* "tmp1";;
      "tmp1" *<- "acc";;
      "acc" <- "tmp2"
    })%SP.

Require Import MakeWrapper ExampleADT ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.

Require Import Notations4.
Module Import Notations4Make := Make ExampleADT.

Definition fact_partial_w (a b : W) : W := $0.

Open Scope stmtex.

    ([  ]
    While (0 < "n") {
      "ret" <- "ret" * "n" ;;
      "n" <- "n" - 1                          
    })%SP.



(* fun v => sel (fst v) "ret" = fact_partial_w (sel (fst v) "n") (sel (fst v) "n0") *)

Definition f := (
  cfunction "fact"("n0") (
    "n" <- "n0" ;;
    "ret" <- 1 ;;
    [  ]
    While (0 < "n") {
      "ret" <- "ret" * "n" ;;
      "n" <- "n" - 1                          
    }
  )%stmtex
  end
)%Citofuncs.

Definition m := cmodule "fact" {{
  f
}}.

Lemma good : IsGoodModule m.
  good_module.
Qed.

Definition gm := to_good_module good.

Definition fspec :=
  cimport "fact"!"fact"
  cmodules [[ gm ]]
  definition f.

Notation extra_stack := 100.

Definition topS := SPEC reserving (4 + extra_stack)
  PREonly[_] mallocHeap 0.

Fixpoint fact n :=
  match n with
    | 0 => 1
    | S n' => (n * fact n')%nat
  end.

Notation input := 5.

Definition top := bimport [[ ("fact"!"fact", fspec), "sys"!"printInt" @ [printIntS],
                             "sys"!"abort" @ [abortS] ]]
  bmodule "top" {{
    bfunction "top"("R") [topS]
      "R" <-- Call "fact"!"fact"(extra_stack, input)
      [PREonly[_, R] [| R = fact input |] ];;

      Call "sys"!"printInt"("R")
      [PREonly[_] Emp ];;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Import LinkSpecMake.

Lemma body_safe : forall stn fs v, stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  admit.
Qed.

Lemma body_runsto : forall stn fs v v', stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = fact_w (sel (fst v) "n") /\ snd v' = snd v.
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
  call_cito 100 ("n" :: nil).
  hiding ltac:(evaluate auto_ext).
  unfold name_marker.
  hiding ltac:(step auto_ext).
  unfold spec_without_funcs_ok.
  post.
  descend.
  eapply CompileExprs.change_hyp.
  Focus 2.
  apply (@is_state_in''' (upd (upd x2 "extra_stack" 100) "n" input)).
  autorewrite with sepFormula.
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
  change 100 with (wordToNat (sel (upd (upd x2 "extra_stack" 100) "n" 5) "extra_stack")).
  apply is_state_out''''.
  NoDup.
  NoDup.
  NoDup.
  hiding ltac:(step auto_ext).
  hiding ltac:(step auto_ext).
  rewrite H10.
  rewrite H12.
  reflexivity.

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
Qed.

Definition all := link top (link_with_adts gm).

Theorem all_ok : moduleOk all.
  link0 top_ok.
Qed.
