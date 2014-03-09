Set Implicit Arguments.

Require Import MakeWrapper ExampleADT ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.

Require Import Notations4.
Module Import Notations4Make := Make ExampleADT.

Open Scope nat.

Require Import Arith.

Definition fact_w (w : W) := natToW (fact (wordToNat w)).

Import ProgramLogicMake.

Definition body := (
    "ret" <- 1;;
    [BEFORE(V, h)
     AFTER(V', h')
       fact_w (V "n") = V' "ret" ^* fact_w (V' "n")
       /\ h' = h]
    While (0 < "n") {
      "ret" <- "ret" * "n";;
      "n" <- "n" - 1                          
    }
  )%stmtex.

Definition f := (
  cfunction "fact"("n")
    body            
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

Definition empty_precond : assert := fun _ v0 v => v0 = v.

Require Import WordFacts2 WordFacts5.

Lemma fact_step : forall n,
  ($0 < n)%word
  -> fact_w n = n ^* fact_w (n ^- $1).
  intros.
  unfold fact_w.
  rewrite wordToNat_positive by assumption.
  unfold fact at 1; fold fact.
  rewrite <- wordToNat_positive by assumption.
  unfold natToW; rewrite natToWord_mult.
  rewrite natToWord_wordToNat.
  reflexivity.
Qed.

Hint Rewrite fact_step using solve [ eauto 2 ] : sepFormula.

Lemma vcs_good : forall env, and_all (vc body empty_precond) env.
  unfold empty_precond; cito_vcs body; words.
Qed.

Local Hint Immediate vcs_good.

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

Import LinkSpecMake.

Lemma body_runsto : forall stn fs v v', stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = fact_w (sel (fst v) "n") /\ snd v' = snd v.
  Ltac cito_runsto f pre := intros;
    match goal with
      | [ H : _ _ _ _ _ |- _ ] => unfold f, Body, Core in H;
        eapply sound_runsto' with (p := pre) (s := Body f) in H; 
          simpl in *; try unfold pre in *; unfold imply_close, and_lift, interp in *; simpl in *;
            auto; openhyp; subst; simpl in *; intuition auto; unfold and_lift in *; openhyp
    end.

  cito_runsto f empty_precond; eauto.
Qed.

Lemma body_safe : forall stn fs v, stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  Ltac cito_safe f body pre := intros;
    unfold f, body, Body, Core; eapply sound_safe with (p := pre); [ reflexivity | eauto | .. ];
      simpl in *; try unfold pre in *; unfold imply_close, and_lift, interp in *; simpl in *;
        auto; openhyp; subst; simpl in *; intuition auto.

  cito_safe f body empty_precond.
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
