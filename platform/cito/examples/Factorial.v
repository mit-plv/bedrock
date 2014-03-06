Set Implicit Arguments.

Require Import MakeWrapper ExampleADT ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.

Require Import Notations4.
Module Import Notations4Make := Make ExampleADT.

Open Scope nat.

Require Import Arith.

Definition fact_w (w : W) := natToW (fact (wordToNat w)).

Fixpoint fact_partial' start n :=
  match n with
    | 0 => 1
    | S n' => start * fact_partial' (1 + start) n'
  end.

(* (a+1) * (a+2) * ... * b  (1 when a>=b) *)
Definition fact_partial (a b : nat) := fact_partial' (1 + a) (b - a).

Definition fact_partial_w (a b : W) : W := natToW (fact_partial (wordToNat a) (wordToNat b)).

Set Printing Coercions.

Lemma fact_partial_0 : forall n, fact_partial 0 n = fact n.
  unfold fact_partial.
  induction n; simpl; intuition.
  rewrite plus_0_r in *.
  Require Import NPeano.
  Import NPeano.Nat.
  rewrite sub_0_r in *.
  Lemma fact_partial'_inv : forall n start, fact_partial' start n * (n + start) = start * fact_partial' (1 + start) n.
    Opaque mult.
    induction n; simpl; intuition.
    repeat rewrite <- IHn.
    rewrite mult_assoc.
    repeat rewrite <- IHn.
    ring.
    Transparent mult.
  Qed.
  specialize (fact_partial'_inv n 1); intro; simpl in *.
  rewrite plus_0_r in *.
  rewrite <- H.
  rewrite IHn.
  ring.
Qed.

Lemma fact_partial_w_0 : forall w, fact_partial_w $0 w = fact_w w.
  intros.
  unfold fact_partial_w, fact_w.
  f_equal.
  change (wordToNat $0) with 0.
  eapply fact_partial_0.
Qed.

Lemma fact_partial_w_same : forall w, fact_partial_w w w = 1.
  admit.
Qed.

Import ProgramLogicMake.

Definition body := (
    "ret" <- 1 ;;
    [ fun v0 v => sel (fst v) "ret" = fact_partial_w (sel (fst v) "n") (sel (fst v0) "n") /\ snd v = snd v0 ]
    While (0 < "n") {
      "ret" <- "ret" * "n" ;;
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

Import LinkSpecMake.

Lemma body_runsto : forall stn fs v v', stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = fact_w (sel (fst v) "n") /\ snd v' = snd v.
  intros.
  unfold f in *; simpl in *.
  eapply sound_runsto' with (p := fun v0 v => v0 = v) in H1.
  2 : instantiate (1 := body); simpl; eauto.
  simpl in *.
  unfold and_lift, interp, abs in *.
  openhyp.
  split.
  2 : eauto.
  rewrite H1.
  replace (sel (fst v') "n") with (natToW 0).
  eapply fact_partial_w_0.
  unfold is_false, abs in *; simpl in *.
  unfold wltb in *.
  destruct wlt_dec; try discriminate.
  Close Scope nat.
  Lemma wle_0_eq : forall w : W, w <= $0 -> w = $0.
    intros.
    unfold wlt in *.
    destruct (N.eq_0_gt_0_cases (wordToN w)).
    change (0)%N with (wordToN (natToW 0)) in H0.
    eapply wordToN_inj in H0.
    eauto.
    change (wordToN ($ 0)) with 0%N in H.
    intuition.
  Qed.
  symmetry.
  eapply wle_0_eq; eauto.
  simpl in *.
  unfold imply_close, and_lift, interp, abs.
  descend.
  openhyp.
  subst.
  simpl.
  split.
  rewrite sel_upd_ne by eauto.
  rewrite H3.
  symmetry; eapply fact_partial_w_same.
  eauto.
  openhyp; simpl in *.
  destruct v0; destruct v'0; simpl in *.
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
  sel_upd_simpl.
  subst.
  split.
  rewrite H4.
  rewrite H3.
  admit.
  eauto.
  eauto.
  unfold interp.
  eauto.
Qed.

Lemma body_safe : forall stn fs v, stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
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
  Open Scope nat.
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
