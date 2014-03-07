Set Implicit Arguments.

Require Import MakeWrapper ExampleADT ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.

Require Import Notations4.
Module Import Notations4Make := Make ExampleADT.

Open Scope nat.

Fixpoint fact_partial' start n :=
  match n with
    | 0 => 1
    | S n' => start * fact_partial' (1 + start) n'
  end.

(* (a+1) * (a+2) * ... * b  (1 when a>=b) *)
Definition fact_partial (a b : nat) := fact_partial' (1 + a) (b - a).

Definition fact_partial_w (a b : W) : W := natToW (fact_partial (wordToNat a) (wordToNat b)).

Import ProgramLogicMake.

Definition body := (
    "ret" <- 1 ;;
    [ fun v0 v => 
        sel (fst v) "ret" = fact_partial_w (sel (fst v) "n") (sel (fst v0) "n") /\ 
        (sel (fst v) "n" <= sel (fst v0) "n")%word /\
        snd v = snd v0 ]
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

Require Import Arith.

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

Open Scope word.

Lemma is_true_0_lt : forall v v' (x : string), is_true (0 < x)%expr v v' -> $0 < sel (fst v') x.
  intros.
  unfold is_true, abs in *.
  simpl in *.
  unfold wltb in *.
  destruct (wlt_dec _ _).
  eauto.
  intuition.
Qed.

Definition fact_w (w : W) := natToW (fact (wordToNat w)).

Require Import NPeano.
Import NPeano.Nat.

Lemma fact_partial'_inv : forall n start, fact_partial' start n * (n + start) = start * fact_partial' (1 + start) n.
  Opaque mult.
  induction n; simpl; intuition.
  repeat rewrite <- IHn.
  rewrite mult_assoc.
  repeat rewrite <- IHn.
  ring.
  Transparent mult.
Qed.

Lemma fact_partial_0 : forall n, fact_partial 0 n = fact n.
  unfold fact_partial.
  induction n; simpl; intuition.
  rewrite plus_0_r in *.
  rewrite sub_0_r in *.
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
  intros.
  unfold fact_partial_w.
  f_equal.
  unfold fact_partial.
  rewrite minus_diag.
  simpl; eauto.
Qed.

Open Scope nat.

Lemma fact_partial_update : forall a b, 0 < a -> a <= b -> a * fact_partial a b = fact_partial (a - 1) b.
  intros.
  unfold fact_partial.
  Opaque mult.
  simpl.
  replace (b - (a - 1)) with (S (b - a)).
  replace (S (a - 1)) with a.
  simpl.
  eauto.
  omega.
  omega.
  Transparent mult.
Qed.

Require Import WordFacts WordFacts2 WordFacts3 WordFacts4 WordFacts5.
Require Import GeneralTactics2.

Open Scope word.

Lemma fact_partial_w_update : forall (a b : W), $0 < a -> a <= b -> a ^* fact_partial_w a b = fact_partial_w (a ^- $1) b.
  unfold fact_partial_w.
  intros.
  set (wordToNat a).
  set (wordToNat (_ ^- _)).
  replace a with (natToW (wordToNat a)).
  rewrite wmult_natToW_comm.
  f_equal.
  subst n n0.
  replace (wordToNat (_ ^- _)) with (wordToNat a - 1).
  eapply fact_partial_update.
  nomega.
  nomega.
  Focus 2.
  eapply natToWord_wordToNat.
  rewrite wordToNat_wminus.
  rewrite roundTrip_1.
  eauto.
  eapply non_zero_wge1.
  nintro.
  subst.
  nomega.
Qed.

Definition empty_precond : assert := fun v0 v => v0 = v.

Lemma vcs_good : and_all (vc body empty_precond).
  unfold body, empty_precond; simpl.
  unfold imply_close, and_lift, interp, abs; simpl.
  descend.
  openhyp.
  subst.
  simpl.
  split.
  rewrite sel_upd_ne by eauto.
  rewrite H0.
  symmetry; eapply fact_partial_w_same.
  eauto.
  openhyp; simpl in *.
  destruct v; destruct v'; simpl in *.
  sel_upd_simpl.
  subst.
  eapply is_true_0_lt in H2.
  simpl in *.
  sel_upd_simpl.
  split.
  rewrite H1.
  rewrite H0.
  rewrite <- fact_partial_w_update.
  words.
  eauto.
  eauto.
  split.
  rewrite H0.
  nomega.
  eauto.
  eauto.
Qed.

Lemma body_runsto : forall stn fs v v', stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = fact_w (sel (fst v) "n") /\ snd v' = snd v.
  intros.
  unfold f in *; simpl in *.
  eapply sound_runsto' with (p := empty_precond) in H1.
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
  symmetry.
  eapply wle_0_eq; eauto.
  eapply vcs_good.
  unfold interp, empty_precond; eauto.
Qed.

Lemma body_safe : forall stn fs v, stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  intros.
  unfold f in *; simpl in *.
  eapply sound_safe with (p := empty_precond).
  instantiate (1 := body).
  eauto.
  eapply vcs_good.
  unfold interp, empty_precond; eauto.
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
