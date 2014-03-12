Set Implicit Arguments.

Require Import MakeWrapper ExampleADT ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.

Require Import Notations4.
Module Import Notations4Make := Make ExampleADT.

Require Import Arith.
Import ProgramLogicMake.
Open Scope nat.

Definition fact_w (w : W) := natToW (fact (wordToNat w)).

Definition body := (
  If ("n" <= 0) {
    "ret" <- 1
  } else {
    "ret" <-- DCall "fact"!"fact" ("n" - 1)
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

Import LinkSpecMake2.

Notation " [[ ]] " := nil.
Notation " [[ x , .. , y ]] " := (cons x .. (cons y nil) ..).

Notation "name @ [ p ]" := (name%stmtex, p) (only parsing).

Definition modules := [[ gm ]].
Definition imports := empty ForeignFuncSpec.

Definition fspec := func_spec modules imports ("fact"!"fact")%stmtex f.

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
(*
Lemma vcs_good : forall env, and_all (vc body empty_precond) env.
  unfold empty_precond; cito_vcs body; words.
Qed.

Local Hint Immediate vcs_good.
*)
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

Require Import SemanticsFacts4.
Module Import SemanticsFacts4Make := Make ExampleADT.

Definition fact_spec : ForeignFuncSpec :=
  {|
    PreCond := fun args => exists n, args = inl n :: nil;
    PostCond := fun args ret => exists n, args = (inl n, None) :: nil
                                          /\ ret = inl (fact_w n)
  |}.

Definition change_fs (fs : settings -> W -> option Callee) : settings -> W -> option Callee := 
  fun stn w =>
    match fs stn w with
      | None => None
      | Some _ => Some (Foreign fact_spec)
    end.

Definition fs_good_to_use' specs (fs : settings -> W -> option Callee) (stn : settings) :=
  forall p spec, 
    fs stn p = Some spec <-> 
    exists lbl : glabel,
      Labels stn lbl = Some p /\
      find lbl specs = Some spec.

Definition specs := add ("fact", "fact") (Foreign fact_spec) (empty _).

Lemma body_runsto' : forall stn fs v v', stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use' specs fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = fact_w (sel (fst v) "n") /\ snd v' = snd v.
  admit.
(* cito_runsto f empty_precond; eauto. *)
Qed.

Definition dummy_gf : GoodFunction.
  refine (to_good_function f _).
  good_module.
Defined.    

Definition spec_op := hd dummy_gf (Functions gm).

Definition specs_op := add ("fact", "fact") (Internal spec_op) (empty _).

Lemma fs_good_gm : forall fs stn, fs_good_to_use [[gm]] (empty _) fs stn -> fs_good_to_use' specs_op fs stn.
  intros.
  unfold fs_good_to_use, fs_good_to_use' in *.
  split; intros.
  eapply H in H0.
  openhyp.
  subst.
  descend; eauto.
  unfold specs_op.
  eapply find_mapsto_iff.
  eapply add_mapsto_iff.
  left.
  unfold spec_op, gm, to_good_module in *; simpl in *.
  openhyp.
  subst; simpl in *.
  openhyp.
  subst; simpl in *.
  eauto.
  intuition.
  intuition.
  rewrite empty_o in H2; intuition.
  openhyp.
  unfold specs_op in *.
  eapply find_mapsto_iff in H1.
  eapply add_mapsto_iff in H1.
  openhyp.
  subst.
  eapply H.
  descend; eauto.
  left.
  descend; eauto.
  unfold spec_op, gm, to_good_module; simpl; eauto.
  eapply empty_mapsto_iff in H2; intuition.
Qed.

Lemma change_fs_good : forall fs stn, fs_good_to_use [[gm]] (empty ForeignFuncSpec) fs stn -> fs_good_to_use' specs (change_fs fs) stn.
  intros.
  eapply fs_good_gm in H.
  unfold fs_good_to_use', change_fs in *.
  split; intros.
  destruct (option_dec (fs0 stn p)).
  destruct s; rewrite e in *.
  injection H0; intros; subst.
  eapply H in e.
  openhyp.
  unfold specs_op in *.
  eapply find_mapsto_iff in H2.
  eapply add_mapsto_iff in H2.
  openhyp.
  subst.
  descend; eauto.
  eapply empty_mapsto_iff in H3; intuition.
  rewrite e in *; intuition.
  openhyp.
  unfold specs in *.
  eapply find_mapsto_iff in H1.
  eapply add_mapsto_iff in H1.
  openhyp.
  subst.
  assert (fs0 stn p = Some (Internal spec_op)).
  eapply H.
  descend; eauto.
  rewrite H1; eauto.
  eapply empty_mapsto_iff in H2; intuition.
Qed.

Lemma map_length_eq : forall A B ls1 ls2 (f : A -> B), List.map f ls1 = ls2 -> length ls1 = length ls2.
  intros.
  eapply f_equal with (f := @length _) in H.
  simpl in *; rewrite map_length in *; eauto.
Qed.

Lemma body_safe' : forall stn fs v, stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use' specs fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  admit.
Qed.

Lemma change_fs_strengthen : forall fs stn, stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use [[gm]] (empty ForeignFuncSpec) fs stn ->strengthen (from_bedrock_label_map (Labels stn), fs stn) (from_bedrock_label_map (Labels stn), change_fs fs stn).
  intros.
  generalize H0; intro.
  eapply fs_good_gm in H0.
  unfold fs_good_to_use' in *.
  unfold strengthen.
  split.
  eauto.
  unfold change_fs at 1.
  unfold change_fs at 1.
  simpl.
  intros.
  destruct (option_dec (fs0 stn w)); simpl in *.
  destruct s; rewrite e in *; simpl in *.
  eapply H0 in e.
  openhyp.
  unfold specs_op in H3.
  eapply find_mapsto_iff in H3.
  eapply add_mapsto_iff in H3.
  openhyp.
  subst.
  right; descend.
  eauto.
  eauto.
  descend.
  unfold PreCond in *; simpl in *.
  openhyp.
  erewrite map_length_eq; eauto.
  eauto.
  eapply body_safe'; eauto.
  eapply change_fs_good; eauto.
  eapply body_runsto' in H3; eauto.
  2 : eapply change_fs_good; eauto.
  openhyp.
  descend.
  instantiate (1 := [[ {| Word := sel (fst v) "n"; ADTIn := inl (sel (fst v) "n"); ADTOut := None |} ]]).
  eauto.
  repeat econstructor.
  descend; eauto.
  descend; eauto.
  repeat econstructor.
  simpl.
  Import SemanticsMake.
  unfold store_out, Semantics.store_out; simpl; eauto.
  unfold f in *; simpl in *.
  rewrite H3.
  eauto.
  eapply empty_mapsto_iff in H4; intuition.
  rewrite e in *.
  eauto.
  Grab Existential Variables.
  eauto.
Qed.

Lemma body_runsto : forall stn fs v v', stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = fact_w (sel (fst v) "n") /\ snd v' = snd v.
  intros.
  eapply strengthen_runsto with (env_ax := (from_bedrock_label_map (Labels stn), change_fs fs0 stn)) in H1.
  eapply body_runsto'; eauto.
  eapply change_fs_good; eauto.
  eapply change_fs_strengthen; eauto.
Qed.

Lemma body_safe : forall stn fs v, stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  intros.
  eapply strengthen_safe.
  eapply body_safe'; eauto.
  eapply change_fs_good; eauto.
  eapply change_fs_strengthen; eauto.
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

Definition all := link top (link_with_adts (gm :: nil) (empty _)).

Theorem all_ok : moduleOk all.
  link0 top_ok.
Qed.