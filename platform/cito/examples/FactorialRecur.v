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
  If (0 < "n") {
    "ret" <-- DCall "fact"!"fact" ("n" - 1);;
    (* Assert [ *)
    (*   BEFORE(V, h) *)
    (*   AFTER(V', h') *)
    (*   V' "ret" = fact_w (V "n" ^- $1) /\ h' = h ];; *)
    "ret" <- "n" * "ret"
  } else {
    "ret" <- 1
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

Definition dummy_gf : GoodFunction.
  refine (to_good_function f _).
  good_module.
Defined.    

Definition spec_op := hd dummy_gf (Functions gm).

Definition specs_op := add ("fact", "fact") (Internal spec_op) (empty _).

Lemma fs_good : forall fs stn, fs_good_to_use modules imports fs stn -> fs_good_to_use' specs_op fs stn.
  unfold modules, imports.
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

Lemma change_fs_good : forall fs stn, fs_good_to_use modules imports fs stn -> fs_good_to_use' specs (change_fs fs) stn.
  unfold modules, imports.
  intros.
  eapply fs_good in H.
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

Lemma stn_good : forall stn, stn_good_to_use modules imports stn -> from_bedrock_label_map (Labels stn) ("fact", "fact") <> None.
  intros.
  eapply H.
  left; descend.
  left; eauto.
  unfold gm, to_good_module; simpl; eauto.
  unfold gm, to_good_module; simpl; eauto.
Qed.

Lemma vcs_good : forall stn fs, stn_good_to_use modules imports stn -> fs_good_to_use' specs fs stn -> and_all (vc body empty_precond) (from_bedrock_label_map (Labels stn), fs stn).
  Ltac cito_vcs body := unfold body; simpl;
    unfold imply_close, and_lift, interp; simpl(* ; *)
      (* firstorder cito'; auto *).

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

  unfold empty_precond.

  cito_vcs body.
  intros; descend; intros; openhyp.
  cito'.
  econstructor; simpl.
  eapply stn_good; eauto.

  subst.
  inversion H2; unfold_all; subst; simpl in *; clear H2.
  unfold from_bedrock_label_map in *.

  eapply SafeCallForeign; simpl in *.
  sel_upd_simpl.
  eapply H0.
  descend; eauto.
  unfold specs; simpl.
  reflexivity.

  sel_upd_simpl.
  instantiate (1 := [[ (sel (fst x) "n" ^- $1, inl (sel (fst x) "n" ^- $1)) ]]).
  eauto.
  repeat constructor.
  unfold PreCond; simpl.
  descend; eauto.

  eauto.
Qed.

Local Hint Immediate vcs_good.

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

Theorem final : forall n,
  ($0 >= n)%word
  -> $1 = fact_w n.
  intros; subst.
  assert (n = $0) by (apply wordToNat_inj; nomega).
  subst.
  change (fact_w $0) with (natToW 1).
  words.
Qed.

Local Hint Resolve final.

Lemma body_runsto' : forall stn fs v v', stn_good_to_use modules imports stn -> fs_good_to_use' specs fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = fact_w (sel (fst v) "n") /\ snd v' = snd v.
  unfold modules, imports.

  Ltac cito_runsto f pre := intros;
    match goal with
      | [ H : _ |- _ ] => unfold f, Body, Core in H;
        eapply sound_runsto' with (p := pre) (s := Body f) in H;
          simpl in *; try eapply vcs_good; simpl in *;
            auto; openhyp; subst; simpl in *; (* intuition auto;  *)unfold empty_precond, and_lift, or_lift in *; openhyp; [ .. | eauto ]
    end.

  cito_runsto f empty_precond.
  Focus 2.
  cito'; eauto.

  subst.
  inversion H4; unfold_all; subst; simpl in *; clear H4.
  unfold from_bedrock_label_map in *.

  assert (fs0 stn w = Some (Foreign fact_spec)).
  eapply H0.
  descend.
  eauto.
  unfold specs; simpl.
  reflexivity.

  inversion H3; unfold_all; subst; simpl in *; clear H3.
  sel_upd_simpl; rewrite H1 in H8; discriminate.
  sel_upd_simpl; rewrite H1 in H8; injection H8; intros; subst.

  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  Fixpoint make_triples_2 words (in_outs : list (ArgIn * ArgOut)) :=
    match words, in_outs with
      | p :: ps, o :: os => {| Word := p; ADTIn := fst o; ADTOut := snd o |} :: make_triples_2 ps os
      | _, _ => nil
    end.

  Lemma triples_intro : forall triples words in_outs, words = List.map (@Word _) triples -> List.map (fun x => (ADTIn x, ADTOut x)) triples = in_outs -> triples = make_triples_2 words in_outs.
    induction triples; destruct words; destruct in_outs; simpl in *; intuition.
    f_equal; intuition.
    destruct a; destruct p; simpl in *.
    injection H; injection H0; intros; subst.
    eauto.
  Qed.

  eapply triples_intro in H3; try eassumption.
  subst; simpl in *.
  Import Semantics.
  unfold good_inputs in *.
  openhyp.
  unfold word_adt_match in *.
  Ltac inversion_Forall :=
    repeat match goal with
             | H : List.Forall _ _ |- _ => inversion H; subst; clear H
           end.

  inversion_Forall; simpl in *.
  subst.
  unfold store_out in *; simpl in *.

  inversion H2; unfold_all; subst; simpl in *; clear H2.
  sel_upd_simpl.
  split.
  symmetry; eapply fact_step; eauto.
  eauto.

Qed.

Lemma body_safe' : forall stn fs v, stn_good_to_use modules imports stn -> fs_good_to_use' specs fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  unfold modules, imports.
  cito_safe f body empty_precond.
Qed.

Lemma change_fs_strengthen : forall fs stn, stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn ->strengthen (from_bedrock_label_map (Labels stn), fs stn) (from_bedrock_label_map (Labels stn), change_fs fs stn).
  unfold modules, imports.
  intros.
  generalize H0; intro.
  eapply fs_good in H0.
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

Lemma body_runsto : forall stn fs v v', stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = fact_w (sel (fst v) "n") /\ snd v' = snd v.
  intros.
  eapply strengthen_runsto with (env_ax := (from_bedrock_label_map (Labels stn), change_fs fs0 stn)) in H1.
  eapply body_runsto'; eauto.
  eapply change_fs_good; eauto.
  eapply change_fs_strengthen; eauto.
Qed.

Lemma body_safe : forall stn fs v, stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
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