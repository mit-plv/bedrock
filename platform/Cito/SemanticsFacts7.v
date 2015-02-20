Set Implicit Arguments.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Semantics.
  Require Import SemanticsUtil.
  Require Import List.

  Notation make_triples := (@make_triples ADTValue).

  Require Import GeneralTactics4.

  Lemma split_triples : forall triples words_cinput coutput, words_cinput = List.map (fun x => (Word x, ADTIn x)) triples -> coutput = List.map (@ADTOut _) triples -> triples = make_triples words_cinput coutput.
  Proof.
    induction triples; destruct words_cinput; destruct coutput; simpl in *; intros; try discriminate.
    eauto.
    destruct a; inject H; inject H0.
    f_equal; eauto.
  Qed.

  Lemma split_triples' : forall triples words cinput coutput, words = List.map (@Word _) triples -> cinput = List.map (@ADTIn _) triples -> coutput = List.map (@ADTOut _) triples -> triples = make_triples (combine words cinput) coutput.
  Proof.
    induction triples; destruct words; destruct cinput; destruct coutput; simpl in *; intros; try discriminate.
    eauto.
    destruct a; inject H; inject H0; inject H1.
    f_equal; eauto.
  Qed.

  Lemma nth_error_make_triples_intro words_cinput : forall coutput i p a a', nth_error words_cinput i = Some (p, a) -> nth_error coutput i = Some a' -> nth_error (make_triples words_cinput coutput) i = Some {| Word := p; ADTIn := a; ADTOut := a'|}.
  Proof.
    induction words_cinput; destruct coutput; destruct i; simpl in *; intros; try discriminate.
    destruct a; inject H; inject H0; eauto.
    eauto.
  Qed.

  Lemma nth_error_make_triples_elim wis : forall os i p a a', nth_error (make_triples wis os) i = Some {| Word := p; ADTIn := a; ADTOut := a' |} -> nth_error wis i = Some (p, a) /\ nth_error os i = Some a'.
  Proof.
    induction wis; destruct os; destruct i; simpl in *; intros; try discriminate.
    destruct a; inject H; eauto.
    eauto.
  Qed.

  Arguments store_out {_} _ _.
  Arguments ADTOut {_} _.

  Lemma make_triples_Word_ADTIn : forall pairs outs, length outs = length pairs -> List.map (fun x => (Word x, ADTIn x)) (make_triples pairs outs) = pairs.
    induction pairs; destruct outs; simpl; intuition.
    f_equal; auto.
  Qed.

  Lemma make_triples_ADTOut : forall pairs outs, length outs = length pairs -> List.map ADTOut (make_triples pairs outs) = outs.
    induction pairs; destruct outs; simpl; intuition.
    f_equal; auto.
  Qed.

  Require Import SemanticsFacts6.
  Require Import ListFacts4.

  Lemma make_triples_ADTIn_ADTOut : forall pairs outs, length outs = length pairs -> List.map (fun x => (ADTIn x, ADTOut x)) (@make_triples pairs outs) = List.combine (List.map snd pairs) outs.
  Proof.
    intros.
    erewrite <- combine_map.
    rewrite make_triples_ADTIn by eauto.
    rewrite make_triples_ADTOut by eauto.
    eauto.
  Qed.

End ADTValue.
