Set Implicit Arguments.

Require Import ADT.
Require Import RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Link.
  Module Import LinkMake := Make E M.
  Require Import Semantics.
  Module Import SemanticsMake := Make E.
  Require Import GoodOptimizer.
  Module Import GoodOptimizerMake := Make E.

  Section TopSection.

    Require Import GoodModule.
    Require Import GLabelMap.
    Import GLabelMap.
    
    Definition GoodToLink_bool (modules : list GoodModule) (imports : t ForeignFuncSpec) := true.

    Require Import GeneralTactics.

    Lemma GoodToLink_bool_sound : 
      forall modules imports,
        GoodToLink_bool modules imports = true ->
        modules <> nil /\
        List.NoDup (List.map Name modules) /\
        ListFacts1.Disjoint (List.map Name modules) (List.map (fun x => fst (fst x)) (elements imports)) /\
        forall l, In l imports -> IsGoodModuleName (fst l).
      admit.
    Qed.

    Lemma result_ok_2 :
      forall modules imports,
        GoodToLink_bool modules imports = true ->
        forall opt (opt_g: GoodOptimizer opt),
          moduleOk (result modules imports opt_g).
    Proof.
      intros.
      eapply GoodToLink_bool_sound in H.
      openhyp.
      eapply result_ok; eauto.
    Qed.

  End TopSection.

End Make.