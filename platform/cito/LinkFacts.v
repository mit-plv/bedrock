Set Implicit Arguments.

Require Import ADT.
Require Import RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import AutoSep.
  Require Import StructuredModule.
  Require Import StructuredModuleFacts.
  Require Import GoodModule.
  Require Import GoodFunction.
  Require Import ConvertLabel.
  Require Import NameDecoration.
  Require Import Wrap.
  Require Import GeneralTactics.
  Require Import GeneralTactics2.
  Require Import StringFacts.

  Require Import Link.
  Module Import LinkMake := Make E M.
  Require Import Stubs.
  Import StubsMake.
  Require Import Stub.
  Import StubMake.
  Require Import CompileFuncSpec.
  Import CompileFuncSpecMake.
  Require Import Inv.
  Import InvMake.
  Require Import Semantics.
  Import SemanticsMake.
  Import InvMake2.
  Require Import GoodOptimizer.
  Module Import GoodOptimizerMake := Make E.

  Require Import FMapFacts1.
  Require Import FMapFacts3.

  Require Import ConvertLabelMap.
  Import Notations.
  Open Scope clm_scope.

  Require LabelMap.
  Module BLM := LabelMap.LabelMap.
  Module BLK := LabelMap.LabelKey.
  Require Import Equalities.
  Module BLK_as_UDT := Make_UDT BLK.
  Module Import BLMFU3 := FMapFacts3.UWFacts_fun BLK_as_UDT BLM.
  Module Import BLMFU := UWFacts.
  Module Import BLMF := WFacts.

  Require Import Label.
  Module LM := LabelMap.
  Module Label_as_UDT := Key'.
  Module Import LMFU3 := FMapFacts3.UWFacts_fun Label_as_UDT LM.
  Module Import LMFU := UWFacts.
  Module Import LMF := WFacts.
  Require Import ListFacts2.
  Module LF := ListFacts2.
  Module Import LFL := Make Label_as_UDT.

  Require Import ListFacts3.

  Module Import SS := StringSet.StringSet.
  Module Import SSF := StringSet.StringFacts.
  Module SSK := StringSet.StringKey.
  Require Import FSetFacts1.
  Module SSK_as_UDT := Make_UDT SSK.
  Module Import SSUF := UWFacts_fun SSK_as_UDT SS.

  Import LM.
  Import P.
  Import F.

  Section TopSection.

    (* modules to be linked *)
    Variable modules : list GoodModule.

    Hypothesis ModulesNotEmpty : modules <> nil.

    Hypothesis NoDupModuleNames : List.NoDup (module_names modules).

    (* imported specs *)
    Variable imports : t ForeignFuncSpec.

    Hypothesis NoSelfImport : LF.Disjoint (module_names modules) (imported_module_names imports).

    Hypotheses ImportsGoodModuleName : forall l, In l imports -> IsGoodModuleName (fst l).

    (* optimizer *)

    Variable optimizer : Optimizer.

    Hypothesis IsGoodOptimizer : GoodOptimizer optimizer.

    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap.
    Notation to_set := SSUF.of_list.

    Hint Extern 1 => reflexivity.

    Require Import Setoid.
    Existing Instance to_blm_Equal_m_Proper.
    Existing Instance CompatReflSym_Symmetric.
    Existing Instance CompatReflSym_Reflexive.
    Existing Instance Compat_m_Proper.
    Existing Instance Disjoint_m_Symmetric.
    Existing Instance BLMFU3.Compat_m_Proper.

    Notation fs' := (fs modules imports).

    Lemma fs_Some : 
      forall stn p spec, 
        fs' stn p = Some spec <-> 
        exists lbl : label,
          Labels stn lbl = Some p /\
          ((exists ispec m f,
              spec = Internal ispec /\
              List.In m modules /\
              List.In f (Functions m) /\
              ispec = f /\ 
              lbl = (MName m, FName f)) \/
           (exists fspec,
              spec = Foreign fspec /\
              find lbl imports = Some fspec)).
    Proof.
      split; intros.
      destruct spec0.
      eapply fs_foreign in H.
      openhyp.
      descend.
      eauto.
      right.
      descend.
      eauto.
      eauto.
      eapply fs_internal in H.
      openhyp.
      descend.
      eauto.
      Definition get_module_exports_map m := of_list (get_module_exports m).

      Lemma exports_alt : exports modules == update_all (List.map get_module_exports_map modules).
        unfold exports.
        unfold get_module_exports_map.
        rewrite app_all_update_all.
        rewrite map_map.
        eauto.
        eapply NoDupKey_app_all; eauto.
      Qed.
      rewrite exports_alt in H.
      eapply find_2 in H.
      eapply update_all_elim in H.
      openhyp.
      eapply in_map_iff in H; openhyp; subst.
      unfold get_module_exports_map in *.
      eapply of_list_1 with (l := get_module_exports _) in H1.
      eapply InA_eqke_In in H1.
      unfold get_module_exports in H1.
      eapply in_map_iff in H1; openhyp; subst.
      injection H; intros; subst.
      left.
      descend; eauto.
      eapply NoDupKey_NoDup_fst.
      unfold get_module_exports.
      rewrite map_map.
      simpl.
      eapply GoodModule_NoDup_labels.

      openhyp.
      subst.
      unfold fs.
      destruct (option_dec (is_export modules stn p)).
      destruct s.
      rewrite e.
      unfold is_export in *.
      unfold find_by_word in *.
      destruct (option_dec (List.find (is_label_map_to_word' stn p)
          (LabelMap.elements (exports modules)))) in *.
      destruct s.
      rewrite e0 in e.
      eapply find_spec in e0.
      openhyp.
      destruct x0; simpl in *.
      injection e; intros; subst.
      unfold is_label_map_to_word' in H0.
      simpl in *.
      unfold is_label_map_to_word in H0.
      destruct (option_dec (labels stn l)).
      destruct s.
      rewrite e0 in H0.
      destruct (weq p x0).
      subst.
      unfold labels in *.
      (*here*)
    Qed.

        

