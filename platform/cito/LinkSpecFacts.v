Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import LinkSpec.
  Module Import LinkSpecMake := Make E.
  Require Import ProgramLogic2.
  Module Import ProgramLogicMake := Make E.

  Section TopSection.

    Notation FName := SyntaxFunc.Name.
    Notation MName := GoodModule.Name.

    Definition imports_exports_mapsto lbl spec modules imports :=
      (exists ispec m f,
         spec = Internal ispec /\
         List.In m modules /\
         List.In f (Functions m) /\
         ispec = f /\ 
         lbl = (MName m, FName f)) \/
      (exists fspec,
         spec = Foreign fspec /\
         find lbl imports = Some fspec).

    Definition imports_exports_in lbl modules (imports : t ForeignFuncSpec) :=
      (exists m f,
         List.In m modules /\
         List.In f (Functions m) /\
         lbl = (MName m, FName f)) \/
      In lbl imports.

    Require Import GeneralTactics.

    Lemma imports_exports_mapsto_in : forall modules imports lbl spec, imports_exports_mapsto lbl spec modules imports -> imports_exports_in lbl modules imports.
      unfold imports_exports_mapsto, imports_exports_in.
      intros.
      openhyp.
      left; descend; eauto.
      right; eapply MapsTo_In; eapply find_mapsto_iff; eauto.
    Qed.

    Definition specs_equal specs modules imports := forall lbl spec, find lbl specs = Some spec <-> imports_exports_mapsto lbl spec modules imports.

    Lemma specs_equal_agree : forall specs modules imports, specs_equal specs modules imports -> forall stn fs, stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> specs_env_agree specs (from_bedrock_label_map (Labels stn), fs stn).
      intros.
      split.

      unfold labels_in_scope.
      intros.
      unfold from_bedrock_label_map in *; simpl in *.
      eapply In_MapsTo in H2.
      openhyp.
      eapply H0.
      eapply imports_exports_mapsto_in.
      eapply H.
      eapply find_mapsto_iff; eauto.

      unfold specs_fs_agree.
      unfold from_bedrock_label_map in *; simpl in *.
      split; intros.

      eapply H1 in H2.
      destruct H2.
      destruct H2.
      descend.
      eauto.
      eapply H; eauto.

      openhyp.
      eapply H1.
      eexists.
      split.
      eauto.
      eapply H; eauto.
    Qed.

  End TopSection.

End Make.
