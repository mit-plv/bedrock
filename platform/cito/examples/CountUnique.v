Set Implicit Arguments.

Require Import MakeWrapper ExampleADT ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.

Require Import Notations4.
Module Import Notations4Make := Make ExampleADT.

Require Import Arith.
Import ProgramLogicMake.
Open Scope nat.

Require Import ExampleImpl.

Require Import FiniteSet.
Require Import WordMap.
Import WordMap.

Infix "==" := Equal.
Infix "=s=" := WordSet.Equal (at level 60).

Definition singleton_map elt k v := @add elt k v (empty _).

Infix "-->" := (@singleton_map _) (at level 40).

Require Import WordMapFacts.

Definition AllDisjoint elt := ForallOrdPairs (@Disjoint elt).

Definition equal_disj_update_all elt h' hs := (h' == @update_all elt hs) /\ AllDisjoint hs.

Notation "h === x ** .. ** y" := (equal_disj_update_all h (cons x .. (cons y nil) ..)) (at level 60).

Require MSetProperties.
Module WordSetFacts := MSetProperties.Properties WordSet.

Notation to_set := WordSetFacts.of_list.

Definition wnat (w : W) := wordToNat w.
Coercion wnat : W >-> nat.

Notation " [[ ]] " := nil.
Notation " [[ x , .. , y ]] " := (cons x .. (cons y nil) ..).

Definition count_body := (
    "set" <-- DCall "ADT"!"ListSet_new"();;
    "i" <- 0;;
    [BEFORE (V, h) AFTER (V', h') exists arr fset,
       (h' === h ** (V "arr" --> Arr arr) ** (V "set" --> FSet fset)) /\ 
       V "len" = length arr /\
       fset =s= to_set (firstn (V "i") arr)
    ]
    While ("i" < "len") {
      "e" <-- DCall "ADT"!"ArraySeq_read" ("arr", "i");;
      DCall "ADT"!"ListSet_add"("set", "e");;
      "i" <- "i" + 1
    };;
    "ret" <-- DCall "ADT"!"ListSet_size"("set");;
    DCall "ADT"!"ListSet_delete"("set")
)%stmtex.

Definition main_body := (
    "arr" <-- DCall "ADT"!"ArraySeq_new"(3);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ length arr = 3 ];;
    DCall "ADT"!"ArraySeq_write"("arr", 0, 10);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ length arr = 3 /\ Array.sel arr 0 = 10 ];;
    DCall "ADT"!"ArraySeq_write"("arr", 1, 20);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ exists w, arr = [[$10, $20, w]] ];;
    DCall "ADT"!"ArraySeq_write"("arr", 2, 10);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ arr = [[$10, $20, $10]] ];;
    "ret" <-- DCall "count"!"count" ("arr", 3);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ V' "ret" = 2 ];;
    DCall "ADT"!"ArraySeq_delete"("arr");;
    Assert [ BEFORE(V, h) AFTER(V', h') 
      h' == h /\ V' "ret" = 2 ]
)%stmtex.

Definition m := cmodule "count" {{
  cfunction "count"("arr", "len")
    count_body
  end with
  cfunction "main"()
    main_body
  end
}}.

Lemma good : IsGoodModule m.
  good_module.
Qed.

Definition gm := to_good_module good.

Import LinkSpecMake2.

Notation "name @ [ p ]" := (name%stmtex, p) (only parsing).

Definition modules := [[ gm ]].

Require Import GLabelMapFacts.

Definition imports := 
  of_list 
    [[ 
        "ADT"!"ArraySeq_new" @ [ArraySeq_newSpec],
        "ADT"!"ArraySeq_write" @ [ArraySeq_writeSpec],
        "ADT"!"ArraySeq_read" @ [ArraySeq_readSpec],
        "ADT"!"ArraySeq_delete" @ [ArraySeq_deleteSpec],
        "ADT"!"ListSet_new" @ [ListSet_newSpec],
        "ADT"!"ListSet_add" @ [ListSet_addSpec],
        "ADT"!"ListSet_size" @ [ListSet_sizeSpec],
        "ADT"!"ListSet_delete" @ [ListSet_deleteSpec]
    ]].

Definition dummy_gf : GoodFunction.
  refine (to_good_function (cfunction "dummy"() "ret" <- 0 end)%Citofuncs _).
  good_module.
Defined.    

Definition count := nth 0 (Functions gm) dummy_gf.
Definition main := nth 1 (Functions gm) dummy_gf.

Definition main_spec_Bedrock := func_spec modules imports ("count"!"main")%stmtex main.

Notation extra_stack := 40.

Definition topS := SPEC reserving (4 + extra_stack)
  PREonly[_] mallocHeap 0.

Definition top := bimport [[ ("count"!"main", main_spec_Bedrock), "sys"!"printInt" @ [printIntS],
                             "sys"!"abort" @ [abortS] ]]
  bmodule "top" {{
    bfunction "top"("R") [topS]
      "R" <-- Call "count"!"main"(extra_stack)
      [PREonly[_, R] [| R = 2 |] ];;

      Call "sys"!"printInt"("R")
      [PREonly[_] Emp ];;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Import Semantics.
Import SemanticsMake.

Import WordSet.

Definition unique_count ls := cardinal (fold_right add empty ls).

Definition count_spec : ForeignFuncSpec :=
  {|
    PreCond := fun args => exists arr len, args = inr (Arr arr) :: inl len :: nil /\ len = length arr;
    PostCond := fun args ret => exists arr len, args = (inr (Arr arr), Some (Arr arr)) :: (inl len, None) :: nil /\ ret = inl (unique_count arr : W)
  |}.

Definition main_spec : ForeignFuncSpec :=
  {|
    PreCond := fun args => args = nil;
    PostCond := fun _ ret => ret = inl $2
  |}.

Require Import GLabelMap.
Import GLabelMap.GLabelMap.

Definition make_specs modules imports := fold_right (fun m acc => fold_right (fun (f : GoodFunction) acc => add (GName m, FName f) (Internal f) acc) acc (Functions m)) (map Foreign imports) modules.

(* Definition specs := add ("count", "count") (Foreign count_spec) (make_specs modules imports). *)

Definition specs_change_table : t (InternalFuncSpec * ForeignFuncSpec) :=
  of_list
    [[
        "count"!"count" @ [(count : InternalFuncSpec, count_spec)],
        "count"!"main" @ [(main : InternalFuncSpec, main_spec)]
    ]]%stmtex.

Definition is_pointer_of_label elt new_specs (stn : glabel -> option W) w : option elt :=
  fold (fun k v res => 
          match res with
            | Some _ => res
            | None => 
              match stn k with
                | Some w' => if weq w w' then Some v else None
                | None => None
              end
          end
       ) new_specs None.

Definition change_env new_specs (env : Env) : Env :=
  let stn := fst env in
  let fs := snd env in
  (stn,
   fun w =>
     match is_pointer_of_label new_specs stn w with
       | Some new_spec => Some new_spec
       | None => fs w
     end).

Require Import SemanticsFacts4.
Module Import SemanticsFacts4Make := Make ExampleADT.
Import TransitMake.

Definition strengthen_op_ax env_ax (spec_op : InternalFuncSpec) spec_ax :=
  let args := ArgVars spec_op in
  let rvar := RetVar spec_op in
  let s := Body spec_op in
  (forall ins, 
     PreCond spec_ax ins ->
     length args = length ins) /\
  (forall v,
     TransitSafe spec_ax (List.map (sel (fst v)) args) (snd v) ->
     Safe env_ax s v) /\
  forall v v', 
    RunsTo env_ax s v v' -> 
    TransitTo spec_ax (List.map (sel (fst v)) args) (snd v) (sel (fst v') rvar) (snd v').

Definition sub_domain elt1 elt2 (m1 : t elt1) (m2 : t elt2) := forall k, In k m1 -> In k m2.
Definition equal_domain elt1 elt2 (m1 : t elt1) (m2 : t elt2) := sub_domain m1 m2 /\ sub_domain m2 m1.

Lemma change_env_agree : forall specs new_specs, equal_domain new_specs specs -> forall env, specs_env_agree specs env -> specs_env_agree new_specs (change_env new_specs env).
  admit.
Qed.

Definition apply_specs_diff specs specs_diff := update specs (map (fun v : InternalFuncSpec * _ => Foreign (snd v)) specs_diff).

Definition strengthen_specs env_ax specs_diff :=
  fold (fun k v a =>
          strengthen_op_ax env_ax (fst v) (snd v) /\ a
       ) specs_diff True.

Lemma change_env_strength : forall specs specs_diff, sub_domain specs_diff specs -> forall env_op env_ax, specs_env_agree specs env_op -> specs_env_agree (apply_specs_diff specs specs_diff) env_ax -> strengthen_specs env_ax specs_diff -> strengthen env_op env_ax.
  admit.
Qed.

(*here*)

Lemma change_fs_agree : forall fs stn, stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> specs_env_agree specs (from_bedrock_label_map (Labels stn), change_fs fs stn).
  intros.
  split.
  simpl.
  unfold labels_in_scope.
  intros.
  eapply H.
  unfold specs in *.
  eapply add_in_iff in H1.
  openhyp.
  subst; simpl in *.
  left.
  unfold gm, to_good_module in *; simpl in *.
  descend.
  eauto.
  simpl; eauto.
  simpl; eauto.
  eapply empty_in_iff in H1; intuition.

  unfold specs_fs_agree; simpl in *.
  unfold change_fs.
  intros.
  destruct (option_dec (fs0 stn p)).
  destruct s; rewrite e in *.
  destruct x; simpl in *.
  eapply H0 in e.
  openhyp.
  subst; simpl in *.
  openhyp.
  subst; simpl in *.
  openhyp.
  subst; simpl in *.
  discriminate.
  intuition.
  intuition.
  injection H2; intros; subst.
  unfold imports in H3; simpl in *.
  compute in H3; intuition.
  split; intros.
  injection H1; intros; subst.
  eapply H0 in e.
  openhyp.
  subst; simpl in *.
  openhyp.
  subst; simpl in *.
  openhyp.
  subst; simpl in *.
  injection H3; intros; subst; simpl in *; clear H3.
  descend.
  eauto.
  reflexivity.
  intuition.
  intuition.
  compute in H4; intuition.
  openhyp.
  unfold specs in H2.
  eapply find_mapsto_iff in H2.
  eapply add_mapsto_iff in H2.
  openhyp.
  subst; eauto.
  eapply empty_mapsto_iff in H3; intuition.
  rewrite e in *.
  split; intros.
  discriminate.
  openhyp.
  unfold specs in H2.
  eapply find_mapsto_iff in H2.
  eapply add_mapsto_iff in H2.
  openhyp.
  subst; simpl in *.
  contradict e.
  Lemma Some_not_None : forall A o (v : A), o = Some v -> o <> None.
    intuition.
  Qed.
  eapply Some_not_None.
  eapply H0.
  descend.
  eauto.
  left.
  unfold gm, to_good_module in *; simpl in *.
  descend.
  eauto.
  eauto.
  simpl; eauto.
  eauto.
  simpl; eauto.
  eapply empty_mapsto_iff in H3; intuition.
Qed.

Lemma change_fs_strengthen : forall fs stn, stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn ->strengthen (from_bedrock_label_map (Labels stn), fs stn) (from_bedrock_label_map (Labels stn), change_fs fs stn).
  unfold modules, imports.
  intros.
  generalize H0; intro.
  unfold strengthen.
  split.
  eauto.
  unfold change_fs at 1.
  unfold change_fs at 1.
  simpl.
  intros.
  destruct (option_dec (fs0 stn w)); simpl in *.
  destruct s; rewrite e in *; simpl in *.
  destruct x; simpl in *.
  eauto.
  eapply H0 in e.
  openhyp.
  subst; simpl in *.
  openhyp.
  subst; simpl in *.
  openhyp.
  subst; simpl in *.
  injection H3; intros; subst; simpl in *; clear H3.
  right; descend.
  eauto.
  eauto.
  simpl in *.
  openhyp.
  rewrite H3.
  eauto.
  simpl in *.
  eapply body_safe'; eauto.
  eapply change_fs_agree; eauto.
  eapply body_runsto' in H3; eauto.
  Focus 2.
  eapply change_fs_agree; eauto.
  simpl.
  openhyp.
  unfold TransitMake.TransitTo.
  descend.
  instantiate (1 := [[ {| Word := sel (fst v) "n"; ADTIn := inl (sel (fst v) "n"); ADTOut := None |} ]]).
  eauto.
  repeat econstructor.
  descend; eauto.
  descend; eauto.
  repeat econstructor.
  simpl.
  Import TransitMake.SemanticsMake.
  unfold store_out, Semantics.store_out; simpl; eauto.
  unfold f in *; simpl in *.
  eauto.
  intuition.
  intuition.
  rewrite empty_o in H4; intuition.
  rewrite e in *.
  eauto.
  Grab Existential Variables.
  eauto.
Qed.

Definition specs := update (make_specs modules imports) (map (fun e => Foreign (snd e)) specs_change_table).

Lemma body_runsto : forall stn fs v v', stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = fact_w (sel (fst v) "n") /\ snd v' = snd v.
  intros.
  eapply strengthen_runsto with (env_ax := (from_bedrock_label_map (Labels stn), change_fs fs0 stn)) in H1.
  eapply body_runsto'; eauto.
  eapply change_fs_agree; eauto.
  eapply change_fs_strengthen; eauto.
Qed.

Lemma body_safe : forall stn fs v, stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  intros.
  eapply strengthen_safe.
  eapply body_safe'; eauto.
  eapply change_fs_agree; eauto.
  eapply change_fs_strengthen; eauto.
Qed.

*)
Import LinkSpecMake.
Require Import LinkSpecFacts.
Module Import LinkSpecFactsMake := Make ExampleADT.
Import Notations4Make.

Lemma specs_good : specs_equal specs modules imports.
(*  split; intros.

  unfold imports_exports_mapsto, specs in *.
  eapply find_mapsto_iff in H.
  eapply add_mapsto_iff in H.
  openhyp.
  subst; simpl in *.
  left; descend; eauto.
  unfold spec_op, gm; simpl; eauto.

  eapply map_mapsto_iff in H0.
  openhyp.
  subst; simpl in *.
  right; descend; eauto.
  eapply find_mapsto_iff; eauto.

  unfold imports_exports_mapsto, specs in *.
  eapply find_mapsto_iff.
  eapply add_mapsto_iff.
  openhyp.
  subst; simpl in *.
  openhyp.
  2 : intuition.
  subst.
  left.
  unfold spec_op, gm, to_good_module in *; simpl in *.
  openhyp.
  2 : intuition.
  subst; simpl in *.
  eauto.

  subst; simpl in *.
  right; descend; eauto.
  Require Import GeneralTactics2.
  nintro.
  subst; simpl in *.
  compute in H0.
  intuition.
  eapply map_mapsto_iff.
  descend; eauto.
  eapply find_mapsto_iff; eauto.*)
  admit.
Qed.

Require Import WordFacts2 WordFacts5.
Require Import WordMapFacts.

Definition empty_precond : assert := fun _ v0 v => v0 = v.

Import WordMap.
Require Import GeneralTactics2.

Lemma empty_mapsto_elim : forall P elt k v, MapsTo k v (empty elt) -> P.
  intros.
  eapply empty_mapsto_iff in H; intuition.
Qed.
Hint Extern 0 => (eapply empty_mapsto_elim; eassumption).
Lemma empty_in_elim : forall P elt k, In k (empty elt) -> P.
  intros.
  eapply empty_in_iff in H; intuition.
Qed.
Hint Extern 0 => (eapply empty_in_elim; eassumption).
Lemma singleton_mapsto_iff : forall elt k v k' v', @MapsTo elt k' v' (k --> v) <-> k' = k /\ v' = v.
  split; intros.
  eapply add_mapsto_iff in H; openhyp; eauto.
  openhyp; eapply add_mapsto_iff; eauto.
Qed.
Lemma singleton_in_iff : forall elt k k' v, @In elt k' (k --> v) <-> k' = k.
  split; intros.
  eapply add_in_iff in H; openhyp; eauto.
  openhyp; eapply add_in_iff; eauto.
Qed.
Lemma update_add : forall elt k v h, @update elt h (k --> v) == add k v h.
  intros.
  unfold Equal; intros.
  eapply option_univalence.
  split; intros.

  eapply find_mapsto_iff in H.
  eapply find_mapsto_iff.
  eapply update_mapsto_iff in H.
  openhyp.
  eapply singleton_mapsto_iff in H.
  openhyp; subst.
  eapply add_mapsto_iff; eauto.
  eapply add_mapsto_iff.
  right.
  split.
  not_not.
  subst.
  eapply singleton_in_iff; eauto.
  eauto.

  eapply find_mapsto_iff in H.
  eapply find_mapsto_iff.
  eapply add_mapsto_iff in H.
  openhyp.
  subst.
  eapply update_mapsto_iff.
  left.
  eapply singleton_mapsto_iff; eauto.
  eapply update_mapsto_iff.
  right.
  split.
  eauto.
  not_not.
  eapply singleton_in_iff in H1; eauto.
Qed.
Lemma singleton_disj : forall elt k v h, ~ @In elt k h <-> Disjoint h (k --> v).
  unfold Disjoint; split; intros.
  not_not; openhyp.
  eapply singleton_in_iff in H0; subst; eauto.
  nintro.
  specialize (H k).
  contradict H.
  split.
  eauto.
  eapply singleton_in_iff; eauto.
Qed.
Lemma separated_star : forall h k v, separated h k (Some v) -> add k v h === h ** k --> v.
  intros.
  unfold separated, Semantics.separated in *.
  openhyp.
  intuition.
  split.
  unfold update_all.
  simpl.
  rewrite update_add.
  rewrite update_empty_1.
  reflexivity.
  repeat econstructor.
  eapply singleton_disj; eauto.
Qed.

Require Import BedrockTactics.
Lemma map_fst_combine : forall A B (a : list A) (b : list B), length a = length b -> a = List.map fst (List.combine a b).
  induction a; destruct b; simpl; intuition.
  f_equal; eauto.
Qed.

Ltac eapply_in_any t :=
  match goal with
      H : _ |- _ => eapply t in H
  end.

Lemma map_add_same_key : forall elt m k v1 v2, @add elt k v2 (add k v1 m) == add k v2 m.
  unfold WordMap.Equal; intros.
  repeat rewrite add_o.
  destruct (UWFacts.WFacts.P.F.eq_dec k y); intuition.
Qed.

Lemma add_remove : forall elt m k v, ~ @In elt k m -> WordMap.remove k (add k v m) == m.
  unfold WordMap.Equal; intros.
  rewrite remove_o.
  rewrite add_o.
  destruct (UWFacts.WFacts.P.F.eq_dec k y); intuition.
  subst.
  symmetry; eapply not_find_in_iff; eauto.
Qed.

Fixpoint same_keys_ls elt (hs1 hs2 : list (t elt)) :=
  match hs1, hs2 with
    | h1 :: hs1', h2 :: hs2' => keys h1 = keys h2 /\ same_keys_ls hs1' hs2'
    | nil, nil => True
    | _ , _ => False
  end.

Lemma same_keys_all_disj : forall elt hs1 hs2, @AllDisjoint elt hs1 -> same_keys_ls hs1 hs2 -> AllDisjoint hs2.
  unfold AllDisjoint; induction hs1; destruct hs2; simpl; intuition.
  Require Import GeneralTactics3.
  inv_clear H.
  econstructor; eauto.
  Lemma same_keys_forall_disj : forall elt hs1 hs2 h1 h2, List.Forall (@Disjoint elt h1) hs1 -> same_keys_ls hs1 hs2 -> keys h1 = keys h2 -> List.Forall (Disjoint h2) hs2.
    induction hs1; destruct hs2; simpl; intuition.
    inv_clear H.
    econstructor; eauto.
    Lemma same_keys_disj : forall elt (a b a' b' : t elt), Disjoint a b -> keys a = keys a' -> keys b = keys b' -> Disjoint a' b'.
      unfold Disjoint; intros.
      Lemma same_keys_in_iff : forall elt (m1 m2 : t elt), keys m1 = keys m2 -> forall k, In k m1 <-> In k m2.
        split; intros.
        eapply In_In_keys; rewrite <- H; eapply In_In_keys; eauto.
        eapply In_In_keys; rewrite H; eapply In_In_keys; eauto.
      Qed.
      specialize (same_keys_in_iff _ _ H0); intros.
      specialize (same_keys_in_iff _ _ H1); intros.
      intuition.
      eapply H; split.
      eapply H2; eauto.
      eapply H3; eauto.
    Qed.
    eapply same_keys_disj; eauto.
  Qed.
  eapply same_keys_forall_disj; eauto.
Qed.

Lemma add_o_eq : forall elt k v v' m, @find elt k (add k v m) = Some v' -> v = v'.
  intros.
  rewrite add_o in H.
  destruct (eq_dec _ _); [ | intuition].
  injection H; intros; subst; eauto.
Qed.

Import ProgramLogicMake.SemanticsMake.

Ltac destruct_state :=
  repeat match goal with
           | [ x : State |- _ ] => destruct x; simpl in *
         end.

Ltac split_all :=
  repeat match goal with
           | |- _ /\ _ => split
         end.

Lemma main_vcs_good : and_all (vc main_body empty_precond) specs.
  unfold empty_precond, main_body; simpl; unfold imply_close, and_lift; simpl; split_all.

  (* vc1 *)
  intros.
  subst.
  unfold SafeDCall.
  simpl.
  intros.
  Import TransitMake.
  unfold TransitSafe.
  descend.
  instantiate (1 := [[ ($3, _) ]]).
  eauto.
  repeat econstructor.
  instantiate (1 := inl $3).
  repeat econstructor.
  repeat econstructor.
  descend; eauto.

  (* vc2 *)
  intros.
  destruct_state.
  openhyp.
  subst.
  unfold RunsToDCall in *.
  simpl in *.
  openhyp.
  unfold TransitTo in *.
  openhyp.
  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  eapply triples_intro in H3; try eassumption.
  subst; simpl in *.
  Import SemanticsMake.
  unfold good_inputs, Semantics.good_inputs in *.
  openhyp.
  unfold Semantics.word_adt_match in *.
  inversion_Forall; simpl in *.
  subst.
  unfold store_out, Semantics.store_out in *; simpl in *.
  descend; eauto.
  eapply separated_star; eauto.

  (* vc3 *)
  intros.
  unfold SafeDCall.
  simpl.
  intros.
  destruct_state.
  openhyp.
  destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in *; rewrite update_add in *.
  unfold TransitSafe.
  descend.
  sel_upd_simpl.
  eapply map_fst_combine.
  instantiate (1 := [[ _, _, _ ]]); eauto.
  split.
  unfold Semantics.word_adt_match.
  repeat econstructor; simpl.
  eauto.
  instantiate (1 := inr (Arr x)); simpl in *.
  rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
  instantiate (1 := inl $0); simpl in *.
  eauto.
  instantiate (1 := inl $10); simpl in *.
  eauto.
  simpl.
  unfold Semantics.disjoint_ptrs.
  NoDup.
  descend; eauto.
  rewrite H0.
  eauto.

  (* vc4 *)
  intros.
  openhyp.
  destruct_state.
  destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
  unfold RunsToDCall in *.
  simpl in *.
  openhyp.
  unfold TransitTo in *.
  openhyp.
  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  eapply_in_any triples_intro; try eassumption.
  subst; simpl in *.
  unfold store_out, Semantics.store_out in *; simpl in *.
  unfold good_inputs, Semantics.good_inputs in *.
  openhyp.
  unfold Semantics.word_adt_match in *.
  inversion_Forall; simpl in *.
  subst; simpl in *.
  sel_upd_simpl.
  rewrite H in H9.
  eapply_in_any add_o_eq; subst.
  injection H9; intros; subst.
  descend.
  split.
  rewrite H; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
  eapply map_add_same_key.
  eapply same_keys_all_disj; eauto.
  simpl; eauto.
  rewrite upd_length; eauto.
  eapply CompileExpr.sel_upd_eq; eauto.
  rewrite H1; eauto.

  (* vc5 *)
  intros.
  unfold SafeDCall.
  simpl.
  intros.
  destruct_state.
  openhyp.
  destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
  unfold TransitSafe.
  sel_upd_simpl.
  descend.
  eapply map_fst_combine.
  instantiate (1 := [[ _, _, _ ]]); eauto.
  split.
  unfold Semantics.word_adt_match.
  repeat econstructor; simpl.
  instantiate (1 := inr (Arr x)); simpl in *.
  rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
  instantiate (1 := inl $1); simpl in *.
  eauto.
  instantiate (1 := inl $20); simpl in *.
  eauto.
  simpl.
  unfold Semantics.disjoint_ptrs.
  NoDup.
  descend; eauto.
  rewrite H0; eauto.

  (* vc6 *)
  intros.
  openhyp.
  destruct_state.
  destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
  unfold RunsToDCall in *.
  simpl in *.
  openhyp.
  unfold TransitTo in *.
  openhyp.
  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  eapply_in_any triples_intro; try eassumption.
  subst; simpl in *.
  unfold store_out, Semantics.store_out in *; simpl in *.
  unfold good_inputs, Semantics.good_inputs in *.
  openhyp.
  unfold Semantics.word_adt_match in *.
  inversion_Forall; simpl in *.
  subst; simpl in *.
  sel_upd_simpl.
  rewrite H in H10; eapply_in_any add_o_eq; subst; injection H10; intros; subst.
  destruct x5; simpl in *; try discriminate.
  destruct x5; simpl in *; try discriminate.
  destruct x5; simpl in *; try discriminate.
  descend.
  split.
  rewrite H; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
  eapply map_add_same_key.
  eapply same_keys_all_disj; eauto.
  simpl; eauto.
  Transparent natToWord.
  unfold Array.upd; simpl.
  unfold Array.sel in H2; simpl in H2; subst.
  repeat f_equal.
  destruct x5; simpl in *; try discriminate.
  eauto.
  Opaque natToWord.

  (* vc7 *)
  intros.
  unfold SafeDCall.
  simpl.
  intros.
  destruct_state.
  openhyp.
  destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
  unfold TransitSafe.
  sel_upd_simpl.
  descend.
  eapply map_fst_combine.
  instantiate (1 := [[ _, _, _ ]]); eauto.
  split.
  unfold Semantics.word_adt_match.
  repeat econstructor; simpl.
  instantiate (1 := inr (Arr x)); simpl in *.
  rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
  instantiate (1 := inl $2); simpl in *.
  eauto.
  instantiate (1 := inl $10); simpl in *.
  eauto.
  simpl.
  unfold Semantics.disjoint_ptrs.
  NoDup.
  descend; eauto.
  rewrite H0; eauto.

  (* vc8 *)
  intros.
  openhyp.
  destruct_state.
  destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
  unfold RunsToDCall in *.
  simpl in *.
  openhyp.
  unfold TransitTo in *.
  openhyp.
  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  eapply_in_any triples_intro; try eassumption.
  subst; simpl in *.
  unfold store_out, Semantics.store_out in *; simpl in *.
  unfold good_inputs, Semantics.good_inputs in *.
  openhyp.
  unfold Semantics.word_adt_match in *.
  inversion_Forall; simpl in *.
  subst; simpl in *.
  sel_upd_simpl.
  rewrite H in H8; eapply_in_any add_o_eq; subst; injection H8; intros; subst.
  descend.
  split.
  rewrite H; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
  eapply map_add_same_key.
  eapply same_keys_all_disj; eauto.
  simpl; eauto.
  Transparent natToWord.
  reflexivity.
  Opaque natToWord.

  (* vc9 *)
  intros.
  unfold SafeDCall.
  simpl.
  intros.
  destruct_state.
  openhyp.
  destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
  unfold TransitSafe.
  sel_upd_simpl.
  descend.
  eapply map_fst_combine.
  instantiate (1 := [[ _, _ ]]); eauto.
  split.
  unfold Semantics.word_adt_match.
  repeat econstructor; simpl.
  instantiate (1 := inr (Arr x)); simpl in *.
  rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
  instantiate (1 := inl $3); simpl in *.
  eauto.
  simpl.
  unfold Semantics.disjoint_ptrs.
  NoDup.
  descend.
  eauto.
  rewrite H0; eauto.

  (* vc10 *)
  intros.
  openhyp.
  destruct_state.
  destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
  unfold RunsToDCall in *.
  simpl in *.
  openhyp.
  unfold TransitTo in *.
  openhyp.
  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  eapply_in_any triples_intro; try eassumption.
  subst; simpl in *.
  unfold store_out, Semantics.store_out in *; simpl in *.
  unfold good_inputs, Semantics.good_inputs in *.
  openhyp.
  unfold Semantics.word_adt_match in *.
  inversion_Forall; simpl in *.
  subst; simpl in *.
  sel_upd_simpl.
  rewrite H in H8; eapply_in_any add_o_eq; subst; injection H8; intros; subst.
  descend.
  split.
  rewrite H; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
  eapply map_add_same_key.
  eapply same_keys_all_disj; eauto.
  simpl; eauto.
  reflexivity.

  (* vc11 *)
  intros.
  unfold SafeDCall.
  simpl.
  intros.
  destruct_state.
  openhyp.
  destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
  unfold TransitSafe.
  sel_upd_simpl.
  descend.
  eapply map_fst_combine.
  instantiate (1 := [[ _ ]]); eauto.
  split.
  unfold Semantics.word_adt_match.
  repeat econstructor; simpl.
  instantiate (1 := inr (Arr x)); simpl in *.
  rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
  simpl.
  unfold Semantics.disjoint_ptrs.
  NoDup.
  descend.
  eauto.

  (* vc12 *)
  intros.
  openhyp.
  destruct_state.
  destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
  unfold RunsToDCall in *.
  simpl in *.
  openhyp.
  unfold TransitTo in *.
  openhyp.
  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  eapply_in_any triples_intro; try eassumption.
  subst; simpl in *.
  unfold store_out, Semantics.store_out in *; simpl in *.
  unfold good_inputs, Semantics.good_inputs in *.
  openhyp.
  unfold Semantics.word_adt_match in *.
  inversion_Forall; simpl in *.
  subst; simpl in *.
  sel_upd_simpl.
  rewrite H in H9; eapply_in_any add_o_eq; subst; injection H9; intros; subst.
  descend.
  rewrite H.
  eapply add_remove.
  eapply singleton_disj.
  inv_clear H2.
  inversion_Forall.
  eauto.

  eauto.
Qed.

Local Hint Immediate main_vcs_good.

Hint Resolve specs_good.

Lemma main_runsto : forall stn fs v v', stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body main) v v' -> sel (fst v') (RetVar f) = 2 /\ snd v' == snd v.
  cito_runsto main empty_precond main_vcs_good; eauto.
  eapply specs_equal_agree; eauto.
Qed.

Lemma main_safe : forall stn fs v, stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body main) v.
  cito_safe main empty_precond main_vcs_good; eauto.
  eapply specs_equal_agree; eauto.
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
  call_cito 40 (@nil string).
  hiding ltac:(evaluate auto_ext).
  unfold name_marker.
  hiding ltac:(step auto_ext).
  unfold spec_without_funcs_ok.
  post.
  descend.
  eapply CompileExprs.change_hyp.
  Focus 2.
  apply (@is_state_in''' (upd x2 "extra_stack" 40)).
  autorewrite with sepFormula.
  clear H7 H8.
  hiding ltac:(step auto_ext).
  apply main_safe; eauto.
  hiding ltac:(step auto_ext).
  repeat ((apply existsL; intro) || (apply injL; intro) || apply andL); reduce.
  apply swap; apply injL; intro.
  openhyp.
  Import LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.
  match goal with
    | [ x : State |- _ ] => destruct x; simpl in *
  end.
  apply main_runsto in H9; simpl in H9; intuition subst.
  eapply replace_imp.
  change 40 with (wordToNat (sel (upd x2 "extra_stack" 40) "extra_stack")).
  apply is_state_out'''''.
  NoDup.
  NoDup.
  NoDup.
  eauto.
  
  hiding ltac:(step auto_ext).
  hiding ltac:(step auto_ext).

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
Qed.

Definition all := link top (link_with_adts modules imports).

Theorem all_ok : moduleOk all.
  Import Wrp.LinkMake.
  Import Wrp.LinkMake.LinkModuleImplsMake.

  Ltac link0 ok1 :=
    eapply linkOk; [ eapply ok1 | impl_ok
                     | reflexivity
                     | (* simpl; unfold CompileModuleMake.mod_name; unfold impl_module_name; *)
                       (* simpl; unfold StubsMake.StubMake.bimports_diff_bexports; *)
                       (* simpl; unfold StubsMake.StubMake.LinkSpecMake2.func_impl_export; *)
                       (* simpl; unfold StubsMake.StubMake.LinkSpecMake2.impl_label; *)
                       (* unfold impl_module_name; simpl; unfold CompileModuleMake.imports; simpl; *)
                       (* link_simp; eauto *) ..
                   ].

  link0 top_ok.

  simpl; unfold CompileModuleMake.mod_name; unfold impl_module_name;
  simpl; unfold StubsMake.StubMake.bimports_diff_bexports;
  simpl; unfold StubsMake.StubMake.LinkSpecMake2.func_impl_export;
  simpl; unfold StubsMake.StubMake.LinkSpecMake2.impl_label;
  unfold impl_module_name; simpl; unfold CompileModuleMake.imports; simpl;
  link_simp.

  eauto.

  simpl; unfold CompileModuleMake.mod_name; unfold impl_module_name;
  simpl; unfold StubsMake.StubMake.bimports_diff_bexports;
  simpl; unfold StubsMake.StubMake.LinkSpecMake2.func_impl_export;
  simpl; unfold StubsMake.StubMake.LinkSpecMake2.impl_label;
  unfold impl_module_name; simpl; unfold CompileModuleMake.imports; simpl;
  link_simp.

  eauto.

  unfold modules, gm, to_good_module, imports, link_with_adts.
  unfold to_good_functions', to_good_functions.
  unfold CompileModuleMake.mod_name; unfold impl_module_name.
  unfold StubsMake.StubMake.bimports_diff_bexports.
  unfold StubsMake.StubMake.LinkSpecMake2.func_impl_export.
  unfold StubsMake.StubMake.LinkSpecMake2.impl_label.
  unfold impl_module_name; unfold CompileModuleMake.imports.
  simpl.
  link_simp.
(* stuck here*)
  eauto.

Qed.
