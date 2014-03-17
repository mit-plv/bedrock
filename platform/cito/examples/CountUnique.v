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
Require Import GLabelMap.
Import GLabelMap.GLabelMap.
Require Import SemanticsFacts4.
Module Import SemanticsFacts4Make := Make ExampleADT.
Import TransitMake.

Definition strengthen_op_ax (spec_op : InternalFuncSpec) spec_ax env_ax :=
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

Definition strengthen_specs specs_op specs_ax env_ax :=
  forall (lbl : glabel),
    find lbl specs_op = find lbl specs_ax \/
    exists spec_op spec_ax,
      find lbl specs_op = Some (Internal spec_op) /\
      find lbl specs_ax = Some (Foreign spec_ax) /\
      strengthen_op_ax spec_op spec_ax env_ax.

Lemma strengthen_specs_strengthen : forall specs_op specs_ax env_op env_ax, strengthen_specs specs_op specs_ax env_ax -> specs_env_agree specs_op env_op -> specs_env_agree specs_ax env_ax -> (forall lbl, fst env_op lbl = fst env_ax lbl) -> strengthen env_op env_ax.
Proof.
  split; intros.
  eauto.
  destruct (option_dec (fs_op w)).
  destruct s.
  destruct H0.
  generalize e; intro.
  eapply H3 in e.
  openhyp.
  edestruct (H x0).
  left.
  rewrite e0.
  symmetry.
  destruct H1.
  eapply H7.
  unfold Callee in H5.
  rewrite H6 in H5; clear H6.
  descend; eauto.
  rewrite <- H2.
  eauto.
  openhyp.
  unfold Callee in H5.
  rewrite H6 in H5; injection H5; intros; subst.
  assert (fs_ax w = Some (Foreign x2)).
  destruct H1.
  eapply H9.
  descend; eauto.
  rewrite <- H2; eauto.
  right; descend; eauto.
  destruct (option_dec (fs_ax w)).
  destruct s.
  destruct H1.
  generalize e0; intro.
  eapply H3 in e0.
  openhyp.
  edestruct (H x0).
  assert (fs_op w = Some x).
  destruct H0.
  eapply H7.
  descend; eauto.
  rewrite H2; eauto.
  unfold Callee.
  rewrite H6.
  eauto.
  rewrite H7 in e; intuition.
  openhyp.
  assert (fs_op w = Some (Internal x1)).
  destruct H0.
  eapply H9.
  descend; eauto.
  rewrite H2; eauto.
  rewrite H9 in e; intuition.
  left; congruence.
Qed.

Definition apply_specs_diff specs specs_diff := update specs (map Foreign specs_diff).

Definition strengthen_diff_f specs env_ax k v a :=
  a /\
  (find k specs = Some (Foreign v) \/
   exists op, 
     find k specs = Some (Internal op) /\
     strengthen_op_ax op v env_ax).

Definition strengthen_diff specs specs_diff env_ax :=
  fold (strengthen_diff_f specs env_ax) specs_diff True.

Require Import GeneralTactics2.

Lemma strengthen_diff_elim : forall specs_diff env_ax specs, strengthen_diff specs specs_diff env_ax -> forall lbl ax, find lbl specs_diff = Some ax -> find lbl specs = Some (Foreign ax) \/ exists op, find lbl specs = Some (Internal op) /\ strengthen_op_ax op ax env_ax.
  do 3 intro.
  eapply fold_rec_bis with (P := fun specs_diff (H : Prop) => H -> forall lbl ax, find lbl specs_diff = Some ax -> find lbl specs = Some (Foreign ax) \/ exists op, find lbl specs = Some (Internal op) /\ strengthen_op_ax op ax env_ax); simpl; intros.
  eapply H0; eauto.
  rewrite H; eauto.
  rewrite empty_o in H0; intuition.
  eapply find_mapsto_iff in H3.
  eapply add_mapsto_iff in H3.
  openhyp.
  subst.
  destruct H2.
  openhyp.
  eauto.
  right; descend; eauto.
  eapply H1.
  destruct H2; eauto.
  eapply find_mapsto_iff; eauto.
Qed.

Lemma strengthen_diff_strengthen_specs : forall specs specs_diff env_ax, strengthen_diff specs specs_diff env_ax -> strengthen_specs specs (apply_specs_diff specs specs_diff) env_ax.
  intros.
  unfold strengthen_specs.
  intros.
  destruct (option_dec (find lbl specs_diff)).
  destruct s.
  eapply strengthen_diff_elim in H; eauto.
  openhyp.
  left.
  rewrite H.
  symmetry.
  eapply find_mapsto_iff.
  eapply update_mapsto_iff.
  left.
  eapply find_mapsto_iff.
  rewrite map_o.
  rewrite e.
  eauto.
  right; descend; eauto.
  eapply find_mapsto_iff.
  eapply update_mapsto_iff.
  left.
  eapply find_mapsto_iff.
  rewrite map_o.
  rewrite e.
  eauto.
  left.
  unfold apply_specs_diff.
  rewrite update_o_1; eauto.
  nintro.
  eapply map_4 in H0.
  eapply In_find_not_None in H0.
  erewrite e in H0.
  intuition.
Qed.

Lemma strengthen_diff_strenghthen : forall specs specs_diff env_op env_ax, strengthen_diff specs specs_diff env_ax -> specs_env_agree specs env_op -> specs_env_agree (apply_specs_diff specs specs_diff) env_ax -> (forall lbl, fst env_op lbl = fst env_ax lbl) -> strengthen env_op env_ax.
  intros.
  eapply strengthen_specs_strengthen; eauto.
  eapply strengthen_diff_strengthen_specs; eauto.
Qed.

Definition sub_domain elt1 elt2 (m1 : t elt1) (m2 : t elt2) := forall k, In k m1 -> In k m2.
Definition equal_domain elt1 elt2 (m1 : t elt1) (m2 : t elt2) := sub_domain m1 m2 /\ sub_domain m2 m1.

Definition is_pointer_of_label specs (stn : glabel -> option W) w : option Callee :=
  fold (fun k v res => 
          match res with
            | Some _ => res
            | None => 
              match stn k with
                | Some w' => if weq w w' then Some v else None
                | None => None
              end
          end
       ) specs None.

Definition change_env new_specs (env : Env) : Env :=
  let stn := fst env in
  let fs := snd env in
  (stn,
   fun w =>
     match is_pointer_of_label new_specs stn w with
       | Some new_spec => Some new_spec
       | None => fs w
     end).

Definition stn_nodup (specs : t Callee) stn := forall lbl1 lbl2 (w : W), In lbl1 specs -> In lbl2 specs -> stn lbl1 = Some w -> stn lbl2 = Some w -> lbl1 = lbl2.

Lemma sub_domain_stn_nodup : forall specs1 specs2 stn, stn_nodup specs1 stn -> sub_domain specs2 specs1 -> stn_nodup specs2 stn.
  unfold stn_nodup, sub_domain; intros.
  eapply H; eauto.
Qed.

Lemma add_stn_nodup : forall specs k v stn, stn_nodup (add k v specs) stn -> stn_nodup specs stn.
  intros.
  eapply sub_domain_stn_nodup; eauto.
  unfold sub_domain; intros.
  eapply add_in_iff; eauto.
Qed.

Lemma is_pointer_of_label_intro_elim : forall specs stn w, (forall v, is_pointer_of_label specs stn w = Some v -> exists lbl, find lbl specs = Some v /\ stn lbl = Some w) /\ (forall v lbl, stn_nodup specs stn -> find lbl specs = Some v -> stn lbl = Some w -> is_pointer_of_label specs stn w = Some v).
  do 3 intro.
  eapply fold_rec_bis with (P := fun specs a => (forall v, a = Some v -> exists lbl, find lbl specs = Some v /\ stn lbl = Some w) /\ (forall v lbl, stn_nodup specs stn -> find lbl specs = Some v -> stn lbl = Some w -> a = Some v)); simpl; intros.
  unfold stn_nodup in *.
  setoid_rewrite H in H0.
  eapply H0; eauto.
  split; intros.
  intuition.
  rewrite empty_o in H0; intuition.
  openhyp.
  split; intros.
  destruct a.
  injection H3; intros; subst.
  edestruct H1; eauto.
  openhyp.
  descend; eauto.
  eapply find_mapsto_iff; eapply add_mapsto_iff.
  right.
  split.
  nintro; subst.
  eapply find_mapsto_iff in H4; eapply MapsTo_In in H4.
  contradiction.
  eapply find_mapsto_iff; eauto.
  destruct (option_dec (stn k)).
  destruct s.
  rewrite e0 in *.
  destruct (weq w x).
  subst.
  injection H3; intros; subst.
  descend; eauto.
  eapply find_mapsto_iff; eapply add_mapsto_iff.
  eauto.
  intuition.
  rewrite e0 in *; intuition.
  destruct a.
  edestruct H1; eauto.
  openhyp.
  eapply find_mapsto_iff in H4; eapply find_mapsto_iff in H6.
  assert (lbl = x).
  eapply H3; eauto.
  eapply MapsTo_In; eauto.
  eapply add_in_iff; right; eapply MapsTo_In; eauto.
  subst.
  eapply add_mapsto_iff in H4; openhyp.
  subst.
  eapply MapsTo_In in H6; contradiction.
  eapply H2; eauto.
  eapply add_stn_nodup; eauto.
  eapply find_mapsto_iff; eauto.

  eapply find_mapsto_iff in H4.
  destruct (option_dec (stn k)).
  destruct s.
  rewrite e0 in *.
  eapply add_mapsto_iff in H4; openhyp.
  subst.
  rewrite H5 in e0; injection e0; intros; subst.
  destruct (weq x x); intuition.
  destruct (weq w x).
  subst.
  contradict H4.
  eapply H3; eauto.
  eapply add_in_iff; eauto.
  eapply add_in_iff; right; eapply MapsTo_In; eauto.
  eapply H2; eauto.
  eapply add_stn_nodup; eauto.
  eapply find_mapsto_iff; eauto.
  rewrite e0 in *.
  eapply add_mapsto_iff in H4; openhyp.
  subst.
  rewrite H5 in e0; intuition.
  eapply H2; eauto.
  eapply add_stn_nodup; eauto.
  eapply find_mapsto_iff; eauto.
Qed.

Lemma is_pointer_of_label_intro : forall specs stn w v lbl, stn_nodup specs stn -> find lbl specs = Some v -> stn lbl = Some w -> is_pointer_of_label specs stn w = Some v.
  eapply is_pointer_of_label_intro_elim; eauto.
Qed.

Lemma is_pointer_of_label_elim : forall specs stn w v, is_pointer_of_label specs stn w = Some v -> exists lbl, find lbl specs = Some v /\ stn lbl = Some w.
  eapply is_pointer_of_label_intro_elim; eauto.
Qed.

Lemma NoDup_stn_nodup : forall specs fs stn, List.NoDup (List.map snd (elements specs)) -> specs_fs_agree specs (stn, fs) -> forall new_specs, stn_nodup new_specs stn.
  admit.
Qed.

Lemma change_env_agree : forall specs new_specs, List.NoDup (List.map snd (elements specs)) -> equal_domain new_specs specs -> forall env, specs_env_agree specs env -> specs_env_agree new_specs (change_env new_specs env).
Proof.
  unfold specs_env_agree.
  intros.
  openhyp.
  simpl.
  split.
  unfold labels_in_scope in *.
  intros.
  eapply H1.
  destruct H0.
  eapply H0; eauto.
  
  unfold specs_fs_agree in *.
  split; intros.
  simpl in *.
  destruct env in *; simpl in *.
  destruct (option_dec (is_pointer_of_label new_specs o p)).
  destruct s.
  rewrite e in *.
  injection H3; intros; subst.
  eapply is_pointer_of_label_elim in e; openhyp.
  descend; eauto.
  rewrite e in *.
  eapply H2 in H3; openhyp.
  eapply find_mapsto_iff in H4; eapply MapsTo_In in H4.
  destruct H0.
  eapply H5 in H4.
  eapply In_MapsTo in H4; openhyp.
  assert (is_pointer_of_label new_specs o p = Some x0).
  eapply is_pointer_of_label_intro; eauto.
  eapply NoDup_stn_nodup; eauto.
  eapply find_mapsto_iff; eauto.
  rewrite e in H6; intuition.
  openhyp.
  simpl in *.
  destruct env; simpl in *.
  assert (is_pointer_of_label new_specs o p = Some spec0).
  eapply is_pointer_of_label_intro; eauto.
  eapply NoDup_stn_nodup; eauto.
  rewrite H5; eauto.
Qed.

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

Import GLabelMap.GLabelMap.

Definition make_specs modules imports := fold_right (fun m acc => fold_right (fun (f : GoodFunction) acc => add (GName m, FName f) (Internal f) acc) acc (Functions m)) (map Foreign imports) modules.

Definition specs_change_table :=
  of_list
    [[
        "count"!"count" @ [count_spec],
        "count"!"main" @ [main_spec]
    ]]%stmtex.

Definition specs := apply_specs_diff (make_specs modules imports) specs_change_table.

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
  Import ProgramLogicMake.
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

Import LinkSpecMake.
Require Import LinkSpecFacts.
Module Import LinkSpecFactsMake := Make ExampleADT.
Import Notations4Make.

Lemma make_specs_equal : forall modules imports, specs_equal (make_specs modules imports) modules imports.
  admit.
Qed.

Definition specs_op := make_specs modules imports.

Lemma count_strengthen : forall env_ax, specs_env_agree specs env_ax -> strengthen_op_ax count count_spec env_ax.
  admit.
Qed.

Lemma main_strengthen : forall env_ax, specs_env_agree specs env_ax -> strengthen_op_ax main main_spec env_ax.
  intros.
  unfold strengthen_op_ax.
  split_all.
  intros.
  simpl in *.
  rewrite H0; simpl; eauto.
  intros.
  cito_safe main empty_precond main_vcs_good.
  cito_runsto main empty_precond main_vcs_good.
  2 : eauto.
  Import SemanticsFacts4Make.TransitMake.
  unfold TransitTo.
  descend.
  instantiate (1 := [[]]).
  eauto.
  simpl.
  Import SemanticsMake.
  repeat econstructor.
  eauto.
  eauto.
  simpl.
  repeat econstructor.
  simpl.
  admit. (* snd v' == snd v -> snd v' = snd v *)
  unfold decide_ret, Semantics.decide_ret.
  simpl.
  eauto.
  Grab Existential Variables.
  eapply ($0).
Qed.

Lemma specs_strengthen_diff : forall env_ax, specs_env_agree specs env_ax -> strengthen_diff (make_specs modules imports) specs_change_table env_ax.
  intros.
  unfold strengthen_diff.
  rewrite GLabelMap.fold_1.
  Opaque make_specs specs.
  simpl.
  Transparent make_specs specs.
  unfold strengthen_diff_f.
  split_all.
  eauto.
  right.
  eexists.
  split.
  reflexivity.
  eapply count_strengthen; eauto.
  right.
  eexists.
  split.
  reflexivity.
  eapply main_strengthen; eauto.
Qed.

Import GLabelMap.GLabelMap.
Import GLabelMapFacts.
Definition sub_domain_dec elt1 elt2 (m1 : t elt1) (m2 : t elt2) := forallb (fun k => mem k m2) (keys m1).
Lemma sub_domain_dec_sound : forall elt1 elt2 (m1 : t elt1) (m2 : t elt2), sub_domain_dec m1 m2 = true -> sub_domain m1 m2.
  intros.
  unfold sub_domain_dec, sub_domain in *.
  intros.
  eapply forallb_forall in H.
  eapply mem_in_iff; eauto.
  Require Import SetoidListFacts.
  eapply InA_In.
  eapply In_In_keys; eauto.
Qed.
Definition equal_domain_dec elt1 elt2 (m1 : t elt1) (m2 : t elt2) := (sub_domain_dec m1 m2 && sub_domain_dec m2 m1)%bool.
Lemma equal_domain_dec_sound : forall elt1 elt2 (m1 : t elt1) (m2 : t elt2), equal_domain_dec m1 m2 = true -> equal_domain m1 m2.
  unfold equal_domain_dec, equal_domain; intros.
  eapply Bool.andb_true_iff in H; openhyp.
  eapply sub_domain_dec_sound in H.
  eapply sub_domain_dec_sound in H0.
  eauto.
Qed.
Lemma specs_equal_domain : equal_domain specs specs_op.
  eapply equal_domain_dec_sound; reflexivity.
Qed.

Lemma main_runsto : forall stn fs v v', stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body main) v v' -> sel (fst v') (RetVar f) = 2 /\ snd v' == snd v.
  intros.
  eapply strengthen_runsto with (env_ax := change_env specs (from_bedrock_label_map (Labels stn), fs0 stn)) in H1.
  cito_runsto main empty_precond main_vcs_good.
  split; eauto.
  eapply change_env_agree.
  Focus 3.
  eapply specs_equal_agree; eauto.
  eapply make_specs_equal.
  admit. (* NoDup _ *)
  eapply specs_equal_domain.
  eauto.
  eapply strengthen_diff_strenghthen.
  Focus 2.
  eapply specs_equal_agree; eauto.
  eapply make_specs_equal.
  Focus 2.
  eapply change_env_agree.
  Focus 3.
  eapply specs_equal_agree; eauto.
  eapply make_specs_equal.
  admit. (* NoDup _ *)
  eapply specs_equal_domain.
  eapply specs_strengthen_diff.
  eapply change_env_agree.
  Focus 3.
  eapply specs_equal_agree; eauto.
  eapply make_specs_equal.
  admit. (* NoDup _ *)
  eapply specs_equal_domain.
  intros; simpl.
  eauto.
Qed.

Lemma main_safe : forall stn fs v, stn_good_to_use modules imports stn -> fs_good_to_use modules imports fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body main) v.
  intros.
  eapply strengthen_safe with (env_ax := change_env specs (from_bedrock_label_map (Labels stn), fs0 stn)).
  cito_safe main empty_precond main_vcs_good.
  eapply change_env_agree.
  Focus 3.
  eapply specs_equal_agree; eauto.
  eapply make_specs_equal.
  admit. (* NoDup _ *)
  eapply specs_equal_domain.
  eapply strengthen_diff_strenghthen.
  Focus 2.
  eapply specs_equal_agree; eauto.
  eapply make_specs_equal.
  Focus 2.
  eapply change_env_agree.
  Focus 3.
  eapply specs_equal_agree; eauto.
  eapply make_specs_equal.
  admit. (* NoDup _ *)
  eapply specs_equal_domain.
  eapply specs_strengthen_diff.
  eapply change_env_agree.
  Focus 3.
  eapply specs_equal_agree; eauto.
  eapply make_specs_equal.
  admit. (* NoDup _ *)
  eapply specs_equal_domain.
  intros; simpl.
  eauto.
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
  link0 top_ok.
Qed.
