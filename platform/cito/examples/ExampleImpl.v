Set Implicit Arguments.

Require Import ExampleADT.
Import ExampleADT.ExampleADT.
Require Import RepInv.

Require Import AutoSep.
Require Import WordMap.

Require Import Cell SimpleCell.

Parameter is_fset : W -> WordSet.t -> HProp.
Parameter is_fmap : W -> WordMap.t W -> HProp.

Definition rep_inv p adtvalue : HProp :=
  match adtvalue with
    | FSet s => is_fset p s
    | FMap m => is_fmap p m
    | Cell v => cell v p
  end.

Module ExampleRepInv <: RepInv ExampleADT.

  Definition RepInv := W -> ADTValue -> HProp.

  Definition rep_inv := rep_inv.

  Lemma rep_inv_ptr : forall p a, rep_inv p a ===> p =?> 1 * any.
    destruct a; simpl.
    admit.
    admit.
    eapply Himp_trans; [ apply cell_fwd | sepLemma ]; apply any_easy.
  Qed.

End ExampleRepInv.

Require Import Semantics.
Module Import SemanticsMake := Make ExampleADT.
Require Import List.

Require Import Link.
Module Import LinkMake := Make ExampleADT ExampleRepInv.

Import StubsMake StubMake ConvertLabelMap GoodModule GoodOptimizer.

Definition SimpleCell_newSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => args = nil;
    PostCond := fun _ ret => ret = inr (Cell 0)
  |}.

Definition wrapper_module mname impls (fs : list (string * ForeignFuncSpec * nat * label)) :=
  StructuredModule.bmodule_ impls
  (map (fun (p : string * ForeignFuncSpec * nat * label) => let '(name, ffs, n, delegate) := p in
    (name, foreign_func_spec (mname, name) ffs,
      fun im im_g =>
        Structured.If_ im_g (LvMem (Sp + 4)%loc) IL.Lt n
        (Structured.Goto_ im_g mname ("sys"!"abort")%SP)
        (Structured.Goto_ im_g mname delegate))) fs).

Notation "'ffunction' name 'reserving' n [ ffs ] := lab" :=
  (name, ffs, n, lab%SP) (no associativity, at level 95) : ffuncs_scope.
Delimit Scope ffuncs_scope with ffuncs.

Notation "{{ x 'with' .. 'with' y }}" := (cons x .. (cons y nil) ..) (only parsing) : ffuncs_scope.
  
Notation "'bimport' is 'fmodule' name fs" := (wrapper_module name is%SPimps fs%ffuncs)
  (no associativity, at level 95, name at level 0, only parsing).

Definition m := bimport [[ "sys"!"abort" @ [abortS], "SimpleCell"!"new" @ [newS] ]]
  fmodule "ADT" {{
    ffunction "SimpleCell_new" reserving 8 [SimpleCell_newSpec] := "SimpleCell"!"new"
  }}.

Lemma pure_split : forall P Q R,
  (forall specs sm m, interp specs (P sm m ---> [|Q|]))%PropX
  -> P ===> R
  -> P ===> [|Q|] * R.
  intros; do 3 intro.
  apply existsR with smem_emp.
  apply existsR with m0.
  apply andR.
  apply injR.
  apply split_a_semp_a.
  apply andR.
  eapply Imply_trans; [ apply H | ].
  apply injL; propxFo.
  reflexivity.
  apply H0.
Qed.

Lemma pure_extend : forall P Q R,
  P ===> [|Q|] * any
  -> [|Q|] * P ===> R
  -> P ===> R.
  intros; do 3 intro.
  eapply Imply_trans; [ | apply H0 ].
  apply pure_split; try apply Himp_refl; intros.
  unfold Himp, himp, injB, inj in H.
  eapply Imply_trans; [ apply H | ].
  do 2 (apply existsL; intro).
  repeat (apply andL || (apply injL; intro)).
  apply Inj_I; auto.
Qed.

Definition map_fst A B := map (@fst A B).

Lemma make_map_fst : forall A B, map (@fst A B) = @map_fst A B.
  auto.
Qed.

Ltac fwrap := unfold CompileFuncSpecMake.InvMake2.is_state, Inv.has_extra_stack in *;
  simpl in *; rewrite make_map_fst in *;
    repeat match goal with
             | [ H : context[map] |- _ ] => clear H
           end.

Section scary.
  Import CompileFuncSpecMake.InvMake2 Inv Malloc CompileFuncSpecMake.InvMake SemanticsMake.

  Fixpoint zip_vals (args : list string) (pairs : list (W * ArgIn)) : vals :=
    match args, pairs with
      | arg :: args, (w, _) :: pairs => upd (zip_vals args pairs) arg w
      | _, _ => empty_vs
    end.

  Ltac selify :=
    repeat match goal with
             | [ |- context[upd ?a ?b ?c ?d] ] => change (upd a b c d) with (sel (upd a b c) d)
           end; autorewrite with sepFormula.

  Lemma toArray_dontcare : forall x v vs args,
    ~In x args
    -> toArray args (upd vs x v) = toArray args vs.
    induction args; simpl; intuition idtac.
    f_equal; auto.
    selify; auto.
  Qed.

  Hint Rewrite toArray_dontcare using assumption : sepFormula.

  Lemma unzip : forall args,
    NoDup args
    -> forall pairs, length args = length pairs
      -> toArray args (zip_vals args pairs) = map fst pairs.
    induction 1; destruct pairs; simpl; intuition.
    f_equal; auto; selify; auto.
  Qed.

  Hint Rewrite unzip using assumption : sepFormula.

  Opaque mult.

  Theorem is_state_out : forall sp rp e_stack args pairs,
    NoDup args
    -> ~In "rp" args
    -> ~In "extra_stack" args
    -> length args = length pairs
    -> is_state sp rp e_stack e_stack nil (empty_vs, make_heap pairs) (map fst pairs)
    ===> Ex vs, locals ("rp" :: "extra_stack" :: args) vs (wordToNat (sel vs "extra_stack")) sp
    * is_heap (make_heap pairs) * [| e_stack = wordToNat (sel vs "extra_stack") |].
    unfold is_state, locals, has_extra_stack; simpl.
    intros.
    apply Himp_ex_c.
    exists (upd (upd (zip_vals args pairs) "extra_stack" e_stack) "rp" rp).
    selify.
    replace (S (S (length args)) * 4) with (8 + 4 * length args) by omega.
    rewrite map_length.
    rewrite <- H2.
    rewrite natToWord_plus.
    eapply Himp_trans; [ | do 3 (apply Himp_star_frame; [ | apply Himp_refl ]);
      apply Himp_star_frame; [ apply Himp_refl | apply ptsto32m'_out ] ].
    simpl.
    generalize (map fst pairs); intro.
    unfold array at 1; simpl.
    apply pure_extend with (goodSize e_stack).

    Lemma zig : forall P Q R,
      P ===> R * any
      -> P * Q ===> R * any.
      intros.
      eapply Himp_trans; [ apply Himp_star_frame; [ apply H | apply Himp_refl ] | ].      
      eapply Himp_trans; [ apply Himp_star_assoc | ].
      apply Himp_star_frame; try apply Himp_refl.
      apply any_easy.
    Qed.

    Lemma zag : forall P Q R,
      Q ===> R * any
      -> P * Q ===> R * any.
      intros.
      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply H ] | ].
      eapply Himp_trans; [ apply Himp_star_assoc' | ].
      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_star_comm | apply Himp_refl ] | ].
      eapply Himp_trans; [ apply Himp_star_assoc | ].
      apply Himp_star_frame; try apply Himp_refl.
      apply any_easy.
    Qed.

    do 2 apply zag.
    do 3 intro.
    eapply existsR with smem_emp; apply existsR with m.
    apply andR.
    apply injR.
    apply split_a_semp_a.
    apply andR.
    apply andR.
    eapply Imply_trans; [ apply SepHints.behold_the_array_ls | ].
    do 3 (apply existsL; intro).
    repeat (apply andL || (apply injL; intro)).
    rewrite <- H4.
    apply containsArray_goodSizex'; eauto.
    apply injR; reflexivity.
    apply any_easy.
    apply Himp_star_pure_c; intro; subst.

    sepLemma.
    repeat constructor; simpl; intuition.
    symmetry; apply wordToNat_natToWord_idempotent; auto.
    etransitivity; [ apply himp_star_comm | ].
    apply himp_star_frame.
    etransitivity; [ | apply Arrays.ptsto32m'_in ].
    etransitivity; [ | apply ptsto32m_shift_base ].
    unfold array.
    instantiate (1 := 8).
    simpl.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    reflexivity.
    auto.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    rewrite wordToNat_natToWord_idempotent by auto.
    sepLemma.
  Qed.

  Lemma locals_for_abort : forall res (k : nat) vars vs sp,
    res < natToW k
    -> locals ("rp" :: vars) vs (wordToNat res) sp
    ===> locals ("rp" :: nil) vs 0 sp * any.
    unfold locals; simpl.
    intros.

    apply Himp_trans with ([|NoDup ("rp" :: vars)|] * ptsto32m' _ sp 0 (vs "rp" :: toArray vars vs) *
      (sp ^+ $ (S (Datatypes.length vars) * 4)) =?> wordToNat res)%Sep.
    repeat (apply Himp_star_frame; try apply Himp_refl).
    apply Arrays.ptsto32m'_in.
    unfold array; simpl.
    change (vs "rp") with (sel vs "rp").
    sepLemma.
    apply any_easy.
  Qed.

  Lemma locals_for_method : forall res (k : nat) vars vs sp,
    natToW k <= res
    -> goodSize k
    -> locals vars vs (wordToNat res) sp
    ===> locals vars vs k sp * (sp ^+ $((length vars + k) * 4)) =?> (wordToNat res - k).
    unfold locals; simpl.
    sepLemma.
    etransitivity; [ eapply allocated_split | sepLemma ].
    nomega.
    eapply allocated_shift_base; auto.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    replace (length vars * 4 + 4 * k) with ((length vars + k) * 4) by omega.
    unfold natToW.
    words.
  Qed.

  Theorem is_state_in : forall vs sp args pairs e_stack,
    length args = length pairs
    -> locals ("rp" :: "extra_stack" :: args) vs e_stack sp
      * is_heap (make_heap pairs)
    ===> is_state sp (sel vs "rp") (wordToNat (sel vs "extra_stack")) e_stack nil
    (vs, make_heap pairs) (toArray args vs).
    unfold is_state, locals, has_extra_stack; simpl.
    intros.
    change (vs "rp") with (sel vs "rp").
    change (vs "extra_stack") with (sel vs "extra_stack").
    replace (S (S (length args)) * 4) with (8 + 4 * length args) by omega.
    rewrite natToWord_plus.
    rewrite length_toArray.
    eapply Himp_trans; [ do 2 (apply Himp_star_frame; [ | apply Himp_refl ]);
      apply Himp_star_frame; [ apply Himp_refl | apply Arrays.ptsto32m'_in ] | ].
    simpl.
    unfold array at 1; simpl.
    sepLemma.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.    
    unfold natToW; rewrite natToWord_wordToNat.
    sepLemma.
    etransitivity; [ apply ptsto32m'_out | ].
    unfold array; etransitivity; [ apply ptsto32m_shift_base' | ].
    instantiate (1 := 8); auto.
    simpl.
    change (4 * 0) with 0.
    sepLemma.
  Qed.

  Lemma extra_back_in : forall k vars sp res vs,
    natToW k <= res
    -> goodSize k
    -> (sp ^+ natToW ((k + length vars) * 4)) =?> (wordToNat res - k) * locals vars vs k sp
    ===> locals vars vs (wordToNat res) sp.
    unfold locals; sepLemma.
    etransitivity; [ | eapply allocated_join ]; sepLemma.
    eapply allocated_shift_base; auto.
    repeat rewrite <- wplus_assoc.
    repeat rewrite <- natToWord_plus.
    do 2 f_equal.
    omega.
    nomega.
  Qed.
End scary.

Theorem ok : moduleOk m.
  vcgen.

  sep_auto.

  post.
  fwrap.
  evaluate auto_ext.

  Ltac do_abort argNames :=
    post; repeat match goal with
                   | [ H : map snd ?X = _ |- _ ] => destruct X; simpl in *; try discriminate
                 end;
    match goal with
      | [ H : interp _ _ |- _ ] => eapply CompileExprs.change_hyp in H; [ |
        do 2 (eapply Himp_star_frame; [ | apply Himp_refl ]);
          apply is_state_out; [ instantiate (1 := argNames); auto | .. ]; (simpl; tauto) ]
    end;
    evaluate auto_ext;
    match goal with
      | [ H : interp _ _ |- _ ] => eapply CompileExprs.change_hyp in H; [ |
        do 3 (apply Himp_star_frame; [ apply Himp_refl | ]);
          apply Himp_star_frame; [ eapply locals_for_abort; eassumption | apply Himp_refl ] ]
    end; descend; step auto_ext.

  do_abort (@nil string).

  Lemma Regs_back : forall s : state, (let (Regs, _) := s in Regs) = Regs s.
    auto.
  Qed.

  Ltac do_delegate1 argNames :=
    post; repeat match goal with
                   | [ H : map snd ?X = _ |- _ ] => destruct X; simpl in *; try discriminate
                 end;
    match goal with
      | [ H : interp _ _ |- _ ] => eapply CompileExprs.change_hyp in H; [ |
        do 2 (eapply Himp_star_frame; [ | apply Himp_refl ]);
          apply is_state_out; [ instantiate (1 := argNames); auto | .. ]; (simpl; tauto) ]
    end;
    evaluate auto_ext;
    match goal with
      | [ H : interp _ _ |- _ ] => eapply CompileExprs.change_hyp in H; [ |
        do 3 (apply Himp_star_frame; [ apply Himp_refl | ]);
          apply Himp_star_frame; [ eapply locals_for_method; eassumption || reflexivity | apply Himp_refl ] ]
    end; repeat (descend; step auto_ext); [
      match goal with
        | [ |- context[locals _ ?vs _ _] ] =>
          etransitivity; [ | apply himp_star_frame; [ reflexivity | apply (@is_state_in vs); auto ] ];
          [ | instantiate (1 := argNames); auto ]
      end | ].

  Ltac do_delegate2 argNames :=
    simpl; rewrite Regs_back; step auto_ext;
      match goal with
        | [ _ : natToW ?k <= _ |- _ ] => apply (@extra_back_in k ("rp" :: "extra_stack" :: argNames)); auto
      end.

  Ltac do_delegate argNames tac :=
    do_delegate1 argNames; [ | tac ]; cbv beta; do_delegate2 argNames.

  do_delegate (@nil string) ltac:(simpl; intuition; instantiate (1 := nil); auto).
Qed.
