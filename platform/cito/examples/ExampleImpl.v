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

Theorem ok : moduleOk m.
  vcgen.

  sep_auto.

  Opaque mult.

  Definition map_fst A B := map (@fst A B).

  Lemma make_map_fst : forall A B, map (@fst A B) = @map_fst A B.
    auto.
  Qed.

  Ltac fwrap := unfold CompileFuncSpecMake.InvMake2.is_state, Inv.has_extra_stack in *;
    simpl in *; rewrite make_map_fst in *;
      repeat match goal with
               | [ H : context[map] |- _ ] => clear H
             end.

  post.
  fwrap.
  evaluate auto_ext.

  post.
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

  Theorem is_state_out : forall sp rp e_stack args pairs,
    NoDup args
    -> ~In "rp" args
    -> ~In "extra_stack" args
    -> length args = length pairs
    -> is_state sp rp e_stack e_stack nil (empty_vs, make_heap pairs) (map fst pairs)
    ===> Ex vs, locals ("rp" :: "extra_stack" :: args) vs (wordToNat (sel vs "extra_stack")) sp
    * is_heap (make_heap pairs).
    unfold is_state, locals, has_extra_stack; simpl.
    intros.
    apply Himp_ex_c.
    exists (upd (upd (zip_vals args pairs) "extra_stack" e_stack) "rp" rp).
    selify.
    replace (S (S (length args)) * 4) with (8 + 4 * length args) by omega.
    rewrite map_length.
    rewrite <- H2.
    rewrite natToWord_plus.
    eapply Himp_trans; [ | do 2 (apply Himp_star_frame; [ | apply Himp_refl ]);
      apply Himp_star_frame; [ apply Himp_refl | apply ptsto32m'_out ] ].
    simpl.
    generalize (map fst pairs); intro.
    unfold array at 1; simpl.
    sepLemma.
    repeat constructor; simpl; intuition.
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
    (* This step just needs to use the fact that only a [goodSize] may appear after [=?>]. *)
  Admitted.

  eapply CompileExprs.change_hyp in H2.
  Focus 2.
  apply Himp_star_frame.
  apply Himp_star_frame.
  apply is_state_out.
  instantiate (1 := nil).
  auto.
  simpl; tauto.
  simpl; tauto.
  destruct x0; auto; discriminate.
  apply Himp_refl.
  apply Himp_refl.
  clear H5.
  evaluate auto_ext.
  descend.
  (* Here, need to split [locals] to indicate an unused free space. *)
