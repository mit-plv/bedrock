Set Implicit Arguments.

Require Import MakeWrapper ExampleADT ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.

Require Import Notations.
Require Import Notations2.

Definition DirectCall x f args := (Syntax.Label "_f" f ;; Syntax.Call x "_f" args)%stmt.

Notation "'DCall' f ()" := (DirectCall None f nil)
  (no associativity, at level 95, f at level 0) : stmt_scope.

Notation "'DCall' f ( x1 , .. , xN )" := (DirectCall None f (cons x1 (.. (cons xN nil) ..))%expr)
  (no associativity, at level 95, f at level 0) : stmt_scope.
 
Notation "x <-- 'DCall' f ()" := (DirectCall (Some x) f nil)
  (no associativity, at level 95, f at level 0) : stmt_scope.

Notation "x <-- 'DCall' f ( x1 , .. , xN )" := (DirectCall (Some x) f (cons x1 (.. (cons xN nil) ..))%expr) (no associativity, at level 95, f at level 0) : stmt_scope.

Notation "a ! b" := (a, b) : stmt_scope.

Require Import SyntaxExpr.
 
Infix "+" := (SyntaxExpr.Binop Plus) : expr_scope.
Infix "-" := (SyntaxExpr.Binop Minus) : expr_scope.
Infix "*" := (SyntaxExpr.Binop Times) : expr_scope.
Infix "=" := (SyntaxExpr.TestE IL.Eq) : expr_scope.
Infix "<>" := (SyntaxExpr.TestE IL.Ne) : expr_scope.
Infix "<" := (SyntaxExpr.TestE IL.Lt) : expr_scope.
Infix "<=" := (SyntaxExpr.TestE IL.Le) : expr_scope.

Definition f := (
  cfunction "fact"("n")
    If ("n" = $0) {
      "ret" <- $1
    } else {
      "ret" <-- DCall "fact"!"fact" ("n" - $1)
    }
  end
)%Citofuncs.

Definition m := cmodule "fact" {{
  f
}}.

Lemma good : IsGoodModule m.
  good_module.
Qed.

Definition gm := to_good_module good.

Definition fspec :=
  cimport "fact"!"fact"
  cmodules [[ gm ]]
  definition f.

Notation extra_stack := 100.

Definition topS := SPEC reserving (4 + extra_stack)
  PREonly[_] mallocHeap 0.

Fixpoint fact n :=
  match n with
    | 0 => 1
    | S n' => (n * fact n')%nat
  end.

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
(*
Lemma body_safe : forall env v, Safe env (Body f) v.
  econstructor; eauto.
Qed.

Lemma body_runsto : forall env v v', RunsTo env (Body f) v v'
  -> sel (fst v') (RetVar f) = 0 /\ snd v' = snd v.
  intros.
  inversion_clear H.
  subst vs.
  simpl.
  split.
  apply sel_upd_eq; auto.
  auto.
Qed.
*)

Require Import Inv.
Module Import InvMake := Make ExampleADT.
Module Import InvMake2 := Make ExampleRepInv.
Import Made.

Theorem is_state_in'' : forall vs sp args e_stack h, locals ("rp" :: "extra_stack" :: args) vs e_stack sp * is_heap h ===> is_state sp (sel vs "rp") (wordToNat (sel vs "extra_stack")) e_stack args (vs, h) nil.
Proof.
  intros; sepLemma.
  set (_ :: _ :: _).
  set (_ * _)%Sep.
  etransitivity.
  instantiate (1 := (h0 * [| NoDup l |])%Sep).
  subst h0 l.
  unfold locals.
  set (array _ _).
  sepLemma.
  subst h0 l.
  sepLemma.
  etransitivity.
  etransitivity.
  2 : eapply is_state_in.
  sepLemma.
  change LinkMake.StubsMake.StubMake.LinkSpecMake2.CompileFuncSpecMake.InvMake2.is_state with is_state.
  unfold is_state, has_extra_stack, locals, array.
  Opaque mult.
  sepLemma.
  inversion_clear H.
  inversion_clear H2.
  eauto.
  fold (@length W).
  Require Import Mult.
  rewrite mult_0_r.
  Require Import WordFacts.
  rewrite wplus_0.
  rewrite plus_0_r.
  rewrite length_toArray.
  sepLemma.
  Transparent mult.
Qed.

Theorem is_state_in''' : forall vs sp args e_stack F,
  locals ("rp" :: "extra_stack" :: args) vs e_stack sp
  * mallocHeap 0 * F
  ===> is_state sp (sel vs "rp") (wordToNat (sel vs "extra_stack")) e_stack args
  (vs, heap_empty) nil * mallocHeap 0 * F.
  intros; sepLemma.
  etransitivity; [ | apply is_state_in'' ]; auto.
  sepLemma.
Qed.

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
  Import LinkSpecMake.
  Lemma body_safe : forall stn fs v, stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
    admit.
  Qed.
  apply body_safe; eauto.
  hiding ltac:(step auto_ext).
  repeat ((apply existsL; intro) || (apply injL; intro) || apply andL); reduce.
  apply swap; apply injL; intro.
  openhyp.
  Import LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.
  match goal with
    | [ x : State |- _ ] => destruct x; simpl in *
  end.
  Lemma body_runsto : forall stn fs v v', stn_good_to_use (gm :: nil) (empty _) stn -> fs_good_to_use (gm :: nil) (empty _) fs stn -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = $ (fact (wordToNat (sel (fst v) "n"))) /\ snd v' = snd v.
    admit.
  Qed.

  apply body_runsto in H9; simpl in H9; intuition subst.
  eapply replace_imp.
  change 100 with (wordToNat (sel (upd (upd x2 "extra_stack" 100) "n" 5) "extra_stack")).
  Theorem is_state_out''' : forall sp rp args pairs vs e_stack e_stack',
    NoDup args
    -> ~List.In "rp" args
    -> ~List.In "extra_stack" args
    -> toArray args vs = List.map fst pairs
    -> is_state sp rp e_stack e_stack' args
    (vs, make_heap pairs) nil
    ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp
    * is_heap (make_heap pairs) * [| sel vs' "extra_stack" = e_stack |]
    * [| saved_vars vs' args pairs |].
    unfold Himp; intros.
    etransitivity.
    2 : eapply is_state_out''; eauto.
    Lemma toArray_map_length : forall A vs f ls1 ls2, toArray ls1 vs = @List.map A _ f ls2 -> length ls1 = length ls2.
      intros.
      eapply f_equal with (f := @length _) in H.
      rewrite length_toArray in *.
      rewrite map_length in *.
      eauto.
    Qed.
    2 : eapply toArray_map_length; eauto.
    Opaque mult.
    change LinkSpecMake2.CompileFuncSpecMake.InvMake2.is_state with is_state.
    change LinkMake.StubsMake.StubMake.LinkSpecMake2.CompileFuncSpecMake.InvMake.make_heap with make_heap.
    unfold is_state, locals, has_extra_stack; simpl.
    rewrite H2.
    rewrite mult_0_r.
    rewrite wplus_0.
    set (array (List.map _ _) _).
    set (is_heap _).
    rewrite map_length.
    replace (length args) with (length pairs).
    rewrite plus_0_r.
    Ltac clear_all :=
      repeat match goal with
               | H : _ |- _ => clear H
             end.
    clear_all.
    sepLemma.
    symmetry; eapply toArray_map_length; eauto.
    Transparent mult.
    Grab Existential Variables.
    eauto.
  Qed.

  Theorem is_state_out'''' : forall vs sp rp F e_stack e_stack' args,
    NoDup args
    -> ~List.In "rp" args
    -> ~List.In "extra_stack" args
    -> (is_state sp rp e_stack e_stack' args
      (vs, heap_empty) nil * mallocHeap 0) * F
    ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp
    * [| sel vs' "extra_stack" = e_stack|]
    * mallocHeap 0 * F.
    intros.
    assert (make_heap (List.map (fun w => (w, inl w)) (toArray args vs)) = heap_empty).
    Lemma make_heap_heap_empty : forall ls, make_heap (List.map (fun w : W => (w) ! (inl w)%stmt) ls) = heap_empty.
      induction ls; simpl; intuition.
    Qed.
    eapply make_heap_heap_empty.
    rewrite <- H2.
    eapply Himp_trans; [ do 2 (apply Himp_star_frame; [ | apply Himp_refl ]); apply is_state_out''' | ]; eauto.
    rewrite map_map; simpl.
    Lemma map_id : forall A ls, List.map (fun x : A => x) ls = ls.
      induction ls; simpl; intuition.
    Qed.
    symmetry; eapply map_id.
    repeat rewrite H2.
    set (_ :: _ :: _).
    set (List.map _ _).
    clear_all.
    sepLemma.
  Qed.

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

Definition all := link top (link_with_adts gm).

Theorem all_ok : moduleOk all.
  link0 top_ok.
Qed.
