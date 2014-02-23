Set Implicit Arguments.

Require Import ExampleADT.
Import ExampleADT.ExampleADT.
Require Import RepInv.

Require Import AutoSep.
Require Import WordMap.

Parameter is_fset : W -> WordSet.t -> HProp.
Parameter is_fmap : W -> WordMap.t W -> HProp.

Fixpoint rep_inv p adtvalue : HProp :=
  match adtvalue with
    | FSet s => is_fset p s
    | FMap m => is_fmap p m
    | Cell v => (p =*> v)%Sep
  end.

Module ExampleRepInv <: RepInv ExampleADT.

  Definition RepInv := W -> ADTValue -> HProp.

  Definition rep_inv := rep_inv.

  Lemma rep_inv_ptr : forall p a, rep_inv p a ===> p =?> 1 * any.
    admit.
  Qed.

End ExampleRepInv.

Require Import Semantics.
Module Import SemanticsMake := Make ExampleADT.
Require Import List.

Definition addPostCond := fun ins outs => length ins = 2 /\ length outs = 2 /\ exists s w, nth_error ins 0 = Some (inr (FSet s)) /\ nth_error ins 1 = Some (inl w) /\ nth_error outs 0 = Some (Some (FSet (WordSet.add w s))).

Definition addSpec : ForeignFuncSpec := 
  {|
    PreCond := fun args => exists outs, addPostCond args outs ;
    PostCond := fun pairs ret => addPostCond (List.map fst pairs) (List.map snd pairs)
  |}.

Require Import Link.
Module Import LinkMake := Make ExampleADT ExampleRepInv.

Import StubsMake StubMake ConvertLabelMap GoodModule GoodOptimizer.
Import ListNotations.

Definition addS := foreign_func_spec_FFS ("fset", "add") addSpec.

Definition add : StructuredModule.function "fset" := ("add", addS, fun im im_g => Goto_ im_g "fset" ("fset_impl"!"add")%SP).

Require Import Malloc.

Definition addS_impl := SPEC("extra_stack", "s", "a") reserving 0
  Al s,
  PRE[V] is_fset (V "s") s * mallocHeap 0
  POST[_] is_fset (V "s") (WordSet.add (V "a") s) * mallocHeap 0.

Definition fset := StructuredModule.bmodule_ [ ("fset_impl"!"add" @ [addS_impl])%SPimps ] [add].

Theorem fset_ok : moduleOk fset.
  vcgen.
  post.
  post.
  Import CompileFuncSpecMake CompileFuncSpecMake.InvMake2 CompileFuncSpecMake.InvMake CompileFuncSpecMake.InvMake.SemanticsMake Inv.
  unfold is_state in *; simpl in *.
  descend.
  Admitted.

Definition fset_impl := bimport [[ "malloc"!"malloc" @ [mallocS] ]]
bmodule "fset_impl" {{
  bfunction "add"("s", "w") [addS_impl]
    Return 0
  end
}}.
