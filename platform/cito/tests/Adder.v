Require Import Compile.


Definition adder := cfunction "adder"("a", "b", "c")
  "a" <== "__arg"[1];;
  "b" <== "__arg"[2];;
  "c" <- "a" + "b";;
  "__arg"[0] <== "c"
end.

Definition m := cmodule "Adder" {{
  adder
}}.

Theorem ok : moduleOk m.
  compile.
Qed.

Definition addS := SPEC("in1", "in2") reserving 45
  PRE[V] mallocHeap 0
  POST[R] [| R = V "in1" ^+ V "in2" |] * mallocHeap 0.

Definition mainS := SPEC reserving 49
  PREonly[V] mallocHeap 0.

Definition returnOk (arr in1 in2 : W) (arrs : arrays) :=
  fst arrs = WMake.add WMake.empty (arr ^+ $8)
  /\ let ls := snd arrs (arr ^+ $8) in
    length ls = 3 /\ Array.sel ls 0 = in1 ^+ in2.

Definition heap_returnOk (_ _ _ : W) := heap.

Lemma WMake_add : forall ls s s',
  WMake.equiv s
  (fold_left WMake.add ls s')
  -> List.Forall (fun x => WMake.mem x s) ls /\ WMake.incl s' s.
  induction ls; simpl; intuition.
  apply IHls in H; intuition.
  apply IHls in H; intuition.
Qed.

Lemma singleton_equiv : forall arr x,
  WMake.equiv (WMake.add WMake.empty (arr ^+ $8)) (WMake.setify x)
  -> NoDup x
  -> x = (arr ^+ $8) :: nil.
  unfold WMake.setify; destruct x; simpl; intros.
  WMake.sets.
  specialize (H (arr ^+ $8)); tauto.
  inversion_clear H0.
  specialize (WMake_add _ _ _ H); intuition idtac.
  assert (a = arr ^+ $8) by WMake.sets.
  f_equal; auto.
  destruct x; simpl in *; auto.
  inversion_clear H3.
  assert (a0 = arr ^+ $8) by WMake.sets.
  subst; tauto.
Qed.

Lemma array3 : forall p a b c,
  array (a :: b :: c :: nil) p = (p =*> a * ((p ^+ $4) =*> b * (p ^+ $8) =*> c))%Sep.
  auto.
Qed.

Hint Rewrite array3 : sepFormula.

Theorem returnOk_fwd : forall arr in1 in2 arrs,
  returnOk arr in1 in2 arrs
  -> heap_returnOk arr in1 in2 arrs
  ===> Ex a, Ex b, Ex c, Ex d, (arr ==*> a, b, in1 ^+ in2, c, d) * [| arr <> 0 |] * [| freeable arr 5 |].
  intros.
  destruct arrs.
  hnf in H; simpl in *; intuition subst.
  apply Himp'_ex; intro.
  eapply Himp_trans; [ apply Himp_star_assoc | ].
  do 2 (apply Himp_star_pure_c; intro).
  apply singleton_equiv in H0; auto; subst.
  simpl.
  unfold array_ptr, MyMalloc.array_with_size.
  rewrite H.
  destruct (d (arr ^+ $8)); try discriminate; simpl in *.
  do 3 (destruct d0; try discriminate; simpl in *).
  sepLemma; autorewrite with sepFormula in *; auto.
  sepLemma.
  rewrite <- H2.
  reflexivity.
Qed.

Definition hints : TacPackage.
  prepare returnOk_fwd singletonArray_bwd.
Defined.

Inductive please_unfold := PleaseUnfold.
Local Hint Constructors please_unfold.

Definition main := bimport [[ "Cito_Adder"!"adder" @ [funcSpec adder],
                              "sys"!"printInt" @ [printIntS], "sys"!"abort" @ [abortS],
                              "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "test" {{
    bfunction "main"("n") [mainS]
      "n" <-- Call "test"!"add"(5, 7)
      [PREonly[_, R] [| R = 12 |] ];;

      Call "sys"!"printInt"("n")
      [PREonly[_] Emp];;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ];;

      Fail
    end with bfunction "add"("in1", "in2", "arr", "tmp") [addS]
      "arr" <-- Call "malloc"!"malloc"(0, 5)
      [PRE[V, R] R =?> 5 * [| R <> 0 |] * [| freeable R 5 |] * mallocHeap 0
        POST[R'] [| R' = V "in1" ^+ V "in2" |] * mallocHeap 0];;

      "arr" + 4 *<- 3;;
      "arr" + 8 *<- 0;;
      "arr" + 12 *<- "in1";;
      "arr" + 16 *<- "in2";;

      Assert [PRE[V] heap (singletonArray (V "arr" ^+ natToW 8) ($0 :: V "in1" :: V "in2" :: nil)) * mallocHeap 0
        POST[R] [| R = V "in1" ^+ V "in2" |] * mallocHeap 0];;

      "tmp" <- "arr" + 8;;
      Note [please_unfold];;
      Call "Cito_Adder"!"adder"(40, "tmp")
      [Al arrs,
        PRE[V] heap_returnOk (V "arr") (V "in1") (V "in2") arrs * mallocHeap 0
          * [| returnOk (V "arr") (V "in1") (V "in2") arrs |]
        POST[R] [| R = V "in1" ^+ V "in2" |] * mallocHeap 0];;

      Assert [Al a, Al b, Al c, Al d,
        PRE[V] (V "arr" ==*> a, b, V "in1" ^+ V "in2", c, d) * mallocHeap 0
          * [| V "arr" <> 0 |] * [| freeable (V "arr") 5 |]
        POST[R] [| R = V "in1" ^+ V "in2" |] * mallocHeap 0];;

      "tmp" <-* "arr" + 8;;
      Call "malloc"!"free"(0, "arr", 5)
      [PRE[V] Emp
       POST[R] [| R = V "tmp" |] ];;

      Return "tmp"
    end
  }}.

Ltac returnOk :=
  match goal with
    | [ |- returnOk _ _ _ _ ] => 
      RunsTo; hnf; descend; auto; reflexivity
  end.

Ltac t :=
  try match goal with
        | [ |- context[please_unfold] ] => unfold heap_returnOk
      end;
  sep hints (fun _ : W => @None Callee); auto; returnOk.

Theorem mainOk : moduleOk main.
  vcgen; abstract t.
Qed.
