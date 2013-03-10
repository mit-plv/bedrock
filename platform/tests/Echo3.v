Require Import Thread Arrays8.


(* Move this to Thread *)
Import Bags.W_Bag.

Module Type S.
  Variables globalSched globalSock : W.
End S.

Module Make(M : S).
Import M.

Module M'''.
  Definition globalSched := M.globalSched.

  Open Scope Sep_scope.

  Definition globalInv (fs : files) : HProp := Ex fr, globalSock =*> fr * [| fr %in fs |].
End M'''.

Ltac unf := unfold M'''.globalSched, M'''.globalInv in *.

Module T := Thread.Make(M''').

Import T M'''.
Export T M'''.

Definition hints : TacPackage.
  prepare (materialize_buffer, buffer_split_tagged) buffer_join_tagged.
Defined.

Ltac sep := T.sep unf hints.

Definition handlerS := SPEC reserving 49
  Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0.

Definition mainS := SPEC reserving 49
  PREmain[_] globalSched =?> 1 * globalSock =?> 1 * mallocHeap 0.

Definition writeSomeS := SPEC("fr", "buf", "len") reserving 36
  Al fs, Al len,
  PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 len * [| (wordToNat (V "len") <= len)%nat |]
    * sched fs * globalInv fs * mallocHeap 0
  POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 len * sched fs' * globalInv fs' * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS],
                           "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS], "scheduler"!"listen" @ [listenS],
                           "scheduler"!"accept" @ [acceptS], "scheduler"!"read" @ [readS],
                           "scheduler"!"write" @ [writeS], "scheduler"!"close" @ [closeS] ]]
  bmodule "test" {{
    bfunction "writeSome"("fr", "buf", "len") [writeSomeS]
      Assert [Al fs, Al len,
        PRE[V] [| V "fr" %in fs |] * buffer_splitAt (wordToNat (V "len")) (V "buf") len
          * [| (wordToNat (V "len") <= len)%nat |] * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * buffer_joinAt (wordToNat (V "len")) (V "buf") len
          * sched fs' * globalInv fs' * mallocHeap 0];;

      Call "scheduler"!"write"("fr", "buf", "len")
      [PRE[_] Emp POST[_] Emp];;
      Return 0
    end with bfunctionNoRet "handler"("buf", "fr", "n") [handlerS]
      "buf" <-- Call "malloc"!"malloc"(0, 10)
      [Al fs, PREmain[_, R] R =?> 10 * sched fs * globalInv fs * mallocHeap 0];;

      Note [please_materialize_buffer 10];;

      [Al fs, PREmain[V] V "buf" =?>8 40 * sched fs * globalInv fs * mallocHeap 0]
      While (0 = 0) {
        "fr" <-- Call "scheduler"!"accept"($[globalSock])
        [Al fs, PREmain[V, R] [| R %in fs |] * V "buf" =?>8 40 * sched fs * globalInv fs * mallocHeap 0];;

        "n" <-- Call "scheduler"!"read"("fr", "buf", 40)
        [Al fs, PREmain[V] [| V "fr" %in fs |] * V "buf" =?>8 40 * sched fs * globalInv fs * mallocHeap 0];;

        [Al fs, PREmain[V] [| V "fr" %in fs |] * V "buf" =?>8 40 * sched fs * globalInv fs * mallocHeap 0]
        While ("n" <> 0) {
          If ("n" <= 40) {
            Call "test"!"writeSome"("fr", "buf", "n")
            [Al fs, PREmain[V] [| V "fr" %in fs |] * V "buf" =?>8 40 * sched fs * globalInv fs * mallocHeap 0]
          } else {
            Skip
          };;

          "n" <-- Call "scheduler"!"read"("fr", "buf", 40)
          [Al fs, PREmain[V] [| V "fr" %in fs |] * V "buf" =?>8 40 * sched fs * globalInv fs * mallocHeap 0]
        }
      }
    end with bfunctionNoRet "main"("fr", "x") [mainS]
      Init
      [Al fs, Al v, PREmain[_] sched fs * globalSock =*> v * mallocHeap 0];;

      "fr" <-- Call "scheduler"!"listen"(8080%N)
      [Al fs, Al v, PREmain[_, R] [| R %in fs |] * sched fs * globalSock =*> v * mallocHeap 0];;

      globalSock *<- "fr";;

      Spawn("test"!"handler", 50)
      [Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0];;

      Spawn("test"!"handler", 50)
      [Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0];;

      Exit 50
    end
  }}.

Ltac t := sep; auto.

Opaque allocated.

(* Move to Thread *)
Hint Extern 1 (@eq W _ _) => words.

Lemma single_cell : forall p,
  (p =?> 1 = (Ex v, p =*> v) * Emp)%Sep.
  auto.
Qed.

Lemma le_40 : forall w : W,
  w <= natToW 40
  -> (wordToNat w <= 40)%nat.
  intros; pre_nomega.
  rewrite wordToNat_natToWord_idempotent in * by reflexivity; omega.
Qed.

Hint Immediate le_40.

Theorem ok : moduleOk m.
  vcgen.

  t.
  t.
  t.
  t.
  t.

  unf.
  post.
  evaluate hints.
  descend.
  step hints.
  step hints.
  step hints.
  descend.
  
  Ltac imply_simp'' := match goal with
                         | [ H : ex _ |- _ ] => destruct H
                         | [ H : _ /\ _ |- _ ] => destruct H
                         | [ |- interp _ (PropX.Inj _ ---> _) ] => apply injL; intro
                         | [ |- interp _ (PropX.Cptr _ _ ---> _) ] => apply cptrL; intro
                         | [ |- interp _ (PropX.And _ _ ---> _) ] => apply andL
                         | [ |- interp _ (PropX.Exists _ ---> _) ] => apply existsL; intro
                       end.

  repeat imply_simp''.
  descend.
  exBegone.
  step hints.
  step hints.
  step hints.
  descend; step hints.
  descend; step hints.
  descend; step hints.
  auto.
  step hints.
  step hints.

  t.
  t.
  t.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.

  post.
  evaluate hints.
  descend.
  match goal with
    | [ |- context[locals _ ?X _ _] ] => equate X (upd
                                      (upd (upd x2 "fr" (sel x1 "fr")) "buf"
                                         (sel x1 "buf")) "len" 
                                      (sel x1 "n"))
  end.
  descend.

  step hints.
  step hints.
  unfold localsInvariantMain.
  descend; step hints.
  descend; step hints.
  auto.
  step hints.

  t.
  t.
  t.
  t.

  t.
  t.
  t.

  rewrite (single_cell globalSock).

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
Qed.

End Make.
