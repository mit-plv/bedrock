Require Import AutoSep Malloc Arrays8.


Definition bmallocS : spec := SPEC("n") reserving 8
  PRE[V] [| V "n" >= $2 |] * mallocHeap 0
  POST[R] [| R <> 0 |] * [| freeable R (wordToNat (V "n")) |]
    * R =?>8 (wordToNat (V "n") * 4) * mallocHeap 0.

Definition bfreeS : spec := SPEC("p", "n") reserving 5
  PRE[V] [| V "p" <> 0 |] * [| freeable (V "p") (wordToNat (V "n")) |]
    * V "p" =?>8 (wordToNat (V "n") * 4) * mallocHeap 0
  POST[_] mallocHeap 0.

Definition ensureS : spec := SPEC("p", "len", "min") reserving 10
  PRE[V] V "p" =?>8 (wordToNat (V "len") * 4) * [| V "p" <> 0 |] * [| freeable (V "p") (wordToNat (V "len")) |]
    * mallocHeap 0
  POST[R] Ex len, R =?>8 (wordToNat len * 4) * [| len >= V "min" |] * [| R <> 0 |]
    * [| freeable R (wordToNat len) |] * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "buffers" {{
    bfunction "bmalloc"("n", "r") [bmallocS]
      "r" <-- Call "malloc"!"malloc"(0, "n")
      [PRE[_, R] Emp
       POST[R'] [| R' = R |] ];;
      Return "r"
    end with bfunction "bfree"("p", "n") [bfreeS]
      Assert [PRE[V] [| V "p" <> 0 |] * [| freeable (V "p") (wordToNat (V "n")) |]
        * V "p" =?> wordToNat (V "n") * mallocHeap 0
        POST[_] mallocHeap 0];;

      Call "malloc"!"free"(0, "p", "n")
      [PRE[_] Emp
       POST[_] Emp ];;
      Return 0
    end with bfunction "ensure"("p", "len", "min") [ensureS]
      If ("len" >= "min") {
        Return "p"
      } else {
        Call "buffers"!"bfree"("p", "len")
        [PRE[V] mallocHeap 0
         POST[R] Ex len, R =?>8 (wordToNat len * 4) * [| (len >= V "min")%word |] * [| R <> 0 |]
           * [| freeable R (wordToNat len) |] * mallocHeap 0];;

        [PRE[V] mallocHeap 0
         POST[R] Ex len, R =?>8 (wordToNat len * 4) * [| (len >= V "min")%word |] * [| R <> 0 |]
           * [| freeable R (wordToNat len) |] * mallocHeap 0]
        While ("len" < "min") {
          "len" <- "len" * 2
        };;

        If ("len" < 2) {
          "len" <- 2
        } else {
          Skip
        };;

        Assert [PRE[V] [| (V "len" >= $2)%word |] * [| (V "len" >= V "min")%word |] * mallocHeap 0
         POST[R] Ex len, R =?>8 (wordToNat len * 4) * [| (len >= V "min")%word |] * [| R <> 0 |]
           * [| freeable R (wordToNat len) |] * mallocHeap 0];;

        "p" <-- Call "buffers"!"bmalloc"("len")
        [PRE[_, R] Emp
         POST[R'] [| R' = R |] ];;
        Return "p"
      }
    end
  }}.

Theorem dematerialize_buffer : forall p n, p =?>8 (n * 4) ===> p =?> n.
  unfold buffer; sepLemma; apply decomission_array8; auto.
Qed.

Ltac finish :=
  repeat match goal with
           | [ H : _ = _ |- _ ] => rewrite H
         end; try apply materialize_array8;
  try (etransitivity; [ apply himp_star_comm | apply himp_star_frame; reflexivity || apply dematerialize_buffer ]);
    auto; try nomega.

Ltac t := sep_auto; finish.

Hint Extern 1 (@eq W _ _) => words.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.
