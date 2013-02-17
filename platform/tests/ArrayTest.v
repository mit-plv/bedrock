Require Import AutoSep.


Definition readS := SPEC("arr", "pos") reserving 0
  Al arr,
  PRE[V] array8 arr (V "arr") * [| V "pos" < $(length arr) |]
  POST[R] array8 arr (V "arr") * [| R = BtoW (Array8.sel arr (V "pos")) |].

Definition writeS := SPEC("arr", "pos", "val") reserving 0
  Al arr,
  PRE[V] array8 arr (V "arr") * [| V "pos" < $(length arr) |]
  POST[_] array8 (Array8.upd arr (V "pos") (WtoB (V "val"))) (V "arr").

Definition m := bmodule "array" {{
  bfunction "read"("arr", "pos") [readS]
    "arr" <-*8 "arr" + "pos";;
    Return "arr"
  end with bfunction "write"("arr", "pos", "val") [writeS]
    "arr" + "pos" *<-8 "val";;
    Return 0
  end
}}.

Theorem ok : moduleOk m.
  vcgen; abstract sep_auto.
Qed.
