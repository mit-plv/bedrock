Require Import AutoSep.


Inductive request :=
| Echo (_ : W)
| Add (_ _ : W).

Definition encode (req : request) : list W :=
  match req with
    | Echo w => $0 :: w :: nil
    | Add w1 w2 => $1 :: w1 :: w2 :: nil
  end.

Definition reply (req : request) : W :=
  match req with
    | Echo w => w
    | Add w1 w2 => w1 ^+ w2
  end.

Definition mainS := SPEC("req", "len") reserving 3
  Ex req,
  PRE[V] [| V "len" = length (encode req) |] * array (encode req) (V "req")
  POST[R] [| R = reply req |] * array (encode req) (V "req").

Definition m := bmodule "m" {{
  bfunction "main"("req", "len", "pos", "x", "y") [mainS]
    "pos" <- 0;;
    Match1 "req" Size "len" Position "pos" Pattern (0 ++ "x") {
      Diverge
    } else {
      Match1 "req" Size "len" Position "pos" Pattern (1 ++ "x" ++ "y") {
        Diverge
      } else {
        Diverge
      }
    }
  end
}}.

Theorem mOk : moduleOk m.
  vcgen; abstract (parse0; post; evaluate auto_ext; parse1; sep_auto; parse2).
Qed.
