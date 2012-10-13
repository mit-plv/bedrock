Require Import AutoSep.


Fixpoint countNonzero (ws : list W) : nat :=
  match ws with
    | nil => O
    | w :: ws => if weq w $0 then countNonzero ws else S (countNonzero ws)
  end.

Definition mainS := SPEC("arr", "len") reserving 3
  Al arr,
  PRE[V] [| V "len" = length arr |] * array arr (V "arr")
  POST[R] [| R = countNonzero arr |] * array arr (V "arr").

Notation "[ 'After' ws 'Approaching' full 'PRE' [ V ] pre 'POST' [ R ] post ] 'For' index 'Holding' value 'in' arr 'Size' size 'Where' c { Body }" :=
  (ForArray arr size index value c%ArrayQuery (fun ws V => pre%qspec%Sep)
    (fun full V R => post%qspec%Sep) Body)
  (no associativity, at level 95, index at level 0, value at level 0, arr at level 0, size at level 0,
    c at level 0) : SP_scope.

Definition m := bmodule "m" {{
  bfunction "main"("arr", "len", "acc", "index", "value") [mainS]
    "acc" <- 0;;

    [After prefix Approaching all
      PRE[V] [| V "acc" = countNonzero prefix |]
      POST[R] [| R = countNonzero all |] ]
    For "index" Holding "value" in "arr" Size "len"
      Where (Value <> 0) {
      "acc" <- "acc" + 1
    };;

    Return "acc"
  end
}}.

Ltac for0 := try solve [ intuition (try congruence);
  repeat match goal with
           | [ H : forall x : string, _ |- _ ] => rewrite H by congruence
         end; reflexivity ].

Theorem mOk : moduleOk m.
  vcgen; for0.

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto; auto.
  admit.
  admit.
  sep_auto.
  sep_auto.
  sep_auto.
Qed.
