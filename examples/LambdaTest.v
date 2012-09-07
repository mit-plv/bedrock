Require Import AutoSep.


(** * Always-0 *)

Definition always0S res : spec := SPEC reserving res
  PRE[_] Emp
  POST[R] [| R = 0 |].

Definition always0 := bmodule "always0" {{
  bfunction "main"("f") [always0S 2]
    "f" <-- Lambda() [always0S 0]
      Return 0
    end;;

    "f" <-- ICall "f"()
    [PRE[_, R] [| R = 0 |]
     POST[R'] [| R' = 0 |] ];;
    Return "f"
  end
}}.

Hint Extern 1 (@eq W _ _) => words.

Theorem always0Ok : moduleOk always0.
  vcgen; abstract (post; try icall (@nil string); (sep_auto; auto)).
Qed.
