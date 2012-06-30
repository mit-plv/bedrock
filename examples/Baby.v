Require Import AutoSep.

(** * The simplest function *)

Definition diverger := bmodule "diverger" {{
  bfunction "diverger"() [SPEC reserving 0
    PRE[_] [| True |]
    POST[_] [| False |] ]
    Diverge
  end
}}.

(* Eval compute in compile diverger. *)

Theorem divergerOk : moduleOk diverger.
  vcgen; sep_auto.
Qed.

(* Print Assumptions divergerOk. *)


(** * Immediate return *)

Definition immedS : spec := SPEC reserving 0
  PRE[_] [| True |]
  POST[_] [| True |].

Definition immed := bmodule "immed" {{
  bfunction "immed"() [immedS]
    Return 0
  end
}}.

(* Eval compute in compile immed. *)

Theorem immedOk : moduleOk immed.
  vcgen; sep_auto.
Qed.

(* Print Assumptions immedOk. *)

Definition immedTest := bimport [[ "immed"!"immed" @ [immedS] ]]
  bmodule "main" {{
    bfunction "main"() [SPEC reserving 1
      PRE[_] [| True |]
      POST[_] [| False |] ]
      Call "immed"!"immed"
      [RET
        PRE[_] [| True |]
        POST[_] [| False |] ];;
      Diverge
    end
  }}.

(* Eval compute in compile immedTest. *)

Theorem immedTestOk : moduleOk immedTest.
  vcgen; (sep_auto; try words).

  (* Need to prove a theorem for switching from callee's to caller's view of stack. *)
  instantiate (1 := fun _ => [| True |]%PropX).
  admit.
Qed.

(* Print Assumptions immedTestOk. *)

Definition immedProg := link immed immedTest.

(* Eval compute in compile immedProg. *)

Theorem immedProgOk : moduleOk immedProg.
  link immedOk immedTestOk.
Qed.

(* Print Assumptions immedProgOk. *)


(** * Incrementer *)

Definition incS : spec := SPEC("x") reserving 0
  PRE[V] [| True |]
  POST[_, rv] [| rv = V "x" ^+ $1 |].

Definition inc := bmodule "inc" {{
  bfunction "inc"("x") [incS]
    Return "x" + 1
  end
}}.

(* Eval compute in compile inc. *)

Theorem incOk : moduleOk inc.
  vcgen; sep_auto.
Qed.


(** * Always-0, in a convoluted way *)

Definition always0S : spec := SPEC("x") reserving 0
  PRE[_] [| True |]
  POST[_, rv] [| rv = $0 |].

Definition always0 := bmodule "always0" {{
  bfunction "always0"("x") [always0S]
    If ("x" = 0) {
      Skip
    } else {
      "x" <- 0
    };;
    Return "x"
  end
}}.

(* Eval compute in compile always0. *)

Theorem always0Ok : moduleOk always0.
  vcgen; sep_auto.
Qed.
