Require Import Bedrock.


(** The simplest function *)

Definition diverger := bmodule "diverger" {{
  bfunction "diverger" [st ~> [|True|] ] {
    Diverge
  }
}}.

Eval compute in compile diverger.

Theorem divergerOk : moduleOk diverger.
  structured.
Qed.

Print Assumptions divergerOk.

(** Asserts *)

Definition asserter := bmodule "asserter" {{
  bfunction "asserter" [st ~> [|True|] ] {
    Assert [ st ~> [|False|] ];;
    Diverge
  }
}}.

Theorem asserterOk : moduleOk asserter.
  structured.
Abort.

(** Immediate return *)

Definition immedS : assert := st ~> st#Rp @@ (st' ~> [| True |]).

Definition immed := bmodule "immed" {{
  bfunction "immed" [immedS] {
    Goto Rp
  }
}}.

Eval compute in compile immed.

Theorem immedOk : moduleOk immed.
  structured; ho.
Qed.

Print Assumptions immedOk.

Definition immedTest := bimport [[ "immed"!"immed" @ [immedS] ]]
  bmodule "main" {{
    bfunction "main" [st ~> [| True |] ] {
      Call "immed"!"immed"
      [st ~> [| True |] ];;
      Diverge
    }
  }}.

Eval compute in compile immedTest.

Theorem immedTestOk : moduleOk immedTest.
  structured; ho.
Qed.

Print Assumptions immedTestOk.

Definition immedProg := link immed immedTest.

Eval compute in compile immedProg.

Theorem immedProgOk : moduleOk immedProg.
  link immedOk immedTestOk.
Qed.

Print Assumptions immedProgOk.

Definition immedSettings := leSettings immedProg.
Definition immedProgram := snd (labelsOf (XCAP.Blocks immedProg)).

Theorem immedProgReallyOk : { w : _ | Labels immedSettings ("main", Global "main") = Some w
  /\ forall st, safe immedSettings immedProgram (w, st) }.
  withLabel; safety immedProgOk ("main", Global "main").
Defined.

Print Assumptions immedProgReallyOk.

Transparent natToWord.

Section final.
  Transparent evalInstrs.

  Definition final := Eval compute in exec immedSettings immedProgram 20
    (proj1_sig immedProgReallyOk,
      {| Regs := fun _ => wzero _;
        Mem := fun _ => Some (wzero _) |}).

  Eval compute in match final with None => wzero _ | Some (_, final') => Regs final' Rp end.
End final.


(** Stress testing [structured] performance *)

Definition stress := bmodule "stress" {{
  bfunction "stress" [st ~> [| True |] ] {
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Rp <- Rp;;
    Diverge
  }
}}.

Theorem stressOk : moduleOk stress.
  structured.
Qed.