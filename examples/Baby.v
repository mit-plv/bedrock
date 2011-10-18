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
