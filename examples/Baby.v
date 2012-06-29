Require Import AutoSep.

(** * The simplest function *)

Definition diverger := bmodule "diverger" {{
  bfunction "diverger" [SPEC reserving 0
    PRE[_] [| True |]
    POST[_] [| False |] ]
  reserving 0 {
    Diverge
  }
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
  bfunction "immed" [immedS]
  reserving 0 {
    Return 0
  }
}}.

(* Eval compute in compile immed. *)

Theorem immedOk : moduleOk immed.
  vcgen; sep_auto.
Qed.

(* Print Assumptions immedOk. *)

Definition immedTest := bimport [[ "immed"!"immed" @ [immedS] ]]
  bmodule "main" {{
    bfunction "main" [SPEC reserving 1
      PRE[_] [| True |]
      POST[_] [| False |] ]
    reserving 0 {
      Call "immed"!"immed"
      [INV
        PRE[_] [| True |]
        POST[_] [| False |] ];;
      Diverge
    }
  }}.

(* Eval compute in compile immedTest. *)

Theorem immedTestOk : moduleOk immedTest.
  vcgen.

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  
Regs st Sp = Regs x Sp ^+ 4
  H1 : Regs st Rp = Regs x Rp
  H5 : Regs st Rv = Regs x Rv
  H6 : interp specs
         (![SEP.ST.star (fun (st : ST.settings) (m : smem) => x0 (st, m))
              (SEP.ST.star (locals ("rp" :: nil) x1 1 (Regs x Sp))
                 (SEP.ST.inj [|True|]))] (stn, st))
  H7 : True
  H8 : True
  H2 : True
  ============================
   himp specs
     ((fun (st0 : ST.settings) (m : smem) => x0 (st0, m)) *
      locals ("rp" :: nil) x1 1 (Regs x Sp))%Sep
     (SEP.ST.star (fun (stn0 : ST.settings) (sm : smem) => ?55543 (stn0, sm))
        (locals ("rp" :: nil) ?44877 0 (Regs st Sp)))

  
  

  vcgen; sep_auto.
Qed.

(* Print Assumptions immedTestOk. *)

Definition immedProg := link immed immedTest.

(* Eval compute in compile immedProg. *)

Theorem immedProgOk : moduleOk immedProg.
  link immedOk immedTestOk.
Qed.

(* Print Assumptions immedProgOk. *)

Definition immedSettings := leSettings immedProg.
Definition immedProgram := snd (labelsOf (XCAP.Blocks immedProg)).

Theorem immedProgReallyOk : { w : _ | Labels immedSettings ("main", Global "main") = Some w
  /\ forall st, safe immedSettings immedProgram (w, st) }.
  withLabel; safety immedProgOk ("main", Global "main").
Defined.

(* Print Assumptions immedProgReallyOk. *)

Transparent natToWord.

Section final.
  Transparent evalInstrs.

  Definition final := Eval compute in exec immedSettings immedProgram 20
    (proj1_sig immedProgReallyOk,
      {| Regs := fun _ => wzero _;
        Mem := fun _ => Some (wzero _) |}).

(*   Eval compute in match final with None => wzero _ | Some (_, final') => Regs final' Rp end.
*)
End final.


(** * Always-0, in a convoluted way *)

Definition always0S : assert := SPEC reserving 0
  PRE[_] [| True |]
  POST[_, rv] [| rv = $0 |].

Definition always0 := bmodule "always0" {{
  bfunction "always0" [always0S]
  reserving 0 {
    If (Rv = 0) {
      Skip
    } else {
      Rv <- 0
    };;
    Return Rv
  }
}}.

(* Eval compute in compile always0. *)

Theorem always0Ok : moduleOk always0.
  vcgen; sep_auto.
Qed.
