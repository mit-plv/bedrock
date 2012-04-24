Require Import AutoSep.

(** Swapping two pointers *)

Definition getArg (n : nat) :=
  $[Sp + $(4 * n)]%SP.

(* "Uh, argument conventions"
    - Grows up
    - All values stored on stack must be W size
*)

Fixpoint args {sos} (vs : list W) (vend : W) (offset : nat) (st : settings * state) : hpropB sos :=
  match vs with
    | nil => ((st#Sp ^+ natToWord 32 offset) =*> vend)%Sep
    | v :: vs' => (args vs' vend (offset + 4) st * (st#Sp ^+ natToWord 32 offset) =*> v)%Sep
  end.

Definition swapS : assert := st ~> ExX, Ex v, Ex v', ![ args (v :: nil) v' 0 st * #0 ] st
  /\ st#Rp @@ (st' ~> [| st#Sp = st'#Sp |] /\ ![ args (v' :: nil) v 0 st * #1 ] st').

Definition swap := bmodule "swap" {{
  bfunction "swap" [swapS] {
    Rv <- getArg 1;;
    getArg 1 <- getArg 0;;
    getArg 0 <- Rv;;
    Goto Rp
  }
}}.

Theorem swapOk : moduleOk swap.
  vcgen; repeat cbv beta iota zeta delta [ getArg ] in *; simpl in *; 
    abstract sep_auto.
Qed.
