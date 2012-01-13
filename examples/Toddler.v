Require Import Bedrock.


(** Always-0, in a convoluted way *)

Definition always0S : assert := st ~> st#Rp @@ (st' ~> [| st'#Rv = $0 |]).

Definition always0 := bmodule "always0" {{
  bfunction "always0" [always0S] {
    If (Rv = 0) {
      Skip
    } else {
      Rv <- 0
    };;
    Goto Rp
  }
}}.

Eval compute in compile always0.

Theorem always0Ok : moduleOk always0.
  structured; ho.
Qed.


(** Factorial! *)

Lemma separated_0_4 : separated 0 4.
  W_neq.
Qed.

Lemma separated_4_0 : separated 4 0.
  W_neq.
Qed.

Hint Resolve separated_0_4 separated_4_0.

Inductive factR : W -> W -> Prop :=
| FR0 : factR 0 1
| FRS : forall w r : W, w <> 0 -> factR (w ^- $1) r -> factR w (w ^* r).

Lemma FR0' : forall w : W, w = 0 -> factR w $1.
  intros; subst; apply FR0.
Qed.

Lemma FRS' : forall w r v : W, w <> 0 -> factR (w ^- $1) r -> v = w ^* r -> factR w v.
  intros; subst; eapply FRS; eauto.
Qed.

Hint Resolve FR0' FRS'.

Definition factS : assert := st ~> [| inBounds (fst st) 0 /\ inBounds (fst st) 4 |]
  /\ st#Rp @@ (st' ~> [| factR st#Rv st'#Rv |]).

Definition fact := bmodule "fact" {{
  bfunction "fact" [factS] {
    $[0] <- Rv;;
    $[4] <- 1;;

    [st ~> [| inBounds (fst st) 0 /\ inBounds (fst st) 4 |] /\ st#Rp @@ (st' ~> [| exists r, factR st.[0] r /\ st'#Rv = st.[4] ^* r |])]
    While ($[0] <> 0) {
      $[4] <- $[0] * $[4];;
      $[0] <- $[0] - 1
    };;

    Rv <- $[4];;
    Goto Rp
  }
}}.

Eval compute in compile fact.

Lemma times_1 : forall (n m x : W), factR n x
  -> m = $1 ^* x
  -> factR n m.
  intros; subst. replace ($1 ^* x) with x by W_eq. auto.
Qed.

Hint Resolve times_1.

Hint Extern 5 (@eq W ?X _) => match goal with
                                | [ H : X = _ |- _ ] => rewrite H; clear H; W_eq
                              end.

Hint Extern 5 (@eq W _ _) => match goal with
                               | [ |- ?G ] => has_evar G; fail 1
                               | _ => W_eq
                             end.

Theorem factOk : moduleOk fact.
  structured; (ho; eauto).
Qed.

Definition factDriver := bimport [[ "fact"!"fact" @ [factS] ]]
  bmodule "factDriver" {{
    bfunction "main" [st ~> [| inBounds (fst st) 0 /\ inBounds (fst st) 4 |]] {
      Rv <- 4;;
      Call "fact"!"fact"
      [st ~> [| st#Rv = 24 |] ];;
      Diverge
    }
  }}.

Theorem factR_4 : forall r, factR 4 r -> r = 24.
  intros; repeat match goal with
                   | [ H : factR _ _ |- _ ] => inversion H; clear H; subst; []
                 end;
  match goal with
    | [ H : factR _ _ |- _ ] => inversion H; clear H; subst; [ reflexivity
      | elimtype False; match goal with
                          | [ H : _ |- _ ] => apply H; reflexivity
                        end ]
  end.
Qed.  

Hint Resolve factR_4.

Theorem factDriverOk : moduleOk factDriver.
  structured; ho.
Qed.

Definition factProg := link fact factDriver.

Theorem factProgOk : moduleOk factProg.
  link factOk factDriverOk.
Qed.

Definition factSettings := leSettings (NToWord _ 1024) factProg.
Definition factProgram := snd (labelsOf (XCAP.Blocks factProg)).

Transparent natToWord.

Hint Extern 5 (inBounds _ _) => split; reflexivity.

Theorem factProgReallyOk : { w : _ | Labels factSettings ("factDriver", Global "main") = Some w
  /\ forall st, safe factSettings factProgram (w, st) }.
  withLabel; safety factProgOk ("factDriver", Global "main").
Defined.

Print Assumptions factProgReallyOk.

Definition final := Eval compute in exec factSettings factProgram 20
  (proj1_sig factProgReallyOk,
    {| Regs := fun _ => wzero _;
      Mem := fun _ => wzero _ |}).

Eval compute in match final with None => wzero _ | Some (_, final') => Regs final' Rv end.
