Require Import Bedrock.

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

Definition factS : assert := st ~> ExX, Ex n0, Ex n4, ![ $0 =*> n0 * $4 =*> n4 * #0 ] st
  /\ st#Rp @@ (st' ~> [| factR st#Rv st'#Rv |]).

Definition fact := bmodule "fact" {{
  bfunction "fact" [factS] {
    $[0] <- Rv;;
    $[4] <- 1;;

    [st ~> ExX, Ex n0', Ex n4', ![ $0 =*> n0' * $4 =*> n4' * #0 ] st /\ st#Rp @@ (st' ~> Ex n0, Ex n4, Ex r, ![ $0 =*> n0 * $4 =*> n4 * #1 ] st' /\ [| factR n0 r /\ st'#Rv = n4 ^* r |])]
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
(* ezyang: This stopped working when we switched to partial memories. I assume this
is because the delicate tactics being used to prove the original can't carry through
the reasoning with options/partial memories. I will try to rewrite this so it works. *)
Admitted.

Definition factDriver := bimport [[ "fact"!"fact" @ [factS] ]]
  bmodule "factDriver" {{
    (* ezyang: Similarly, pre-condition probably not strong enough *)
    bfunction "main" [st ~> ExX, Ex n0, Ex n4, ![ $0 =*> n0 * $4 =*> n4 * #0 ] st] {
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
  (* ezyang: ... which is why this theorem fails *)
  structured; ho.
Admitted.

Definition factProg := link fact factDriver.

Theorem factProgOk : moduleOk factProg.
  link factOk factDriverOk.
Qed.

Definition factSettings := leSettings factProg.
Definition factProgram := snd (labelsOf (XCAP.Blocks factProg)).

Transparent natToWord.

Theorem factProgReallyOk : { w : _ | Labels factSettings ("factDriver", Global "main") = Some w
  /\ forall st, safe factSettings factProgram (w, st) }.
  (* withLabel; safety factProgOk ("factDriver", Global "main"). *)
  (* This started failing after we removed all of the inBounds statements *)
Admitted.

Print Assumptions factProgReallyOk.

Section final.
  Transparent evalInstrs.

(* ezyang: Started infinite looping after we removed inBounds checks
  Definition final := Eval compute in exec factSettings factProgram 20
    (proj1_sig factProgReallyOk,
      {| Regs := fun _ => wzero _;
        Mem := fun _ => Some (wzero _) |}).

  Eval compute in match final with None => wzero _ | Some (_, final') => Regs final' Rv end.
*)
End final.
