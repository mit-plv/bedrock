Require Import AutoSep.

(** Factorial is mandatory, isn't it? *)

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
  /\ st#Rp @@ (st' ~> [| factR st#Rv st'#Rv |] /\ Ex n0', Ex n4', ![ $0 =*> n0' * $4 =*> n4' * #1 ] st').

Definition fact := bmodule "fact" {{
  bfunction "fact" [factS] {
    $[0] <- Rv;;
    $[4] <- 1;;

    [st ~> ExX, Ex inp, Ex acc, ![ $0 =*> inp * $4 =*> acc * #0 ] st
      /\ st#Rp @@ (st' ~> Ex n0, Ex n4, ![ $0 =*> n0 * $4 =*> n4 * #1 ] st' /\ [| exists r, factR inp r /\ st'#Rv = acc ^* r |])]
    While ($[0] <> 0) {
      $[4] <- $[0] * $[4];;
      $[0] <- $[0] - 1
    };;

    Rv <- $[4];;
    Goto Rp
  }
}}.

Lemma times_1 : forall (n m x : W), factR n x
  -> m = $1 ^* x
  -> factR n m.
  intros; subst. replace ($1 ^* x) with x by W_eq. auto.
Qed.

Hint Resolve times_1.

Hint Extern 5 (@eq W ?X _) => match goal with
                                | [ H : X = _ |- _ ] =>
                                  let T := type of H in
                                    (has_evar T; fail 1)
                                    || (rewrite H; clear H; W_eq)
                              end.

Hint Extern 5 (@eq W _ _) => match goal with
                               | [ |- ?G ] => has_evar G; fail 1
                               | _ => W_eq
                             end.

Theorem factOk : moduleOk fact.
  vcgen; abstract (sep_auto; eauto).
Qed.

Definition factDriver := bimport [[ "fact"!"fact" @ [factS] ]]
  bmodule "factDriver" {{
    bfunction "main" [st ~> ExX, Ex n0, Ex n4, ![ $0 =*> n0 * $4 =*> n4 * #0 ] st] {
      Rv <- 4;;
      Call "fact"!"fact"
      [st ~> [| st#Rv = 24 |] ];;
      Diverge
    }
  }}.

Theorem factR_4 : forall inp r, factR inp r -> inp = 4 -> r = 24.
  intros; subst;
    repeat match goal with
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
  vcgen; abstract (sep_auto; eauto).
Qed.

Definition factProg := link fact factDriver.

Theorem factProgOk : moduleOk factProg.
  link factOk factDriverOk.
Qed.
