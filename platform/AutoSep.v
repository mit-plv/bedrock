Require Import PreAutoSep Util.
Export PreAutoSep Util.

Ltac enterFunction :=
  match goal with
    | [ |- context[localsInvariant _ _ false _ ?ns _ _] ] =>
      match goal with
        | [ |- context[localsInvariant _ _ true _ ?ns'' _ _] ] =>
          let ns' := peelPrefix ns ns'' in
            intros;
              repeat match goal with
                       | [ H : interp _ _ |- _ ] =>
                         eapply localsInvariant_inEx; [ | apply H ];
                           clear H; simpl; intros
                     end;
              eapply (@localsInvariant_in ns'); [
                eassumption
                | simpl; omega
                | reflexivity
                | reflexivity
                | repeat constructor; simpl; intuition congruence
                | intros ? ? Hrew; repeat rewrite Hrew by (simpl; tauto); reflexivity
                | intros ? ? Hrew; repeat rewrite Hrew by (simpl; tauto); reflexivity ]
      end
  end.

Ltac sep hints := enterFunction || PreAutoSep.sep hints.

Ltac sep_auto := sep auto_ext.
