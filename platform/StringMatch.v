Require Import AutoSep Ascii Wrap.

Definition W_of_ascii (ch : ascii) : W := N_of_ascii ch.
Coercion W_of_ascii : ascii >-> W.

(** Derived command to check whether a string matches a constant. *)


Section StringEq.
  Variables str len pos output : string.
  Variable const : string.

  Variable A : Type. (* Type for a single unified [Al] quantifier in the block spec *)
  Variable precondition : A -> vals -> HProp.
  Variable postcondition : A -> vals -> W -> HProp.

  Definition StringEqSpec :=
    Al bs, Al x : A,
    PRE[V] precondition x V * array8 bs (V str) * [| length bs = wordToNat (V len) |] * [| V pos <= V len |]
    POST[R] postcondition x V R.

  Fixpoint StringEq' (const : string) (offset : nat) : chunk :=
    match const with
      | "" => output <- 1
      | String ch const' =>
        Rp <- str + pos;;
        Rp <-*8 Rp + offset;;
        If (Rp = ch) {
          StringEq' const' (S offset)
        } else {
          output <- 0
        }
    end%SP.

  Lemma himp_refl : forall specs (P Q : HProp),
    P = Q
    -> himp specs P Q.
    intros; subst; reflexivity.
  Qed.

  Hint Extern 1 (himp _ _ _) =>
    try (apply himp_star_frame; try reflexivity);
    apply himp_refl;
      match goal with
        | [ H : _ |- _ ] => apply H
      end; intros; autorewrite with sepFormula; reflexivity.

  Lemma precondition_sel : forall a V, precondition a (sel V) = precondition a V.
    auto.
  Qed.

  Lemma postcondition_sel : forall a V, postcondition a (sel V) = postcondition a V.
    auto.
  Qed.

  Hint Rewrite precondition_sel postcondition_sel : sepFormula.

  Definition StringEq : chunk.
    refine (WrapC (StringEq' const O)
      StringEqSpec
      StringEqSpec
      (fun ns => (~In "rp" ns) :: In str ns :: In len ns :: In pos ns :: In output ns
        :: not (str = len) :: not (str = pos) :: not (str = output)
        :: not (len = pos) :: not (len = output)
        :: not (pos = output)
        :: (forall a V V',
          (forall x, x <> output -> sel V x = sel V' x)
          -> precondition a V = precondition a V')
        :: (forall a V V' r,
          (forall x, x <> output -> sel V x = sel V' x)
          -> postcondition a V r = postcondition a V' r)
        :: nil)
      _ _).

    wrap0; generalize dependent st; induction const.

    propxFo;
    match goal with
      | [ H : _, H' : _ |- _ ] => apply H in H'
    end; post; prep_locals; unfold immInR in *; clear_fancy; evaluate auto_ext;
    match goal with
      | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
    end;
    match goal with
      | [ st : (settings * state)%type |- _ ] => destruct st; simpl in *
    end; descend; repeat (step auto_ext; descend); descend.

    admit.

    admit.
  Defined.

End StringEq.
