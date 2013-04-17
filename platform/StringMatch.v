Require Import AutoSep Ascii Wrap.

Set Implicit Arguments.

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
        Rp <- pos + offset;;
        Rp <-*8 str + Rp;;
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

  Definition StringEqSpec' (offset : nat) :=
    Al bs, Al x : A,
    PRE[V] precondition x V * array8 bs (V str) * [| length bs = wordToNat (V len) |]
      * [| V pos ^+ natToW offset < V len |]
    POST[R] postcondition x V R.

  Ltac app := match goal with
                | [ H : _, H' : _ |- _ ] => apply H in H'
              end.

  Ltac handle_IH :=
    try match goal with
          | [ H : importsGlobal _ |- _ ] =>
            match goal with
              | [ IH : context[H] |- _ ] => clear H IH
            end
        end.

  Ltac simp := post; unfold lvalIn, regInL, immInR in *; clear_fancy; prep_locals.

  Lemma bound_switch : forall (u v : W) n,
    u < v
    -> n = wordToNat v
    -> u < natToW n.
    intros; subst; unfold natToW; rewrite natToWord_wordToNat; auto.
  Qed.
  
  Ltac evalu :=
    repeat match goal with
             | [ H : evalInstrs _ _ _ = _ |- _ ] => generalize dependent H
           end;
    evaluate auto_ext; intros;
    try match goal with
          | [ H : length _ = wordToNat _, H' : _ < _ |- _ ] => specialize (bound_switch H' H); intro
        end;
    evaluate auto_ext; intros;
    repeat match goal with
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
           end.

  Ltac finish := descend; repeat (step auto_ext; descend); descend; step auto_ext.

  Ltac t := app; simp; handle_IH; evalu; finish.

  Notation StringEqVcs := (fun ns => (~In "rp" ns) :: In str ns :: In len ns :: In pos ns :: In output ns
    :: not (str = len) :: not (str = pos) :: not (str = output)
    :: not (len = pos) :: not (len = output)
    :: not (pos = output)
    :: (forall a V V',
      (forall x, x <> output -> sel V x = sel V' x)
      -> precondition a V = precondition a V')
    :: (forall a V V' r,
      (forall x, x <> output -> sel V x = sel V' x)
      -> postcondition a V r = postcondition a V' r)
    :: nil).

  Definition StringEq'' (offset : nat) : chunk.
    refine (WrapC (StringEq' const offset)
      (StringEqSpec' offset)
      (StringEqSpec' offset)
      StringEqVcs
      _ _).

    wrap0; generalize dependent offset; generalize dependent st; induction const.

    propxFo; t.

    propxFo.
    
    admit. (* Recursive case *)

    t.

    admit.
  Defined.

  Definition StringEq : chunk.
    refine (WrapC (StringEq'' O)
      StringEqSpec
      StringEqSpec
      StringEqVcs
      _ _).

    wrap0.
    clear H.
    post; descend; repeat (step auto_ext; descend).
    replace (sel x2 pos ^+ natToW 0) with (sel x2 pos) in H1.
    auto.
    words.

    wrap0.
    admit.
  Defined.

End StringEq.
