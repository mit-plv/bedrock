Require Import PreAutoSep Wrap.


Fixpoint qspecStar (P : HProp) (Q : qspec) : qspec :=
  match Q with
    | Body P' => Body (P' * P)%Sep
    | Quant _ f => Quant (fun x => qspecStar P (f x))
  end.

Import DefineStructured.

Section For.
  Variables counter bound : string.
  (* Local variables for loop counter and upper bound. *)

  Variable body : chunk.
  Variable precondition : assert.

  Variable invariant : nat -> vals -> qspec.
  Variable postcondition : nat -> vals -> W -> qspec.

  Let For_' : chunk := (
    counter <- 0;;
    While_ (fun ns res st => Ex counterN : nat, Ex boundN : nat,
      localsInvariant
      (fun vs _ => qspecStar ([| vs counter = counterN |] * [| vs bound = boundN |])%Sep
        (invariant counterN vs))
      (fun vs _ r => postcondition counterN vs r)
      true (fun w => w) ns res st)%PropX
      (counter < bound)
      (body;; counter <- counter + 1)
  )%SP.

  Variable imports : LabelMap.t assert.
  Hypothesis imports_global : importsGlobal imports.
  Variable modName : string.

  Variable ns : list string.
  Variable res : nat.

  Let body' := toCmd body modName imports_global ns res.

  Opaque evalInstrs.

  Definition For_ : cmd imports modName.
    refine (Wrap _ imports_global modName
      (toCmd For_' modName imports_global ns res)
      (fun _ st => Ex boundN : nat,
        localsInvariant
        (fun vs _ => qspecStar ([| vs counter = boundN |] * [| vs bound = boundN |])%Sep
          (invariant boundN vs))
        (fun vs _ r => postcondition boundN vs r)
        true (fun w => w) ns res st)%PropX
      (fun pre =>
        let cout := body' (fun st => Ex boundN : nat,
          localsInvariant
          (fun vs _ => qspecStar ([| vs counter = boundN |] * [| vs bound = boundN |])%Sep
            (invariant boundN vs))
          (fun vs _ r => postcondition boundN vs r)
          true (fun w => w) ns res st)%PropX in
        (counter <> "rp")%type
        :: (bound <> "rp")%type
        :: In counter ns
        :: In bound ns
        :: (forall specs st, interp specs (pre st)
          -> interp specs (Ex boundN : nat,
            localsInvariant
            (fun vs _ => qspecStar ([| vs bound = boundN |])%Sep
              (invariant 0 (upd vs counter 0)))
            (fun vs _ r => postcondition 0 (upd vs counter 0) r)
            true (fun w => w) ns res st))%PropX
        :: (forall specs st, interp specs (cout.(Postcondition) st)
          -> interp specs (Ex counterN : nat, Ex boundN : nat,
            localsInvariant
            (fun vs _ => qspecStar ([| vs counter = counterN |] * [| vs bound = boundN |])%Sep
              (invariant counterN vs))
            (fun vs _ r => postcondition counterN vs r)
            true (fun w => w) ns res st))%PropX
        :: cout.(VerifCond))
      _ _).

    admit.

    simpl; intros.
    repeat match goal with
             | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; intros; subst
           end.
    repeat match goal with
             | [ |- vcs _ ] => constructor
           end; unfold immInR, variableSlot, lvalIn; simpl; intuition;
    try (generalize dependent body'; clear body'; intros;
      clear imports_global).

    apply H5 in H.
    propxFo.

    Lemma subst_qspecOut : forall A specs v q k,
      interp specs (subst (pc := W) (qspecOut (st := settings * state) (b := A :: nil) q k) v)
      -> interp specs (qspecOut q (fun P => subst (k P) v)).
      induction q; propxFo.
      apply H in H0; eauto.
    Qed.

    apply subst_qspecOut in H.

    Lemma qspecOut_qspecStar : forall specs P q k,
      interp specs (qspecOut (pc := W) (st := settings * state) (qspecStar P q) k)
      -> interp specs (qspecOut (pc := W) (st := settings * state) q (fun Q => k (Q * P)%Sep)).
      induction q; propxFo.
      apply H in H0; eauto.
    Qed.

    apply qspecOut_qspecStar in H.

    Lemma interp_qspecOut : forall specs q k,
      interp specs (qspecOut (pc := W) (st := settings * state) q k)
      -> exists Q, interp specs (k Q).
      induction q; propxFo; eauto.
    Qed.

    destruct (interp_qspecOut _ _ _ H).
    post.

    Lemma variablePosition_rp : forall v,
      v <> "rp"
      -> S (S (S (S (variablePosition ns v))))
      = variablePosition ("rp" :: ns) v.
      intros; unfold variablePosition at 2; fold variablePosition.
      destruct (string_dec "rp" v); intuition.
    Qed.

    rewrite variablePosition_rp in H0 by assumption.
    generalize (or_intror _ H3 : In _ ("rp" :: ns)); intro.
    generalize (or_intror _ H4 : In _ ("rp" :: ns)); intro.
    repeat match goal with
             | [ H : context[qspecOut] |- _ ] => clear H
             | [ H : vcs _ |- _ ] => clear H
           end.
    evaluate auto_ext.

    admit.

    propxFo.
    apply subst_qspecOut in H.
    apply qspecOut_qspecStar in H.
    destruct (interp_qspecOut _ _ _ H).    
    simpl in H7.
    autorewrite with sepFormula in H7.
    propxFo.
    repeat rewrite variablePosition_rp in H0 by assumption.
    clear H8.
    generalize (or_intror _ H3 : In _ ("rp" :: ns)); intro.
    generalize (or_intror _ H4 : In _ ("rp" :: ns)); intro.
    evaluate auto_ext.

    admit.

    admit.    
  Defined.

End For.
