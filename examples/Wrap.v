Require Import Bedrock.


Import DefineStructured.

Section Wrap.
  Variable imports : LabelMap.t assert.
  Hypothesis imports_global : importsGlobal imports.
  Variable modName : string.

  Variable body : cmd imports modName.
  Variable postcondition : assert -> assert.
  Variable verifCond : assert -> list Prop.

  Hypothesis postcondition_ok : forall pre specs x,
    vcs (verifCond pre)
    -> interp specs ((body pre).(Postcondition) x)
    -> interp specs (postcondition pre x).

  Hypothesis verifCond_ok : forall pre,
    vcs (verifCond pre)
    -> vcs (body pre).(VerifCond).

  Hint Extern 1 (_ < _)%N => nomega.
  Hint Extern 1 (not (@eq LabelMap.key _ _)) => lomega.
  Hint Extern 1 (@eq LabelMap.key _ _ -> False) => lomega.
  Hint Extern 1 (LabelMap.MapsTo _ _ _) => apply imps_exit.

  Transparent evalInstrs.

  Definition Wrap : cmd imports modName.
    red; refine (fun pre =>
      let cout := body pre in
      {|
        Postcondition := postcondition pre;
        VerifCond := verifCond pre;
        Generate := fun Base Exit =>
        let cg := cout.(Generate) (Nsucc Base) Base in
          {|
            Entry := Nsucc cg.(Entry);
            Blocks := (cout.(Postcondition),
              (nil, Uncond (RvLabel (modName, Local Exit))))
            :: cg.(Blocks)
          |}
      |}); abstract (struct;
        match goal with
          | [ H : forall k' : LabelMap.key, _
              |- context[Labels _ ?k]  ] =>
            edestruct (H k) as [ ? [ ] ]; eauto;
              match goal with
                | [ H : _ = _ |- _ ] => solve [ rewrite H; eauto 6 ]
              end
          | [ |- context[LabelMap.add (_, Local ?Base) _ _] ] =>
            assert (Base < N.succ Base)%N by nomega;
              match goal with
                | [ H : vcs _ |- _ ] => apply verifCond_ok in H
              end; intuition struct
        end).
  Defined.

End Wrap.


(** * Some tactics useful in clients of [Wrap] *)

Require Import Locals.

Lemma four_plus_variablePosition : forall x ns',
  ~In "rp" ns'
  -> In x ns'
  -> 4 + variablePosition ns' x = variablePosition ("rp" :: ns') x.
  unfold variablePosition at 2; intros.
  destruct (string_dec "rp" x); auto; subst; tauto.
Qed.

Ltac prep_locals :=
  unfold variableSlot in *; repeat rewrite four_plus_variablePosition in * by assumption;
    repeat match goal with
             | [ H : In ?X ?ls |- _ ] =>
               match ls with
                 | "rp" :: _ => fail 1
                 | _ =>
                   match goal with
                     | [ _ : In X ("rp" :: ls) |- _ ] => fail 1
                     | _ => assert (In X ("rp" :: ls)) by (simpl; tauto)
                   end
               end
           end.

Ltac clear_fancy := repeat match goal with
                             | [ H : importsGlobal _ |- _ ] => clear H
                             | [ H : vcs _ |- _ ] => clear H
                           end.

Ltac wrap0 :=
  intros;
    repeat match goal with
             | [ H : vcs nil |- _ ] => clear H
             | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; intros; subst
             | [ H : vcs (_ ++ _) |- _ ] => specialize (vcs_app_bwd1 _ _ H);
               specialize (vcs_app_bwd2 _ _ H); clear H; intros
           end; simpl;
    repeat match goal with
             | [ |- vcs nil ] => constructor
             | [ |- vcs (_ :: _) ] => constructor
             | [ |- vcs (_ ++ _) ] => apply vcs_app_fwd
           end; propxFo;
    try match goal with
          | [ H : forall stn : settings, _, H' : interp _ _ |- _ ] =>
            specialize (H _ _ _ H')
        end.

Ltac wrap1 := prep_locals; auto; clear_fancy.
