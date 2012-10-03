Require Import Bedrock.


Import DefineStructured.

Section Wrap.
  Variable imports : LabelMap.t assert.
  Hypothesis imports_global : importsGlobal imports.
  Variable modName : string.

  Variable body : cmd imports modName.
  Variable postcondition : assert -> assert.
  Variable verifCond : assert -> list Prop.

  Hypothesis postcondition_ok : forall pre specs st,
    vcs (verifCond pre)
    -> interp specs ((body pre).(Postcondition) st)
    -> interp specs (postcondition pre st).

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
