Require Import Bedrock.


Import DefineStructured.

Section Lambda.
  Variable imports : LabelMap.t assert.
  Hypothesis imports_global : importsGlobal imports.
  Variable modName : string.

  Variable body : cmd imports modName.
  Variable precondition : assert.

  Hint Extern 1 (_ < _)%N => nomega.
  Hint Extern 1 (not (@eq LabelMap.key _ _)) => lomega.
  Hint Extern 1 (@eq LabelMap.key _ _ -> False) => lomega.
  Hint Extern 1 (LabelMap.MapsTo _ _ _) => apply imps_exit.

  Transparent evalInstrs.

  Definition Lambda : cmd imports modName.
    red; refine (fun pre =>
      let cout := body precondition in
      {|
        Postcondition := (fun st => Ex st',
        [| snd st = {| Regs := rupd st'.(Regs) Rv st#Rv;
          Mem := st'.(Mem) |} |]
        /\ pre (fst st, st')
        /\ Cptr st#Rv precondition)%PropX;
      VerifCond := (forall specs st, ~interp specs (cout.(Postcondition) st))
        :: cout.(VerifCond);
      Generate := fun Base Exit =>
        let cg := Generate cout (Nsucc (Nsucc Base)) Base in
        {|
          Entry := 1;
          Blocks := (cout.(Postcondition),
            (nil, Uncond (RvLabel (modName, Local Base))))
          :: (pre, (Assign Rv (RvLabel (modName,
            Local (Nsucc (Nsucc Base) + cg.(Entry)))) :: nil,
            Uncond (RvLabel (modName, Local Exit))))
          :: cg.(Blocks)
        |}
      |}); abstract (struct;
        repeat match goal with
                 | [ H : forall k v, _
                     |- context[match Labels _ ?k with None => _
                                  | _ => _ end] ] =>
                   edestruct (H k); eauto; intuition;
                     match goal with
                       | [ H : _ = _ |- _ ] => rewrite H
                     end
               end; repeat esplit; eauto; propxFo; eauto).
  Defined.

End Lambda.
