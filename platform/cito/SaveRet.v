Require Import AutoSep.

Set Implicit Arguments. 

Section TopLevel.

  Variable vars : list string.

  Variable var : option string.

  Definition is_state sp vs : HProp :=
    locals vars vs 0 (sp ^+ $8).

  Definition new_pre : assert := 
    x ~> ExX, Ex vs,
    ![^[is_state x#Sp vs] * #0]x.

  Require Import Semantics.

  Definition runs_to x_pre x := 
    forall specs other vs,
      interp specs (![is_state x_pre#Sp vs * other ] x_pre) ->
      Regs x Sp = x_pre#Sp /\
      interp specs (![is_state (Regs x Sp) (upd_option vs var x_pre#Rv) * other ] (fst x_pre, x)).

  Definition post (pre : assert) := 
    st ~> Ex st_pre, 
    pre (fst st, st_pre) /\
    [| runs_to (fst st, st_pre) (snd st) |].

  Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

  Definition in_scope := 
    match var with
      | Some x => List.In x vars
      | None => True
    end.

  Definition verifCond pre := imply pre new_pre :: in_scope :: nil.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Definition Strline := Straightline_ imports modName.

  Definition SaveRv lv := Strline (IL.Assign lv (RvLval (LvReg Rv)) :: nil).

  Definition vars_start := 4 * 2.
  Definition var_slot x := LvMem (Sp + (vars_start + variablePosition vars x)%nat)%loc.

  Definition Skip := Straightline_ imports modName nil.

  Definition body :=
    match var with
      | None => Skip
      | Some x => SaveRv (var_slot x)
    end.

  Require Import Wrap.

  Definition compile : cmd imports modName.
    refine (Wrap imports imports_global modName body post verifCond _ _).
    admit.
    admit.
 Defined.

End TopLevel.  


