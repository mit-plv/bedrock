Set Implicit Arguments.

Section TopSection.

  Require Import String.
  Variable module_name : string.

  Require Import SyntaxFunc.
  Variable func : Func.

  Require Import List.
  Require Import WellFormed.
  Record GoodFunc := 
    {
      NoDupVars : NoDup (ArgVars func ++ Vars func);
      WellFormed : wellformed (Body func)
    }.

  Hypothesis good_func : GoodFunc.

  Variable optimizer : Stmt -> Stmt.

  Definition GoodOptimizer : Prop.
    admit.
  Qed.

  Hypothesis good_optimizer : GoodOptimizer.

  Require Import Inv.
  Definition spec := Inv.inv (ArgVars func) 0 (SyntaxFunc.Body func).

  Section Body.

    Variable imports : LabelMap.t assert.

    Variable imports_global : importsGlobal imports.

    Definition stack_slot n := LvMem (Sp + (4 * n)%nat)%loc.

    Definition Seq2 := @Seq_ _ imports_global module_name.

    Definition Skip := Skip_ imports module_name.

    Fixpoint Seq ls :=
      match ls with
        | nil => Skip
        | a :: ls' => Seq2 a (Seq ls')
      end.

    Definition Strline := Straightline_ imports module_name.

    Definition CheckExtraStack (n : nat) cmd :=
      Seq2 
        (Strline (IL.Assign Rv (stack_slot 1) :: nil))
        (Structured.If_ imports_global n Le Rv cmd
                        (Diverge_ imports module_name)).

    Definition vars := ArgVars func ++ Vars func.

    Require Import Depth.
    Definition temp_size := depth (SyntaxFunc.Body func).

    Require CompileStmt.
    Definition compile_stmt s := CompileStmt.compile vars temp_size imports_global module_name s Syntax.Skip.

    Infix "/\" := cons : tmp_scope.
    Open Scope tmp_scope.
    Definition body' :=
      let stack_needed := length (Vars func) + temp_size in
      CheckExtraStack 
        stack_needed
        (Seq
           (Strline 
              (Binop (stack_slot 1) (stack_slot 1) Minus stack_needed /\
               Assign (stack_slot 0) Rp /\ nil) /\
            compile_stmt (optimizer (SyntaxFunc.Body func)) /\
            Strline 
              (Assign Rp (stack_slot 0) /\ nil) /\
            IGoto _ _ Rp /\ nil)).
    Close Scope tmp_scope.

    Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

    Definition verifCond pre := imply pre spec :: nil.

    Require Import Wrap.
    Definition body : cmd imports module_name.
      refine (
          Wrap imports imports_global module_name 
               body'
               (fun pre => Postcondition (body' pre))
               verifCond
               _ _).
      wrap0.
      unfold verifCond, imply; wrap0.
      eapply H2 in H.
      unfold spec in *.
      unfold inv in *.
      unfold inv_template in *.
      Opaque funcs_ok.
      post.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
    Defined.

  End Body.

  Require Import StructuredModule.
  Definition compile : function module_name :=
    (Name func, spec, body).

End TopSection.