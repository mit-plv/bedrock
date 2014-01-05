Require Import SyntaxFunc.
Require Import String.
Require Import Inv Malloc Semantics Safe.

Set Implicit Arguments.

Section TopSection.

  Variable func : Func.

  Definition is_state sp e_stack e_stack_real vars (v : State) : HProp :=
    (
     locals vars (fst v) 0 (sp ^+ $8) *
     is_heap (snd v) *
     sp =?> 1 *
     (sp ^+ $4) =*> $(e_stack) *
     (sp ^+ $8 ^+ $(4 * length vars)) =?> e_stack_real
    )%Sep.

  Definition inv vars s ret_var : assert := 
    st ~> Ex fs, 
    let stn := fst st in
    let env := (Labels stn, fs) in
    funcs_ok stn fs /\
    ExX, Ex v, Ex e_stack,
    ![^[is_state st#Sp e_stack e_stack vars v * mallocHeap 0] * #0] st /\
    [| Safe env s v |] /\
    (st#Rp, stn) 
      @@@ (
        st' ~> Ex v', Ex e_stack',
        ![^[is_state st'#Sp e_stack' e_stack vars v' * mallocHeap 0] * #1] st' /\
        [| RunsTo env s v v' /\
           st'#Sp = st#Sp /\
           st'#Rv = sel (fst v') ret_var |]).

  Definition spec := inv (SyntaxFunc.ArgVars func) (SyntaxFunc.Body func) (SyntaxFunc.RetVar func).

  Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

  Definition verifCond pre := imply pre spec :: nil.

End TopSection.