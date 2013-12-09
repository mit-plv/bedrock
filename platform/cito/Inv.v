Require Import AutoSep.
Require Import Semantics.

Set Implicit Arguments.

Definition Layout := W -> ADTValue -> HProp.

Variable is_heap : Layout -> Heap -> HProp.

Definition empty_vs : vals := fun _ => $0.

Section layout.

  Variable layout : Layout.

  Definition has_extra_stack sp offset e_stack :=
    ((sp ^+ $4) =*> $(e_stack) *
     (sp ^+ $8 ^+ $(4 * offset)) =?> e_stack)%Sep.

  Definition is_state sp rp e_stack vars (v : State) temps : HProp :=
    (
     locals vars (fst v) 0 (sp ^+ $8) *
     array temps (sp ^+ $8 ^+ $(4 * length vars)) *
     is_heap layout (snd v) *
     sp =*> rp *
     has_extra_stack sp (length vars + length temps) e_stack
    )%Sep.

  Require Import Malloc.
  Require Import Safe.
  Require Import Basics.

  Definition layout_option addr ret : HProp :=
    match ret with
      | None  => ([| True |])%Sep
      | Some a => layout addr a
    end.

  Fixpoint make_triples pairs outs :=
    match pairs, outs with
      | p :: ps, o :: os => {| Word := fst p; ADTIn := snd p; ADTOut := o |} :: make_triples ps os
      | _, _ => nil
    end.

  Definition funcs_ok (stn : settings) (fs : W -> option Callee) : PropX W (settings * state) := 
    ((Al i, Al spec, 
      [| fs i = Some (Internal spec) |] 
        ---> (i, stn) @@@ (
          st ~> ExX, Ex v, Ex rp, Ex e_stack,
          ![^[is_state st#Sp rp e_stack (ArgVars spec) v nil * mallocHeap 0] * #0] st /\
          [| Safe fs (Body spec) v |] /\
          (st#Rp, stn) 
            @@@ (
              st' ~> Ex v', Ex rp',
              ![^[ is_state st'#Sp rp' e_stack (ArgVars spec) v' nil * mallocHeap 0] * #1] st' /\
              [| exists vs', 
                 RunsTo fs (Body spec) v (vs', snd v') /\ 
                 st'#Rv = sel vs' (RetVar spec) /\
                 st'#Sp = st#Sp |]))) /\
     (Al i, Al spec, 
      [| fs i = Some (Foreign spec) |] 
        ---> (i, stn) @@@ (
          st ~> ExX, Ex heap, Ex pairs, Ex rp, Ex e_stack,
          ![^[is_state st#Sp rp e_stack nil (empty_vs, heap) (map fst pairs) * mallocHeap 0] * #0] st /\
          [| List.Forall (heap_match heap) pairs /\
             PreCond spec (map snd pairs) |] /\
          (st#Rp, stn) 
            @@@ (
              st' ~> Ex args', Ex heap', Ex addr, Ex ret, Ex rp', Ex outs,
              let t := decide_ret addr ret in
              let ret_w := fst t in
              let ret_a := snd t in
              ![^[is_state st#Sp rp' e_stack nil (empty_vs, heap') args' * layout_option ret_w ret_a * mallocHeap 0] * #1] st' /\
              [| length outs = length pairs /\
                 let triples := make_triples pairs outs in
                 PostCond spec (map (fun x => (ADTIn x, ADTOut x)) triples) ret /\
                 length args' = length triples /\
                 let heap := fold_left store_out triples heap in
                 heap' = heap /\ 
                 st'#Rv = ret_w /\
                 st'#Sp = st#Sp |]))))%PropX.

  Section vars.

    Variable vars : list string.
    
    Variable temp_size : nat.

    Definition inv_template rv_precond s : assert := 
      st ~> Ex fs, 
      funcs_ok (fst st) fs /\
      ExX, Ex v, Ex temps, Ex rp, Ex e_stack,
      ![^[is_state st#Sp rp e_stack vars v temps * mallocHeap 0] * #0] st /\
      [| Safe fs s v /\
         length temps = temp_size /\
         rv_precond st#Rv v |] /\
      (rp, fst st) 
        @@@ (
          st' ~> Ex v', Ex temps',
          ![^[is_state st'#Sp rp e_stack vars v' temps' * mallocHeap 0] * #1] st' /\
          [| RunsTo fs s v v' /\
             length temps' = temp_size /\
             st'#Sp = st#Sp |]).

    Definition inv := inv_template (fun _ _ => True).
    
    End vars.

End layout.