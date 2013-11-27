Require Import AutoSep.
Require Import Semantics.

Set Implicit Arguments.

Definition Layout := W -> ADTValue -> HProp.

Variable is_heap : Layout -> Heap -> HProp.

Definition empty_vs : vals := fun _ => $0.

Section layout.

  Variable layout : Layout.

  Definition has_extra_stack sp offset :=
    (Ex stack,
     (sp ^+ $4) =*> stack *
     (sp ^+ $8 ^+ $(4 * offset)) =?> (wordToNat stack))%Sep.

  Definition is_state sp rp vars (v : State) temps : HProp :=
    (
     locals vars (fst v) 0 (sp ^+ $8) *
     array temps (sp ^+ $8 ^+ $(4 * length vars)) *
     is_heap layout (snd v) *
     sp =*> rp *
     has_extra_stack sp (length vars + length temps)
    )%Sep.

  Require Import Malloc.
  Require Import Safe.
  Require Import Basics.

  Definition decide_ret addr (ret : Ret) :=
    match ret with
      | inl w => (w, None)
      | inr a => (addr, Some a)
    end.

  Definition layout_option addr ret : HProp :=
    match ret with
      | None  => ([| True |])%Sep
      | Some a => layout addr a
    end.

  Definition heap_upd_option m k v :=
    match v with
      | Some x => heap_upd m k x
      | None => m
    end.

  Definition funcs_ok (stn : settings) (fs : W -> option Callee) : PropX W (settings * state) := 
    ((Al i, Al spec, 
      [| fs i = Some (Internal spec) |] 
        ---> (i, stn) @@@ (
          st ~> ExX, Ex v, Ex rp,
          ![^[is_state st#Sp rp (ArgVars spec) v nil * mallocHeap 0] * #0] st /\
          [| Safe fs (Body spec) v |] /\
          (st#Rp, stn) 
            @@@ (
              st' ~> Ex v', Ex rp',
              ![^[ is_state st'#Sp rp' (ArgVars spec) v' nil * mallocHeap 0] * #1] st' /\
              [| exists vs', 
                 RunsTo fs (Body spec) v (vs', snd v') /\ 
                 st'#Rv = sel vs' (RetVar spec) /\
                 st'#Sp = st#Sp |]))) /\
     (Al i, Al spec, 
      [| fs i = Some (Foreign spec) |] 
        ---> (i, stn) @@@ (
          st ~> ExX, Ex heap, Ex triples, Ex rp,
          ![^[is_state st#Sp rp nil (empty_vs, heap) (map Ptr triples) * mallocHeap 0] * #0] st /\
          [| List.Forall (fun x => heap_match heap (Ptr x, Semantics.In x)) triples /\
             PreCond spec (map Semantics.In triples) |] /\
          (st#Rp, stn) 
            @@@ (
              st' ~> Ex args', Ex heap', Ex addr, Ex ret, Ex rp',
              let t := decide_ret addr ret in
              let ret_w := fst t in
              let ret_a := snd t in
              ![^[is_state st#Sp rp' nil (empty_vs, heap') args' * layout_option addr ret_a * mallocHeap 0] * #1] st' /\
              [| PostCond spec (map (fun x => (Semantics.In x, Out x)) triples) ret /\
                 length args' = length triples /\
                 let heap := fold_left store_out triples heap in
                 let heap := heap_upd_option heap addr ret_a in
                 heap' = heap /\ 
                 st'#Rv = ret_w /\
                 st'#Sp = st#Sp |]))))%PropX.

  Section vars.

    Variable vars : list string.
    
    Variable temp_size : nat.

    Definition inv_template precond postcond : assert := 
      st ~> Ex fs, 
      funcs_ok (fst st) fs /\
      ExX, Ex v, Ex temps, Ex rp,
      ![^[is_state st#Sp rp vars v temps * mallocHeap 0] * #0] st /\
      [| precond fs v st /\
         length temps = temp_size |] /\
      (rp, fst st) 
        @@@ (
          st' ~> Ex v', Ex temps',
          ![^[is_state st'#Sp rp vars v' temps' * mallocHeap 0] * #1] st' /\
          [| postcond fs v st v' st' /\
             length temps' = temp_size |]).

    Definition inv s := 
      inv_template
        (fun fs v _ =>
           Safe fs s v)
        (fun fs v st v' st' =>
           RunsTo fs s v v' /\
           st'#Sp = st#Sp).
    
    End vars.

End layout.