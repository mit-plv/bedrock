Require Import AutoSep.
Require Import Semantics.

Set Implicit Arguments.

Definition Layout := W -> ADTValue -> HProp.

Variable is_heap : Layout -> Heap -> HProp.

Definition empty_vs : vals := fun _ => $0.

Section layout.

  Variable layout : Layout.

  Require Import ReservedNames.
  Require Import ValsStringList.

  Definition is_state sp vars (v : State) temp_vars temp_vs : HProp :=
    (Ex stack, Ex vs,
     locals ("rp" :: STACK_CAPACITY :: vars ++ temp_vars) vs stack sp * 
     is_heap layout (snd v) * 
     [| agree_in vs temp_vs temp_vars /\ 
        agree_in vs (fst v) vars /\
        stack = wordToNat (Locals.sel vs STACK_CAPACITY) |])%Sep.

  Require Import Malloc.
  Require Import Safe.
  Require Import Basics.
  Require Import TempNamesList.

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

  Definition empty := @nil string.

  Definition funcs_ok (stn : settings) (fs : W -> option Callee) : PropX W (settings * state) := 
    ((Al i, Al spec, 
      [| fs i = Some (Internal spec) |] 
        ---> (i, stn) @@@ (
          st ~> ExX, Ex v,
          ![^[is_state st#Sp (ArgVars spec) v empty empty_vs * mallocHeap 0] * #0] st /\
          [| Safe fs (Body spec) v |] /\
          (st#Rp, stn) 
            @@@ (
              st' ~> Ex v',
              ![^[ is_state st'#Sp (ArgVars spec) v' empty empty_vs * mallocHeap 0] * #1] st' /\
              [| exists vs', 
                 RunsTo fs (Body spec) v (vs', snd v') /\ 
                 st'#Rv = sel vs' (RetVar spec) /\
                 st'#Sp = st#Sp |]))) /\
     (Al i, Al spec, 
      [| fs i = Some (Foreign spec) |] 
        ---> (i, stn) @@@ (
          st ~> ExX, Ex v, Ex triples,
          let vs := fst v in
          let heap := snd v in
          let vars := make_temp_names_list (length triples) in
          ![^[is_state st#Sp vars v empty empty_vs * mallocHeap 0] * #0] st /\
          [| map (sel vs) vars = map Ptr triples /\
             List.Forall (fun x => heap_match heap (Ptr x, Semantics.In x)) triples /\
             PreCond spec (map Semantics.In triples) |] /\
          (st#Rp, stn) 
            @@@ (
              st' ~> Ex v', Ex addr, Ex ret,
              let t := decide_ret addr ret in
              let ret_w := fst t in
              let ret_a := snd t in
              let heap := fold_left store_out triples heap in
              let heap := heap_upd_option heap addr ret_a in
              ![^[is_state st#Sp vars v' empty empty_vs * layout_option addr ret_a * mallocHeap 0] * #1] st' /\
              [| snd v' = heap /\ 
                 PostCond spec (map (fun x => (Semantics.In x, Out x)) triples) ret /\
                 st'#Rv = ret_w /\
                 st'#Sp = st#Sp |]))))%PropX.

  Section vars.

    Variable vars temp_vars : list string.

    Definition inv_template precond postcond : assert := 
      st ~> Ex fs, 
      funcs_ok (fst st) fs /\
      ExX, Ex v, Ex temp_vs,
      ![^[is_state st#Sp vars v temp_vars temp_vs * mallocHeap 0] * #0] st /\
      [| precond fs v st |] /\
      (sel (fst v) "rp", fst st) 
        @@@ (
          st' ~> Ex v', Ex temp_vs',
          ![^[is_state st'#Sp vars v' temp_vars temp_vs' * mallocHeap 0] * #1] st' /\
          [| postcond fs v st v' st' |]).

    Definition inv s := 
      inv_template
        (fun fs v _ =>
           Safe fs s v)
        (fun fs v st v' st' =>
           RunsTo fs s v v' /\
           st'#Sp = st#Sp).
    
    End vars.

End layout.