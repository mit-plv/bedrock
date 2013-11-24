Require Import AutoSep.
Require Import Semantics.

Set Implicit Arguments.

Definition Layout := W -> ADTValue -> HProp.

Variable is_heap : Layout -> Heap -> HProp.

Definition agree_in a b := List.Forall (fun x => Locals.sel a x = Locals.sel b x).

Definition empty_vs : vals := fun _ => $0.

Section layout.

  Variable layout : Layout.

  Require Import ReservedNames.

  Definition is_state sp temp_vars temp_vs vars (v : State) : HProp :=
    (Ex stack, Ex vs,
     locals ("rp" :: STACK_CAPACITY :: vars ++ temp_vars) vs stack sp * 
     is_heap layout (snd v) * 
     [| agree_in vs temp_vs temp_vars /\ 
        stack = wordToNat (Locals.sel vs STACK_CAPACITY) |])%Sep.

  Require Import Malloc.
  Require Import Safe.
  Require Import Range.
  Require Import Basics.

  Infix "*" := compose : program_scope.
  Local Open Scope program_scope.

  Definition make_temp_vars := map temp_var * range0.

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
          st ~> ExX, Ex v,
          ![^[is_state st#Sp nil empty_vs (ArgVars spec) v * mallocHeap 0] * #0] st /\
          [| Safe fs (Body spec) v |] /\
          (st#Rp, stn) 
            @@@ (
              st' ~> Ex v',
              ![^[ is_state st'#Sp nil empty_vs (ArgVars spec) v' * mallocHeap 0] * #1] st' /\
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
          let vars := make_temp_vars (length triples) in
          ![^[is_state st#Sp nil empty_vs vars v * mallocHeap 0] * #0] st /\
          [| map (sel vs) vars = map Ptr triples /\
             List.Forall (fun x => heap_match heap (Ptr x, In x)) triples /\
             PreCond spec (map In triples) |] /\
          (st#Rp, stn) 
            @@@ (
              st' ~> Ex v', Ex addr, Ex ret,
              let t := decide_ret addr ret in
              let ret_w := fst t in
              let ret_a := snd t in
              let heap := fold_left store_out triples heap in
              let heap := heap_upd_option heap addr ret_a in
              ![^[is_state st#Sp nil empty_vs vars v' * layout_option addr ret_a * mallocHeap 0] * #1] st' /\
              [| snd v' = heap /\ 
                 PostCond spec (map (fun x => (In x, Out x)) triples) ret /\
                 st'#Rv = ret_w /\
                 st'#Sp = st#Sp |]))))%PropX.

  Definition inv temp_vars vars s : assert := 
    st ~> Ex fs, 
    funcs_ok (fst st) fs /\
    ExX, Ex v, Ex temp_vs,
    ![^[is_state st#Sp temp_vars temp_vs vars v * mallocHeap 0] * #0] st /\
    [| Safe fs s v |] /\
    (sel (fst v) "rp", fst st) 
      @@@ (
        st' ~> Ex v', Ex temp_vs',
        ![^[is_state st'#Sp temp_vars temp_vs' vars v * mallocHeap 0] * #1] st' /\
        [| RunsTo fs s v v' /\
           st'#Sp = st#Sp |]).

End layout.