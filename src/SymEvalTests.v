Require Import List DepList.
Require Import Heaps.
Require Import Expr SepExpr SymEval.

Module EvaluatorTests (B : Heap) (ST : SepTheoryX.SepTheoryXType B).
  Module Import SE := Evaluator B ST.

  Section Tests.
    Variable a b : Type.

    Variable ptsto32 : B.addr -> W -> ST.hprop a b nil.

    Ltac isConst e :=
      match e with
        | true => true
        | false => true
        | O => true
        | S ?e => isConst e
        | _ => false
      end.

    Definition addr_type : Expr.type :=
      {| Expr.Impl := B.addr 
       ; Expr.Eq := fun x y => match B.addr_dec x y with
                                 | left pf => Some pf
                                 | right _ => None
                               end
       |} .

    Definition W_type : Expr.type :=
      {| Expr.Impl := W
       ; Expr.Eq := fun x y => match equiv_dec x y with
                                 | left pf => Some pf
                                 | right _ => None
                               end
       |}.

    Definition a_type : Expr.type :=
      {| Expr.Impl := a 
       ; Eq := fun _ _ => None
       |}.   
    Definition b_type : Expr.type :=
      {| Expr.Impl := b
       ; Eq := fun _ _ => None
       |}.

    Require Import Word.

    Definition pre_types : list Expr.type := 
      a_type :: b_type :: addr_type :: W_type :: nil.

    (** I need to universally quantify SymEval_word over the functions list
     **
     **)

    Definition funcs : functions (wtypes pre_types 2 3) := nil.

    Definition sfuncs : list (SEP.ssignature (wtypes pre_types 2 3) (tvType 0) (tvType 1)) :=
      {| SDomain := tvType 2 :: tvType 3 :: nil
       ; SDenotation := ptsto32 : functionTypeD
         (map (tvarD (wtypes pre_types 2 3)) (tvType 2 :: tvType 3 :: nil))
         (ST.hprop (tvarD (wtypes pre_types 2 3) (tvType 0))
           (tvarD (wtypes pre_types 2 3) (tvType 1)) nil)
       |} :: nil.
    
    Definition Satisfies cs stn (P : ST.hprop a b nil) m : Prop :=
      exists sm, 
          ST.satisfies cs P stn sm
       /\ ST.HT.satisfies sm m.

    Theorem addr_not_state : 3 <> 2.
      clear; auto.
    Qed.

    Definition known : list nat := 0 :: nil.

    Definition evaluators : DepList.hlist (fun n : nat => match nth_error sfuncs n with
                                                            | None => Empty_set 
                                                            | Some ss => 
                                                              SymEval_word pre_types addr_not_state
                                                                funcs
                                                                (pcIndex := 0) (stateIndex := 1) ss
                                                          end) known.
      refine (DepList.HCons _ DepList.HNil); simpl.
      refine (
        {| sym_read_word := fun _ args p => 
           match args with
             | p' :: v :: nil => 
               if seq_dec p p' then Some v else None
             | _ => None
           end
         ; sym_write_word := fun _ args p v =>
           match args with
             | p' :: v' :: nil => 
               if seq_dec p p' then Some (p' :: v :: nil) else None
             | _ => None
           end
         ; sym_read_word_correct := _
         ; sym_write_word_correct := _
         |}).
      admit.
      admit.
    Defined.

    Ltac lift_evaluator_w e nt nf :=
      let r := eval simpl sym_read_word in (sym_read_word e) in
      let w := eval simpl sym_write_word in (sym_write_word e) in
      let rc := eval simpl sym_read_word_correct in (sym_read_word_correct e) in
      let wc := eval simpl sym_write_word_correct in (sym_write_word_correct e) in
      match type of e with
        | SymEval_word _ ?stI ?pcI ?ptrI ?wI ?pf _ ?s =>
          match SE.SEP.lift_ssignatures (s :: nil) nt with
            | ?s' :: nil =>
              constr:(@Build_SymEval_word nt stI pcI ptrI wI pf nf s' r w rc wc)
          end
      end.

    Ltac lift_evaluators_w es nt nf ns :=
      let rec lift es :=
        match es with
          | @DepList.HNil _ (fun n : nat => 
            match nth_error _ n with
              | None => Empty_set
              | Some ss => @SymEval_word _ ?stI ?pcI ?ptrI ?wI ?pf _ _ 
            end) =>
            let k := 
              constr:(@DepList.HNil nat (fun n : nat =>
                match nth_error ns n with
                  | None => Empty_set
                  | Some ss => @SymEval_word nt stI pcI ptrI wI pf nf ss
                end))
            in k 
          | @DepList.HCons _ (fun n : nat => 
            match nth_error _ n with
              | None => Empty_set
              | Some ss => @SymEval_word _ ?stI ?pcI ?ptrI ?wI ?pf _ _ 
            end) ?f ?ls ?e ?es =>
          idtac "ok" ;
            let es := lift es in
              idtac "here" e ;
            let e := lift_evaluator_w e nt nf in
              idtac "got here " ;
            constr:(@DepList.HCons _ (fun n : nat =>
                match nth_error ns n with
                  | None => Empty_set
                  | Some ss => @SymEval_word nt stI pcI ptrI wI pf nf ss
                end) f ls e es)
        end
      in
      lift es.

    Goal True.
      Set Printing Implicit.
      match goal with
        | [ |- _ ] => 
          let z := eval unfold evaluators in evaluators in
            idtac "foo" z ;
          let r := lift_evaluators_w z pre_types funcs sfuncs in
            idtac "here" ;
            idtac r
      end.

            constr:(@DepList.HNil nat (fun n : nat => 
              match nth_error sfuncs n with
                | None => Empty_set 
                | Some ss => 
                  SymEval_word nt addr_not_state
                  funcs
                  (pcIndex := 0) (stateIndex := 1) ss
              end) nil)
(*
    Goal forall p1 p2 p3 v1 v2 v3 cs stn m,
      Satisfies cs stn (ST.star (ptsto32 p1 v1) (ST.star (ptsto32 p2 v2) (ptsto32 p3 v3))) m
      -> mem_get_word B.addr B.mem B.footprint_w B.mem_get (IL.implode stn) p1 m = Some v1.
    Proof.
      intros.
      match goal with
        | [ H : Satisfies ?CS ?STN ?P ?M
          |- context [ mem_get_word B.addr B.mem B.footprint_w B.mem_get (IL.implode stn) ?PTR ?M ] ] =>
        let Ts := constr:(@nil Type) in
        let Ts := SEP.collectAllTypes_sexpr ltac:(isConst) Ts (P :: nil) in
        let Ts := SEP.collectAllTypes_expr ltac:(isConst) Ts (PTR, tt) in
        let types := eval unfold pre_types in pre_types in
        let types := SEP.extend_all_types Ts types in
        let sexprs := constr:(P :: nil) in
        match SEP.reify_sexprs a b ltac:(isConst) types tt tt sexprs with
          | (?types, ?pcType, ?stateType, ?funcs, ?sfuncs, ?P :: nil) =>
            match SEP.reify_exprs ltac:(isConst) types funcs (PTR, tt) with
              | (?types, ?funcs, ?PTR :: nil) => 
                let hyps := constr:(@nil (expr types)) in
                let s := eval simpl in (SEP.hash P) in
                generalize (@symeval_read_word_correct types 1 0 2 3 addr_not_state funcs sfuncs known)
                  ; pose hyps
(*
                  hyps PTR (snd s) _ (refl_equal _) CS STN nil nil M I H)
*)
            end
        end
      end.
      intros.
      pose evaluators.

        

      specialize (H0 evaluators).
      (** TODO : the known list needs to be parameterized appropriately... **)

      simpl. auto.
    Qed.

    Goal forall p1 p2 p3 v1 v2 v3 cs stn m,
      Satisfies cs stn (ST.star (ptsto32 p1 v1) (ST.star (ptsto32 p2 v2) (ptsto32 p3 v3))) m
      -> Satisfies cs stn (ST.star (ptsto32 p1 v1) (ST.star (ptsto32 p2 v3) (ptsto32 p3 v3))) 
           (mem_set_word B.addr B.mem B.footprint_w B.mem_set (IL.explode stn) p2 v3 m).
    Proof.
      intros.
      match goal with
        | [ H : Satisfies ?CS ?STN ?P ?M
          |- context [ mem_set_word B.addr B.mem B.footprint_w B.mem_set (IL.explode stn) ?PTR ?VAL ?M ] ] =>
        let Ts := constr:(@nil Type) in
        let Ts := SEP.collectAllTypes_sexpr ltac:(isConst) Ts (P :: nil) in
        let Ts := SEP.collectAllTypes_expr ltac:(isConst) Ts (PTR, (VAL, tt)) in
        let types := eval unfold pre_types in pre_types in
        let types := SEP.extend_all_types Ts types in
        let sexprs := constr:(P :: nil) in
        match SEP.reify_sexprs a b ltac:(isConst) types tt tt sexprs with
          | (?types, ?pcType, ?stateType, ?funcs, ?sfuncs, ?P :: nil) =>
             match SEP.reify_exprs ltac:(isConst) types funcs (PTR, (VAL, tt)) with
              | (?types, ?funcs, ?PTR :: ?VAL :: nil) => 
                 let hyps := constr:(@nil (expr pre_types)) in
                let s := eval simpl in (SEP.hash P) in
                generalize (@symeval_write_word_correct types 1 0 2 3 addr_not_state sfuncs known evaluators 
                  hyps PTR VAL (snd s) _ (refl_equal _) CS STN funcs nil nil M _ I (refl_equal _) H)
            end
        end
      end.
      simpl; auto.
    Qed.
*)

  End Tests.
End EvaluatorTests.
