Require Import List Bedrock.DepList.
Require Import Heaps.
Require Import Bedrock.ndep.Expr Bedrock.ndep.SepExpr Bedrock.ndep.SymEval.

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
        match SEP.reflect_sexprs a b ltac:(isConst) types tt tt sexprs with
          | (?types, ?pcType, ?stateType, ?funcs, ?sfuncs, ?P :: nil) =>
            match SEP.reflect_exprs ltac:(isConst) types funcs (PTR, tt) with
              | (?types, ?funcs, ?PTR :: nil) => 
                let hyps := constr:(@nil (expr pre_types)) in
                let s := eval simpl in (SEP.hash P) in
                generalize (@symeval_read_word_correct types 1 0 2 3 addr_not_state sfuncs known evaluators
                  hyps PTR (snd s) _ (refl_equal _) CS STN funcs nil nil M I H)
            end
        end
      end.
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
        match SEP.reflect_sexprs a b ltac:(isConst) types tt tt sexprs with
          | (?types, ?pcType, ?stateType, ?funcs, ?sfuncs, ?P :: nil) =>
             match SEP.reflect_exprs ltac:(isConst) types funcs (PTR, (VAL, tt)) with
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

  End Tests.
End EvaluatorTests.
