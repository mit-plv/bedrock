Require Import Compile.

Definition funcFinalSpec (fs : settings -> W -> option Callee) f : assert := st ~>
  (Ex s, [| s = Name f |])
  /\ ExX, Ex vs, Ex a, Ex res,
  ![^[locals ("rp" :: "__reserved" :: "__arg" :: nil) vs res st#Sp * heap a * mallocHeap 0] * #0] st
  /\ [| res = wordToNat (sel vs "__reserved")
    /\ Safety.Safe (fs (fst st)) (Body f) (vs, a) |]
  /\ (st#Rp, fst st) @@@ (st' ~> Ex vs', Ex a',
    [| st'#Sp = st#Sp |]
    /\ ![^[locals ("rp" :: "__reserved" :: "__arg" :: nil) vs' res st'#Sp * heap a' * mallocHeap 0] * #1] st'
    /\ [| exists vs'', RunsTo (fs (fst st)) (Body f) (vs, a) (vs'', a') |] ).

Definition funcFinalSpec' (fs : settings -> W -> option Callee) f : assert := st ~>
  funcsOk (fst st) (fs (fst st))
  /\ funcFinalSpec fs f st.

Notation "'bstub' name [ p ] b 'end'" :=
  {| FName := name;
    FPrecondition := p;
    FBody := b%SP;
    FVars := nil;
    FReserved := 0 |}
  (no associativity, at level 95, name at level 0, only parsing) : SPfuncs_scope.

Section Recall.
  Variable imps : LabelMap.t assert.
  Variable mn : string.

  Import DefineStructured.

  Variables modName func : string.

  Transparent evalInstrs.

  Definition Recall_ : cmd imps mn.
    red; refine (fun pre => {|
      Postcondition := (fun stn_st =>
        match LabelMap.find (modName, Global func) imps with
          | None => [| False |]
          | Some spec => Ex pc, [| Labels (fst stn_st) (modName, Global func) = Some pc |]
            /\ Ex st, pre (fst stn_st, st)
            /\ [| evalInstrs (fst stn_st) st (Assign Rv pc :: nil) = Some (snd stn_st) |]
            /\ Cptr pc spec
        end)%PropX;
      VerifCond := (LabelMap.find (modName, Global func) imps <> None)%type :: nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (Assign Rv (RvLabel (modName, Global func)) :: nil,
          Uncond (RvLabel (mn, Local Exit)))) :: nil
      |}
    |}); [ abstract struct
      | abstract (intros; repeat match goal with
                                   | [ H : vcs nil |- _ ] => clear H
                                   | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; subst
                                   | [ |- List.Forall _ _ ] => constructor; simpl
                                   | [ |- blockOk _ _ _ ] => hnf; intros
                                 end;
      edestruct (H (mn, Local Exit)); [
        apply LabelMap.add_2; [ lomega | ];
          apply LabelMap.add_1; auto
        | post; case_eq (LabelMap.find (modName, Global func) imps); intros; try congruence;
          edestruct (H (modName, Global func)); [
            do 2 (apply LabelMap.add_2; [ lomega | ]);
              apply LabelMap.find_2; eauto
            | post; rewrite H7; rewrite H4; descend; eauto; simpl ] ];
      cbv beta in *; rewrite H2; propxFo; eauto 10) ].
  Defined.
End Recall.

Definition Recall__ x y : chunk := fun ns _ =>
  Structured nil (fun _ _ _ => Recall_ _ _ x y).

Notation "x <-- 'Recall' l" := (match snd l with
                                  | Local _ => Fail
                                  | Global s =>
                                    Recall__ (fst l) s;;
                                    x <- Rv
                                end)%SP (no associativity, at level 95) : SP_scope.

Ltac vcgen_simp :=
  cbv beta iota zeta
   delta [map app imps LabelMap.add Entry Blocks Postcondition VerifCond
         Straightline_ Seq_ Diverge_ Fail_ Skip_ Assert_ Structured.If_
         Structured.While_ Goto_ Structured.Call_ IGoto setArgs Reserved
         Formals Precondition importsMap fullImports buildLocals blocks union
         N.add N.succ Datatypes.length N.of_nat fold_left ascii_lt string_lt
         label'_lt LabelKey.compare' LabelKey.compare LabelKey.eq_dec
         LabelMap.find toCmd Programming.Seq Instr Diverge Fail
         Programming.Skip Assert_ If_ While_ Goto Call_ RvImm' Assign'
         localsInvariant localsInvariantCont regInL lvalIn immInR labelIn
         variableSlot string_eq ascii_eq andb Bool.eqb qspecOut ICall_
         Structured.ICall_ Assert_ Structured.Assert_ LabelMap.Raw.find
         LabelMap.this LabelMap.Raw.add LabelMap.empty LabelMap.Raw.empty
         string_dec Ascii.ascii_dec string_rec string_rect sumbool_rec
         sumbool_rect Ascii.ascii_rec Ascii.ascii_rect Bool.bool_dec bool_rec
         bool_rect eq_rec_r eq_rec eq_rect eq_sym fst snd labl
         Ascii.N_of_ascii Ascii.N_of_digits N.compare N.mul Pos.compare
         Pos.compare_cont Pos.mul Pos.add LabelMap.Raw.bal
         Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec LabelMap.Raw.create
         ZArith_dec.Z_gt_le_dec Int.Z_as_Int.plus Int.Z_as_Int.max
         LabelMap.Raw.height ZArith_dec.Z_gt_dec Int.Z_as_Int._1 BinInt.Z.add
         Int.Z_as_Int._0 Int.Z_as_Int._2 BinInt.Z.max ZArith_dec.Zcompare_rec
         ZArith_dec.Z_ge_lt_dec BinInt.Z.compare ZArith_dec.Zcompare_rect
         ZArith_dec.Z_ge_dec label'_eq label'_rec label'_rect COperand1 CTest
         COperand2 Pos.succ makeVcs Note_ Note__ IGotoStar_ IGotoStar
         AssertStar_ AssertStar Cond_ Cond Recall_ Recall__].

Ltac vcgen := structured_auto vcgen_simp;
  autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *; refold.

