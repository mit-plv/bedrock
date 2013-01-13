Require Import AutoSep Malloc ThreadQueue.
Export AutoSep Malloc.


Module Make(M : ThreadQueue.S).
Module Q := ThreadQueue.Make(M).
Import M Q.
Export M Q.

Section Recall.
  Variable imps : LabelMap.t assert.
  Variable mn : string.

  Import DefineStructured.
  Transparent evalInstrs.

  Definition Recall_ (mn' l : string) : cmd imps mn.
    red; refine (fun pre => {|
      Postcondition := match LabelMap.find (mn', Global l) imps with
                         | None => (fun _ => [| False |])%PropX
                         | Some pre' => (fun stn_st => Ex st', pre (fst stn_st, st')
                           /\ Ex cp : W, [| evalInstrs (fst stn_st) st' (Assign Rp cp :: nil) = Some (snd stn_st) |]
                             /\ [| (fst stn_st).(Labels) (mn', Global l) = Some cp |]
                             /\ Cptr cp pre')%PropX
                       end;
      VerifCond := match LabelMap.find (mn', Global l) imps with
                     | None => jumpToUnknownLabel (mn', Global l)
                     | Some _ => True
                   end :: nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (Assign Rp (RvLabel (mn', Global l)) :: nil,
          Uncond (RvLabel (mn, Local Exit)))) :: nil
      |}
    |}); abstract (struct; try congruence; descend; eauto; propxFo; eauto 10).
  Defined.
End Recall.


Definition Exit : chunk := (Call "threadq"!"exit"("sc")
  [PREonly[_] [| False |]];; Fail)%SP.

Definition Go : chunk := (Call "threadq"!"exit"("sc")
  [PREonly[_] [| False |]];; Fail)%SP.

Definition Yield_ (afterCall : list string -> nat -> assert) : chunk :=
  (Call "threadq"!"yield"("sc")
    [fun (_ : bool) (_ : W -> W) => afterCall])%SP.

Local Notation RET := (fun inv ns => inv true (fun w => w ^- $(4 + 4 * List.length ns)) ns).

Notation "'Yield' [ afterCall ]" := (Yield_ (RET afterCall)) : SP_scope.

Definition Recall (mn' l : string) : chunk := fun ns res =>
  Structured nil (fun _ _ _ => Recall_ _ _ mn' l).

Definition Spawn_ (l : label) (ss : W) (afterCall : list string -> nat -> assert) : chunk :=
  match snd l with
    | Global l' =>
      (Recall (fst l) l';;
        Call "threadq"!"spawn"("sc", Rp, ss)
        [fun (_ : bool) (_ : W -> W) => afterCall])%SP
    | _ => Fail%SP
  end.

Notation "'Spawn' ( l , ss ) [ afterCall ]" := (Spawn_ l ss (RET afterCall)) : SP_scope.

Require Import Bool.

Ltac vcgen_simp := cbv beta iota zeta delta [map app imps
  LabelMap.add Entry Blocks Postcondition VerifCond
  Straightline_ Seq_ Diverge_ Fail_ Skip_ Assert_
  Structured.If_ Structured.While_ Goto_ Structured.Call_ IGoto
  setArgs Programming.Reserved Programming.Formals Programming.Precondition
  importsMap fullImports buildLocals blocks union Nplus Nsucc length N_of_nat
  List.fold_left ascii_lt string_lt label'_lt
  LabelKey.compare' LabelKey.compare LabelKey.eq_dec
  LabelMap.find
  toCmd Seq Instr Diverge Fail Skip Assert_
  Programming.If_ Programming.While_ Goto Programming.Call_ RvImm'
  Assign' localsInvariant localsInvariantCont
  regInL lvalIn immInR labelIn variableSlot string_eq ascii_eq
  andb eqb qspecOut
  ICall_ Structured.ICall_
  Assert_ Structured.Assert_
  LabelMap.Raw.find LabelMap.this LabelMap.Raw.add
  LabelMap.empty LabelMap.Raw.empty string_dec
  Ascii.ascii_dec string_rec string_rect sumbool_rec sumbool_rect Ascii.ascii_rec Ascii.ascii_rect
  Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym
  fst snd labl
  Ascii.N_of_ascii Ascii.N_of_digits N.compare Nmult Pos.compare Pos.compare_cont
  Pos.mul Pos.add LabelMap.Raw.bal
  Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec LabelMap.Raw.create
  ZArith_dec.Z_gt_le_dec Int.Z_as_Int.plus Int.Z_as_Int.max LabelMap.Raw.height
  ZArith_dec.Z_gt_dec Int.Z_as_Int._1 BinInt.Z.add Int.Z_as_Int._0 Int.Z_as_Int._2 BinInt.Z.max
  ZArith_dec.Zcompare_rec ZArith_dec.Z_ge_lt_dec BinInt.Z.compare ZArith_dec.Zcompare_rect
  ZArith_dec.Z_ge_dec label'_eq label'_rec label'_rect
  COperand1 CTest COperand2 Pos.succ
  makeVcs
  Note_ Note__
  IGotoStar_ IGotoStar AssertStar_ AssertStar
  Exit Go Yield_ Recall Spawn_
].

Ltac vcgen := structured_auto vcgen_simp;
  autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *; refold.

Ltac sep unf hints := unfold ginv in *; unf;
  match goal with
    | [ |- context[starting] ] => post; evaluate hints; descend; [
      toFront_conc ltac:(fun P => match P with
                                    | starting _ _ _ => idtac
                                  end); apply starting_intro;
      unfold ginv in *; unf; descend; [ | step hints | ];
      step hints; unfold localsInvariantCont | | ]; AutoSep.sep hints
    | _ => AutoSep.sep hints
  end.

End Make.
