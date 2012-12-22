Require Import AutoSep Malloc Scheduler.
Export AutoSep Malloc Scheduler.


Definition threadInvariantCont (pre : vals -> W -> qspec) (rpStashed : bool) (adjustSp : W -> W)
  (ns : list string) (res : nat) : assert := st ~>
    let sp := adjustSp st#Sp in
      ExX (* sched *), Ex vs,
      (ExX (* fr *), qspecOut (pre (sel vs) st#Rv) (fun pre =>
        ![ ^[locals ("rp" :: "sc" :: ns) vs res sp * pre * mallocHeap 0] * #1 * #0 ] st))
      /\ (Ex pc_exit, [| (fst st).(Labels) ("scheduler"!"exit")%SP = Some pc_exit |]
        /\ ExX (* pre_exit *), Cptr pc_exit #0
        /\ (AlX (* fr_exit *) : settings * smem, Al st', Al vs',
          ![^[locals ("rp" :: "sc" :: nil) vs' 12 st'#Sp]
            * (#2 * #0 * ^[mallocHeap 0])] st'
          /\ [| sel vs' "sc" = sel vs "sc" |]
          /\ [| (fst st').(Labels) = (fst st).(Labels) |]
          ---> #1 st')).

Notation "'PREonly' [ vs ] pre" := (threadInvariantCont (fun vs _ => pre%qspec%Sep))
  (at level 89) : thread_scope.

Delimit Scope thread_scope with thread.

Notation "'SPECthd' 'reserving' n inv" :=
  (let inv' := inv%thread in let n' := n in {| Reserved := n';
    Formals := nil;
    Precondition := fun extras =>
    match extras with
      | None => inv' false (fun w => w) nil n'
      | Some extras => inv' true (fun w => w) extras (n' - List.length extras)
    end |}) (at level 90, n at level 0, inv at next level).

Notation "'SPECthd' ( x1 , .. , xN ) 'reserving' n inv" :=
  (let inv' := inv%thread in let vars := cons x1 (.. (cons xN nil) ..) in
   let n' := n in
    {| Reserved := n';
      Formals := vars;
      Precondition := fun extras =>
      match extras with
        | None => inv' false (fun w => w) vars n'
        | Some extras => inv' true (fun w => w) extras (n' - (List.length extras - List.length vars))
      end |} ) (at level 90, n at level 0, x1 at level 0, xN at level 0, inv at next level).

Notation "'tfunctionNoRet' name ( x1 , .. , xN ) [ p ] b 'end'" :=
  (let p' := p%thread in
   let vars := cons x1 (.. (cons xN nil) ..) in
   let b' := b%thread%SP in
    {| FName := name;
      FPrecondition := Precondition p' None;
      FBody := ((fun _ _ =>
        Structured nil (fun im mn _ => Structured.Assert_ im mn (Precondition p' (Some vars))));;
      (fun ns res => b' ("sc" :: ns) (res - (List.length vars - List.length (Formals p')))%nat))%SP;
      FVars := vars;
      FReserved := Reserved p' |})
  (no associativity, at level 95, name at level 0, p at level 0, only parsing) : SPfuncs_scope.

Notation "'tfunctionNoRet' name () [ p ] b 'end'" :=
  (let p' := p%thread in
   let b' := b%thread%SP in
    {| FName := name;
      FPrecondition := Precondition p' None;
      FBody := ((fun _ _ =>
        Structured nil (fun im mn _ => Structured.Assert_ im mn (Precondition p' (Some nil))));;
      (fun ns res => b' ("sc" :: ns) res))%SP;
      FVars := nil;
      FReserved := Reserved p' |})
  (no associativity, at level 95, name at level 0, p at level 0, only parsing) : SPfuncs_scope.

Section Thread.
  Variable imps : LabelMap.t assert.
  Variable mn : string.

  Import DefineStructured.
  Transparent evalInstrs.

  Definition Exit_ : cmd imps mn.
    red; refine (fun pre => {|
      Postcondition := (fun _ => [| False |])%PropX;
      VerifCond := (forall specs stn st, interp specs (pre (stn, st))
        -> exists pc_exit, stn.(Labels) ("scheduler", Global "exit") = Some pc_exit
          /\ exists pre_exit, specs pc_exit = Some pre_exit
            /\ interp specs (pre_exit (stn, st)))
        :: nil;
      Generate := fun _ _ => {|
        Entry := 0;
        Blocks := (pre, (nil, Uncond (RvLabel ("scheduler", Global "exit")))) :: nil
      |}
    |}); abstract struct.
  Defined.

  Definition Go_ : cmd imps mn.
    red; refine (fun pre => {|
      Postcondition := (fun _ => [| False |])%PropX;
      VerifCond := (forall specs stn st, interp specs (pre (stn, st))
        -> exists pre_exit, LabelMap.find ("scheduler", Global "exit") imps = Some pre_exit
          /\ interp specs (pre_exit (stn, st)))
        :: nil;
      Generate := fun _ _ => {|
        Entry := 0;
        Blocks := (pre, (nil, Uncond (RvLabel ("scheduler", Global "exit")))) :: nil
      |}
    |}); abstract (struct; congruence).
  Defined.

  Definition Recall (mn' l : string) : cmd imps mn.
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

  Definition Spawn_ (afterCall : assert) : cmd imps mn.
    red; refine (fun pre => {|
      Postcondition := afterCall;
      VerifCond := match LabelMap.find ("scheduler", Global "spawn") imps with
                     | None => jumpToUnknownLabel ("scheduler", Global "spawn")
                     | Some spawn => forall stn st specs,
                       interp specs (pre (stn, st))
                       -> forall rp, specs rp = Some afterCall
                         -> interp specs (spawn (stn, {| Regs := rupd (Regs st) Rp rp; Mem := Mem st |}))
                   end :: nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (Assign Rp (RvLabel (mn, Local Exit)) :: nil,
          Uncond (RvLabel ("scheduler", Global "spawn")))) :: nil
      |}
    |}); [ abstract struct
      | abstract (intros;
        repeat match goal with
                 | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; subst
                 | [ H : vcs nil |- _ ] => clear H
                 | [ _ : match ?E with Some _ => _ | None => _ end |- _ ] => destrOpt E; [ | tauto ]
                 | [ |- List.Forall _ nil ] => constructor
                 | [ |- List.Forall _ (_ :: _) ] => constructor
                 | [ |- blockOk _ _ _ ] => simpl; hnf; intros
               end;
        match goal with
          | [ H : forall l : LabelMap.key, _ |- _ ] =>
            repeat match goal with
                     | [ H' : LabelMap.find ?k _ = Some _ |- _ ] =>
                       edestruct (H k); [ solve [ eauto ] | ]; generalize dependent H'
                   end
        end; struct; descend; (simpl; eauto)) ].
  Defined.
End Thread.

Definition Exit : chunk := fun ns _ =>
  Structured (Binop Rv Sp Plus (4 + 4 * length ns)
    :: Assign (LvMem (Indir Rv 4)) (LvMem (Indir Sp 4))
    :: Binop Sp Sp Plus (4 + 4 * length ns)
    :: nil)
  (fun _ _ _ => Exit_ _ _).

Definition Go (rv : rvalue') : chunk := fun ns _ =>
  Structured (Binop Rv Sp Plus (4 + 4 * length ns)
    :: Assign (LvMem (Indir Rv 4)) (rv ns)
    :: Binop Sp Sp Plus (4 + 4 * length ns)
    :: nil)
  (fun _ _ _ => Go_ _ _).

Definition SpawnBootstrap (rv : rvalue') (l : label) (ss : W) (afterCall : list string -> nat -> assert)
  : chunk := fun ns res =>
    match snd l with
      | Global l' =>
        Seq (Seq (fun _ _ => Structured nil (fun _ _ H => Recall _ _ (fst l) l'))
          (fun ns _ => Structured
            (Binop Rv Sp Plus (4 + 4 * length ns)
              :: Assign (LvMem (Indir Rv 4)) (rv ns)
              :: Binop Rv Sp Plus (4 + 4 * length ns)
              :: Assign (LvMem (Indir Rv 8)) Rp
              :: Binop Rv Sp Plus (4 + 4 * length ns)
              :: Assign (LvMem (Indir Rv 12)) ss
              :: Binop Sp Sp Plus (4 + 4 * length ns)
              :: nil)
            (fun _ _ _ => Spawn_ _ _ (afterCall ns res))))
        (Instr (fun ns => Binop Sp Sp Minus (4 + 4 * length ns))) ns res
      | _ => Fail ns res
    end.

Local Notation RET := (fun inv ns => inv true (fun w => w ^- $(4 + 4 * List.length ns)) ns).

Notation "'Spawn' ( rv , l , ss ) [ afterCall ]" :=
  (SpawnBootstrap rv l ss (RET afterCall)).

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
  Assign' localsInvariant localsInvariantCont threadInvariantCont
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
  IGotoStar_ IGotoStar
  Exit_ Exit Go_ Go Recall Spawn_ SpawnBootstrap
].

Ltac vcgen := structured_auto vcgen_simp;
  autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *; refold.

Ltac sep' hints := unfold localsInvariantCont; AutoSep.sep hints;
  match goal with
    | [ |- Some _ = Some _ ] => reflexivity
    | _ => AutoSep.sep hints
  end.

Ltac sep hints :=
  match goal with
    | [ |- forall specs stn st, interp specs _
      -> exists pc_exit, Labels stn ("scheduler", Global "exit") = Some pc_exit
        /\ _ ] =>
      post; match goal with
              | [ H : context[locals ?ns ?vs ?avail ?sp] |- _ ] =>
                let offset := eval simpl in (4 * length ns) in
                  assert (ok_call ns ("rp" :: "sc" :: nil) avail 12 offset) by
                    (split; [ simpl; omega
                      | split; [ simpl; omega
                        | split; [ NoDup
                          | reflexivity ] ] ]);
                    change (locals ns vs avail sp)
              with (locals_call ns vs avail sp ("rp" :: "sc" :: nil) 12 offset) in H;
                sep' hints; eapply Imply_sound; [ solve [ eauto ] | ];
                  descend; repeat (step hints; descend); try reflexivity
            end
    | _ => sep' hints
  end.

Ltac sep_auto := sep auto_ext.
