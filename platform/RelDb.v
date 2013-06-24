Require Import AutoSep Wrap StringOps Malloc ArrayOps Buffers Bags SinglyLinkedList.

Set Implicit Arguments.


(** * Database schemas and query/command types *)

Definition schema := list string.

Inductive exp :=
| Const (s : string)
| Input (pos len : string).

Definition baseVars := "ibuf" :: "row" :: "ilen" :: "overflowed" :: "tmp" :: "ipos" :: "buf" :: "len" :: nil.

Definition wfExp (ns : list string) (e : exp) :=
  match e with
    | Const s => goodSize (String.length s)
    | Input pos len => In pos ns /\ In len ns /\ ~In pos baseVars /\ ~In len baseVars
  end.

Definition wfExps ns := List.Forall (wfExp ns).

Definition freeable8 buf len :=
  exists len', len = 4 * len' /\ freeable buf len'.

Section preds.
  Open Scope Sep_scope.

  Definition posl := map (@fst W W).
  Definition lenl := map (@snd W W).

  Definition inBounds (len : W) (cols : list (W * W)) :=
    List.Forall (fun col => wordToNat (fst col) + wordToNat (snd col) <= wordToNat len)%nat cols.

  Variable s : schema.

  Definition row (p : W) :=
    Ex buf, Ex len, Ex cols, Ex bs,
    (p ==*> buf, len) * array (posl cols) (p ^+ $8) * array (lenl cols) (p ^+ $8 ^+ $(length s * 4)) * array8 bs buf
    * [| length bs = wordToNat len |] * [| length cols = length s |] * [| inBounds len cols |]
    * [| p <> 0 |] * [| freeable p (2 + length s + length s) |]
    * [| buf <> 0 |] * [| freeable8 buf (length bs) |].

  Theorem row_fwd : forall p,
    row p ===> Ex buf, Ex len, Ex cols, Ex bs,
    (p ==*> buf, len) * array (posl cols) (p ^+ $8) * array (lenl cols) (p ^+ $8 ^+ $(length s * 4)) * array8 bs buf
    * [| length bs = wordToNat len |] * [| length cols = length s |] * [| inBounds len cols |]
    * [| p <> 0 |] * [| freeable p (2 + length s + length s) |]
    * [| buf <> 0 |] * [| freeable8 buf (length bs) |].
    unfold row; sepLemma.
  Qed.

  Theorem row_bwd : forall p,
    (Ex buf, Ex len, Ex cols, Ex bs,
    (p ==*> buf, len) * array (posl cols) (p ^+ $8) * array (lenl cols) (p ^+ $8 ^+ $(length s * 4)) * array8 bs buf
    * [| length bs = wordToNat len |] * [| length cols = length s |] * [| inBounds len cols |]
    * [| p <> 0 |] * [| freeable p (2 + length s + length s) |]
    * [| buf <> 0 |] * [| freeable8 buf (length bs) |]) ===> row p.
    unfold row; sepLemma.
  Qed.
    
  Definition rows (_ : W) := starL row.

  Theorem rows_cons_bwd : forall (dummy : W) ps, dummy <> 0
    -> (Ex p, Ex ps', Ex dummy', [| ps = p :: ps' |] * row p * rows dummy' ps') ===> rows dummy ps.
    destruct ps; simpl; unfold row; sepLemma; eauto;
      match goal with
        | [ H : _ :: _ = _ :: _ |- _ ] => injection H; clear H; intros; subst; sepLemma
      end.
  Qed.

  Definition table (p : W) :=
    Ex p', Ex ls, p =*> p' * sll ls p' * rows p' ls.

  Theorem table_fwd : forall p, table p ===> Ex p', Ex ls, p =*> p' * sll ls p' * rows p' ls.
    unfold table; sepLemma.
  Qed.

  Theorem table_bwd : forall p, (Ex p', Ex ls, p =*> p' * sll ls p' * rows p' ls) ===> table p.
    unfold table; sepLemma.
  Qed.
End preds.

Fixpoint zip A (ls1 ls2 : list A) : list (A * A) :=
  match ls1, ls2 with
    | x1 :: ls1', x2 :: ls2' => (x1, x2) :: zip ls1' ls2'
    | _, _ => nil
  end.

Lemma length_zip : forall A (ls1 ls2 : list A),
  length ls1 = length ls2
  -> length (zip ls1 ls2) = length ls1.
  induction ls1; destruct ls2; simpl; intuition.
Qed.

Lemma posl_zip : forall ls1 ls2,
  length ls1 = length ls2
  -> posl (zip ls1 ls2) = ls1.
  induction ls1; destruct ls2; simpl; intuition; f_equal; auto.
Qed.

Lemma lenl_zip : forall ls1 ls2,
  length ls1 = length ls2
  -> lenl (zip ls1 ls2) = ls2.
  induction ls1; destruct ls2; simpl; intuition; f_equal; auto.
Qed.

Lemma create_len_pos : forall base len off,
  allocated base off (len + len)
  ===> Ex ls, array (posl ls) (base ^+ natToW off)
  * array (lenl ls) (base ^+ natToW off ^+ natToW (len * 4))
  * [| length ls = len |].
  intros.
  eapply Himp_trans; [ eapply allocated_split; instantiate (1 := len); omega | ].
  eapply Himp_trans; [ eapply Himp_star_frame; apply MoreArrays.allocate_array' | ].
  sepLemma; fold (@length (W * W)) in *; fold (@length W) in *; rewrite Minus.minus_plus in *.
  apply length_zip; symmetry; eassumption.
  rewrite posl_zip, lenl_zip by auto.
  rewrite natToW_plus.
  rewrite Mult.mult_comm.
  rewrite wplus_assoc.
  sepLemma.
Qed.

Import Div2.

Definition even n := exists k, n = k + k.

Lemma div2_double' : forall n, div2 (n + n) = n.
  induction n; simpl; try rewrite <- plus_n_Sm; intuition.
Qed.

Inductive expand_allocated (off : nat) := ExpandAllocated.
Local Hint Constructors expand_allocated.

Lemma create_len_pos_div2 : forall base len off,
  even len
  -> expand_allocated off
  -> allocated base off len
  ===> Ex ls, array (posl ls) (base ^+ natToW off)
  * array (lenl ls) (base ^+ natToW off ^+ natToW (div2 len * 4))
  * [| length ls = div2 len |].
  destruct 1; subst; intros; rewrite div2_double'; apply create_len_pos.
Qed.

Definition hints : TacPackage.
  prepare (nil_fwd, cons_fwd, table_fwd, row_fwd, create_len_pos_div2)
  (nil_bwd, cons_bwd, table_bwd, row_bwd, rows_cons_bwd).
Defined.

Definition inputOk1 (V : vals) (e : exp) :=
  match e with
    | Const _ => True
    | Input pos len => wordToNat (sel V pos) + wordToNat (sel V len) <= wordToNat (sel V "len")
  end%nat.

Definition inputOk (V : vals) := List.Forall (inputOk1 V).


(** * Inserting into a table *)

Section Insert.
  Variable A : Type.
  Variable invPre : A -> vals -> HProp.
  Variable invPost : A -> vals -> W -> HProp.

  Variable tptr : W.
  Variable sch : schema.
  Variable es : list exp.
  Variable bufSize : W.

  (* Precondition and postcondition *)
  Definition invar :=
    Al a : A, Al bs,
    PRE[V] array8 bs (V "buf") * table sch tptr * mallocHeap 0
      * [| length bs = wordToNat (V "len") |] * [| inputOk V es |] * invPre a V
    POST[R] array8 bs (V "buf") * table sch tptr * mallocHeap 0
      * invPost a V R.

  (* Alternate sequencing operator, which generates twistier code but simpler postconditions and VCs *)
  Definition SimpleSeq (ch1 ch2 : chunk) : chunk := fun ns res =>
    Structured nil (fun im mn H => Seq_ H (toCmd ch1 mn H ns res) (toCmd ch2 mn H ns res)).

  Infix ";;" := SimpleSeq : SP_scope.

  (* Write the value of an expression into a new row's buffer. *)
  Definition writeExp (col : nat) (e : exp) : chunk :=
    match e with
      | Const s => StringWrite "ibuf" "ilen" "ipos" "overflowed" s
        (fun (p : list B * A) V => array8 (fst p) (V "buf") * mallocHeap 0 * table sch tptr
          * Ex cols, (V "row" ==*> V "ibuf", V "ilen") * array (posl cols) (V "row" ^+ $8)
          * array (lenl cols) (V "row" ^+ $8 ^+ $(length sch * 4))
          * [| length (fst p) = wordToNat (V "len") |] * [| length cols = length sch |]
          * [| V "row" <> 0 |] * [| freeable (V "row") (2 + length sch + length sch) |]
          * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (wordToNat (V "ilen")) |]
          * [| inBounds (V "ilen") (firstn col cols) |] * [| inputOk V es |] * invPre (snd p) V)%Sep
        (fun (p : list B * A) V R => array8 (fst p) (V "buf") * mallocHeap 0 * table sch tptr
          * invPost (snd p) V R)%Sep
      | Input start len =>
        "tmp" <- "ilen" - "ipos";;
        If ("tmp" < len) {
          "overflowed" <- 1
        } else {
          Call "array8"!"copy"("ibuf", "ipos", "buf", start, len)
          [Al a : A, Al bs, Al bsI,
            PRE[V] array8 bs (V "buf") * table sch tptr
              * [| V "ipos" <= V "ilen" |]%word
              * array8 bsI (V "ibuf") * [| length bsI = wordToNat (V "ilen") |] * [| V "ibuf" <> 0 |]
              * [| freeable8 (V "ibuf") (wordToNat (V "ilen")) |]
              * Ex cols, (V "row" ==*> V "ibuf", V "ilen") * array (posl cols) (V "row" ^+ $8)
              * array (lenl cols) (V "row" ^+ $8 ^+ $(length sch * 4))
              * [| length bs = wordToNat (V "len") |] * [| length cols = length sch |]
              * [| V "row" <> 0 |] * [| freeable (V "row") (2 + length sch + length sch) |]
              * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (wordToNat (V "ilen")) |]
              * [| inBounds (V "ilen") (firstn col cols) |] * [| inputOk V es |]
              * [| V len <= V "ilen" ^- V "ipos" |]%word
              * invPre a V * mallocHeap 0
            POST[R] array8 bs (V "buf") * table sch tptr * mallocHeap 0 * invPost a V R];;
          "ipos" <- "ipos" + len
        }
    end%SP.

  Definition lengthOf (e : exp) : rvalue' :=
    match e with
      | Const s => String.length s
      | Input _ len => len
    end%SP.

  Definition winv' (col : nat) :=
    Al a : A, Al bs, Al bsI,
      PRE[V] array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * array8 bsI (V "ibuf") * [| length bsI = wordToNat (V "ilen") |]
        * [| V "ipos" <= V "ilen" |]
        * Ex cols, (V "row" ==*> V "ibuf", V "ilen") * array (posl cols) (V "row" ^+ $8)
        * array (lenl cols) (V "row" ^+ $8 ^+ $(length sch * 4))
        * [| length bs = wordToNat (V "len") |] * [| length cols = length sch |]
        * [| V "row" <> 0 |] * [| freeable (V "row") (2 + length sch + length sch) |]
        * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (wordToNat (V "ilen")) |]
        * [| inBounds (V "ilen") (firstn col cols) |] * [| inputOk V es |] * invPre a V
      POST[R] array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * invPost a V R.

  Definition winv (col : nat) := winv' col true (fun w => w).

  Fixpoint writeExps (col : nat) (es : list exp) {struct es} : chunk :=
    match es with
      | nil => Skip
      | e :: es' =>
        (* Save the current position as the start of the current column. *)
        "tmp" <- "row" + 8;;
        "tmp" + (4 * col)%nat *<- "ipos";;

        (* Check if the current item is small enough to fit in the buffer. *)
        "tmp" <- "ilen" - "ipos";;
        If ("tmp" < lengthOf e) {
          (* It doesn't fit.  Save the "safe" length 0.  [writeExp] will set "overflowed" later. *)
          "tmp" <- "row" + 8;;
          "tmp" <- "tmp" + (length sch * 4)%nat;;
          "tmp" + (4 * col)%nat *<- 0
        } else {
          (* Good, it fits.  Save the proper length. *)
          "tmp" <- "row" + 8;;
          "tmp" <- "tmp" + (length sch * 4)%nat;;
          "tmp" + (4 * col)%nat *<- lengthOf e
        };;
        Assert [winv' (S col)];;
        writeExp (S col) e;;
        writeExps (S col) es'
    end%SP.

  Definition Insert' : chunk := (
    "ibuf" <-- Call "buffers"!"bmalloc"(bufSize)
    [Al a : A, Al bs,
      PRE[V, R] R =?>8 (wordToNat bufSize * 4) * [| R <> 0 |] * [| freeable R (wordToNat bufSize) |]
        * array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * [| length bs = wordToNat (V "len") |] * [| inputOk V es |] * invPre a V
      POST[R'] array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * invPost a V R'];;

    "row" <-- Call "malloc"!"malloc"(0, (2 + length sch + length sch)%nat)
    [Al a : A, Al bs, Al bsI,
      PRE[V, R] array8 bsI (V "ibuf") * [| length bsI = (wordToNat bufSize * 4)%nat |] * [| V "ibuf" <> 0 |]
        * [| freeable (V "ibuf") (wordToNat bufSize) |]
        * R =?> (2 + length sch + length sch)%nat * [| R <> 0 |]
        * [| freeable R (2 + length sch + length sch)%nat |]
        * array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * [| length bs = wordToNat (V "len") |] * [| inputOk V es |] * invPre a V
      POST[R'] array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * invPost a V R'];;

    "row" *<- "ibuf";;
    "ipos" <- 0;;
    "ilen" <- (4 * bufSize)%word;;
    "row"+4 *<- "ilen";;

    Note [expand_allocated 8];;

    writeExps O es;;

    "tmp" <-- Call "malloc"!"malloc"(0, 2)
    [Al a : A, Al bs,
      PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |]
        * row sch (V "row") * array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * [| length bs = wordToNat (V "len") |] * [| inputOk V es |] * invPre a V
      POST[R'] array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * invPost a V R'];;

    "tmp" *<- "row";;
    "tmp"+4 *<- $[tptr];;
    tptr *<- "tmp"
  )%SP.

  Notation "l ~~ im ~~> s" := (LabelMap.find l%SP im = Some (Precondition s None)) (at level 0).

  Lemma incl_peel : forall A (x : A) ls ls',
    incl (x :: ls) ls'
    -> In x ls' /\ incl ls ls'.
    unfold incl; intuition.
  Qed.

  Lemma invPre_sel : forall a V, invPre a (sel V) = invPre a V.
    auto.
  Qed.

  Lemma invPost_sel : forall a V R, invPost a (sel V) R = invPost a V R.
    auto.
  Qed.

  Lemma inputOk_sel : forall V es, inputOk (sel V) es = inputOk V es.
    auto.
  Qed.

  Lemma mult4_S : forall n, 4 * S n = S (S (S (S (4 * n)))).
    simpl; intros; omega.
  Qed.

  Lemma wfExps_inv1 : forall ns e es,
    wfExps ns (e :: es)
    -> wfExp ns e.
    inversion 1; auto.
  Qed.

  Ltac prep := try match goal with
                     | [ _ : context[lengthOf ?E _] |- _ ] =>
                       destruct E; simpl lengthOf in *
                   end; post;
  try match goal with
        | [ H : wfExps _ (_ :: _) |- _ ] =>
          generalize (wfExps_inv1 H); simpl; intuition idtac
      end;
  repeat match goal with
           | [ H : incl nil _ |- _ ] => clear H
           | [ H : incl _ _ |- _ ] =>
             apply incl_peel in H; let P := type of H in destruct H;
               try match goal with
                     | [ H : P |- _ ] => clear H
                   end
         end; clear_fancy;
  try match goal with
        | [ H : importsGlobal _ |- _ ] =>
          repeat match goal with
                   | [ H' : context[H] |- _ ] => clear H'
                 end; clear H
      end;
  unfold lvalIn, regInL, immInR in *; prep_locals;
    try rewrite mult4_S in *;
      try rewrite invPre_sel in *; try rewrite inputOk_sel in *; try rewrite invPost_sel in *; auto.

  Ltac state_apart :=
    try match goal with
          | [ st : (settings * state)%type |- _ ] => destruct st; simpl fst in *; simpl snd in *
        end.

  Lemma posl_bound : forall (es0 : list exp) cols,
    length cols = length sch
    -> (S (length es0) <= length es)%nat
    -> goodSize (length sch)
    -> length es = length sch
    -> natToW (length es - S (length es0)) < natToW (length (posl cols)).
    unfold posl; intros; rewrite map_length;
      apply lt_goodSize; omega || (eapply goodSize_weaken; eauto).
  Qed.

  Lemma lenl_bound : forall (es0 : list exp) cols,
    length cols = length sch
    -> (S (length es0) <= length es)%nat
    -> goodSize (length sch)
    -> length es = length sch
    -> natToW (length es - S (length es0)) < natToW (length (lenl cols)).
    unfold lenl; intros; rewrite map_length;
      apply lt_goodSize; omega || (eapply goodSize_weaken; eauto).
  Qed.

  Hint Immediate posl_bound lenl_bound.

  Lemma natToW_4times : forall n,
    natToW (4 * n) = natToW 4 ^* natToW n.
    intros; rewrite Mult.mult_comm; rewrite wmult_comm; apply natToW_times4.
  Qed.

  Import Div2.

  Ltac evalu := state_apart; unfold buffer in *;
    match goal with
      | [ _ : context[Binop _ _ Plus (RvImm (natToW (4 * _)))] |- _ ] =>
        repeat match goal with
                 | [ H : evalInstrs _ _ _ = _ |- _ ] => generalize dependent H
                 | [ H : evalCond _ _ _ _ _ = _ |- _ ] => generalize dependent H
               end;
        evaluate auto_ext;
        match goal with
          | [ col := _, _ : context[posl ?cols] |- _ ] =>
            assert (natToW col < natToW (length (posl cols)))
              by (subst col; auto);
            assert (natToW col < natToW (length (lenl cols)))
              by (subst col; auto)
        end; intros; rewrite natToW_4times in *;
        try match goal with
              | [ _ : evalCond _ _ _ _ ?s = _,
                  H : evalInstrs _ ?s _ = _ |- _ ] =>
                generalize dependent H; evaluate auto_ext; intro
            end;
        evaluate auto_ext
      | _ =>
        try match goal with
              | [ sch : schema |- _ ] => assert (even (length sch + length sch)) by (hnf; eauto)
            end;
        evaluate hints
    end;
    repeat match goal with
             | [ H : @In string _ _ |- _ ] => clear H
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
             | [ H : evalCond _ _ _ _ _ = _ |- _ ] => clear H
           end; state_apart;
    fold (@firstn (W * W)) in *; fold (@length (W * W)) in *; fold (@length W) in *; fold div2 in *.

  Ltac match_locals :=
    match goal with
      | [ _ : interp _ (?P ?x) |- interp _ (?Q ?x) ] =>
        match P with
          | context[locals _ ?V ?res _] =>
            match Q with
              | context[locals _ ?V' res _] => equate V' V; descend
            end
        end
    end.

  Lemma wminus_wplus : forall u v : W, u ^- v ^+ v = u.
    intros; words.
  Qed.

  Lemma wplus_wminus : forall u v : W, u ^+ v ^- v = u.
    intros; words.
  Qed.

  Hint Rewrite mult4_S wminus_wplus wplus_wminus : words.
  Hint Rewrite mult4_S wminus_wplus wplus_wminus : sepFormula.

  Ltac pair_evar :=
    match goal with
      | [ |- context[@fst ?A ?B ?E] ] => is_evar E;
        let x := fresh in let y := fresh in
          evar (x : A); evar (y : B);
          let x' := eval unfold x in x in let y' := eval unfold y in y in
            equate E (x', y'); clear x y; simpl
    end.

  Ltac my_descend := unfold localsInvariant in *;
    repeat match goal with
             | [ H : (_ * _)%type |- _ ] => destruct H; simpl in *
           end; descend;
    repeat match goal with
             | [ H : Regs _ _ = _ |- _ ] => rewrite H
             | [ |- context[invPre ?a (sel ?V)] ] => rewrite (invPre_sel a V)
             | [ |- context[invPost ?a (sel ?V) ?R] ] => rewrite (invPost_sel a V R)
             | [ |- context[inputOk (sel ?V) ?es] ] => rewrite (inputOk_sel V es)
           end; autorewrite with sepFormula in *; autorewrite with words; try pair_evar.

  Ltac weaken_invPre' :=
    match goal with
      | [ H : context[invPre] |- _ ] => apply H; solve [ descend ]
    end.

  Ltac weaken_invPre :=
    (apply himp_star_frame; try reflexivity; [weaken_invPre'])
    || (etransitivity; [ apply himp_star_comm | ]; apply himp_star_frame; try reflexivity; [weaken_invPre']).

  Ltac weaken_invPost :=
    apply himp_refl;
      match goal with
        | [ H : context[invPost] |- _ ] => apply H; solve [ descend ]
      end.

  Ltac my_cancel' pre post :=
    match post with
      | context[locals ?ns ?vs ?avail _] =>
        match pre with
          | context[excessStack _ ns avail ?ns' ?avail'] =>
            match avail' with
              | avail => fail 1
              | _ =>
                match pre with
                  | context[locals ns ?vs' 0 _] =>
                    equate vs vs';
                    let offset := eval simpl in (4 * List.length ns) in
                      rewrite (create_locals_return ns' avail' ns avail offset);
                        assert (ok_return ns ns' avail avail' offset)%nat by (split; [
                          simpl; omega
                          | reflexivity ] ); autorewrite with sepFormula
                end
            end
        end
    end.

  Ltac my_cancel :=
    match goal with
      | [ |- interp _ (?pre ---> ?post)%PropX ] => my_cancel' pre post
      | [ |- himp _ ?pre ?post ] => my_cancel' pre post
    end; cancel hints.

  Fixpoint updateN (cols : list (W * W)) col pos len :=
    match cols with
      | nil => nil
      | old :: cols' =>
        match col with
          | O => (pos, len) :: cols'
          | S col' => old :: updateN cols' col' pos len
        end
    end.

  Definition update cols (col : W) pos len :=
    updateN cols (wordToNat col) pos len.

  Lemma updN_posl : forall pos len (cols : list (W * W)) col,
    Array.updN (posl cols) col pos = posl (updateN cols col pos len).
    induction cols; destruct col; simpl; intuition.
  Qed.

  Lemma upd_posl : forall (cols : list (W * W)) col pos len,
    Array.upd (posl cols) col pos = posl (update cols col pos len).
    intros; eapply updN_posl.
  Qed.

  Lemma updN_lenl : forall pos len (cols : list (W * W)) col,
    Array.updN (lenl cols) col len = lenl (updateN cols col pos len).
    induction cols; destruct col; simpl; intuition.
  Qed.

  Lemma upd_lenl : forall (cols : list (W * W)) col pos len,
    Array.upd (lenl cols) col len = lenl (update cols col pos len).
    intros; eapply updN_lenl.
  Qed.

  Lemma moveS' : forall n m,
    (S m <= n)%nat
    -> S (n - S m) = n - m.
    intros; omega.
  Qed.

  Lemma wle_plus0 : forall u v : W,
    u <= v
    -> u ^+ natToW 0 <= v.
    intros; pre_nomega.
    rewrite wordToNat_wplus by (rewrite roundTrip_0; apply goodSize_weaken with (wordToNat u); eauto);
      nomega.
  Qed.

  Hint Immediate wle_plus0.

  Ltac updify :=
    match goal with
      | [ |- himp _ ?pre _ ] =>
        match pre with
          | context[Array.upd (posl _) _ _] =>
            erewrite upd_posl; erewrite upd_lenl
          end
    end.

  Ltac guess_locals :=
    match goal with
      | [ _ : context[locals ?ns ?V 0 _] |- context[locals ?ns ?V' _ _] ] =>
        match goal with
          | [ |- interp _ (![ _ ] _) ] => equate V V'; descend
        end
    end.

  Ltac my_step := (unfold natToW in *; congruence) || weaken_invPre || weaken_invPost
    || ((my_cancel || (try updify; try guess_locals; step hints)); fold (@firstn (W * W))).

  Theorem Forall_impl2 : forall A (P Q R : A -> Prop) ls,
    List.Forall P ls
    -> List.Forall Q ls
    -> (forall x, P x -> Q x -> R x)
    -> List.Forall R ls.
    induction 1; inversion 1; auto.
  Qed.

  Theorem inputOk_weaken : forall ns V V' es,
    inputOk V es
    -> wfExps ns es
    -> (forall x, ~In x baseVars \/ x = "len" -> sel V x = sel V' x)
    -> inputOk V' es.
    intros; eapply Forall_impl2; [ apply H | apply H0 | ].
    intro e; destruct e; simpl; intuition idtac.
    repeat rewrite <- H1 by (simpl; tauto); assumption.
  Qed.

  Hint Extern 2 (inputOk _ _) => eapply inputOk_weaken; try eassumption; [ simpl; intuition descend ].

  Lemma roundTrip_2 : wordToNat (natToW 2) = 2.
    auto.
  Qed.

  Hint Rewrite roundTrip_2 : N.

  Ltac invoke1 :=
    match goal with
      | [ H : forall specs : codeSpec _ _, _, H' : interp _ _ |- _ ] => apply H in H'; clear H
    end; post.

  Ltac specify :=
    repeat match goal with
             | [ H : LabelMap.find _ _ = Some _ |- _ ] => try rewrite H; clear H
             | [ H : vcs _ |- _ ] => clear H
           end; propxFo.

  Ltac prove_Himp :=
    match goal with
      | [ V : vals, V' : vals, H : forall x : string, _ |- _ ===> _ ] =>
        specify;
        repeat match goal with
                 | [ |- context[V ?X] ] => change (V X) with (sel V X)
                 | [ |- context[V' ?X] ] => change (V' X) with (sel V' X)
               end; repeat rewrite H by congruence;
        clear_fancy; solve [ sepLemma ]
      | [ V : vals, V' : vals, H : forall x : string, _ |- _ = _ ] =>
        specify;
        repeat match goal with
                 | [ |- context[V ?X] ] => change (V X) with (sel V X)
                 | [ |- context[V' ?X] ] => change (V' X) with (sel V' X)
               end; repeat rewrite H by congruence;
        clear_fancy; match goal with
                       | [ H : _ |- _ ] => solve [ erewrite H; [ reflexivity | auto ] ]
                     end
    end.

  Ltac pre := auto 1; try discriminate; try prove_Himp;
    post; specify; repeat invoke1.

  Lemma moveS : forall A (x : A) (ls : list A) ls',
    (length (x :: ls') <= length ls)%nat
    -> S (length ls - length (x :: ls')) = length ls - length ls'.
    simpl; intros; omega.
  Qed.

  Hint Rewrite wordToNat_wminus using nomega : N.

  Lemma minus_bound : forall (u v w : W) n,
    n = wordToNat w
    -> v < w ^- u
    -> u <= w
    -> (wordToNat u + wordToNat v <= n)%nat.
    intros; subst; nomega.
  Qed.

  Hint Immediate minus_bound.

  Lemma minus_bound' : forall (u v w : W),
    v <= w ^- u
    -> u <= w
    -> u ^+ v <= w.
    intros; pre_nomega;
      rewrite wordToNat_wplus
        by (eapply goodSize_weaken with (wordToNat w); eauto);
        omega.
  Qed.

  Hint Immediate minus_bound'.

  Lemma inBounds_up'' : forall pos len cols col,
    (col < length cols)%nat
    -> firstn (S col) (updateN cols col pos len)
    = firstn col cols ++ (pos, len) :: nil.
    induction cols; simpl; intuition.
    destruct col; simpl; intuition.
    f_equal; apply IHcols; auto.
  Qed.        

  Lemma inBounds_up' : forall pos len cols col,
    (col < length cols)%nat
    -> goodSize (length cols)
    -> firstn (S col) (update cols col pos len)
    = firstn col cols ++ (pos, len) :: nil.
    intros; unfold update.
    rewrite wordToNat_natToWord_idempotent.
    apply inBounds_up''; auto.
    change (goodSize col).
    eapply goodSize_weaken; eauto.
  Qed.
  
  Lemma inBounds_up : forall (es es0 : list exp) ilen cols pos len n,
    let col := length es - S (length es0) in
      inBounds ilen (firstn col cols)
      -> pos ^+ len <= ilen
      -> length cols = n
      -> goodSize n
      -> len <= ilen ^- pos
      -> pos <= ilen
      -> (col < length cols)%nat
      -> (S (length es0) <= length es)%nat
      -> inBounds ilen (firstn (length es - length es0)
        (update cols (length es - S (length es0)) pos len)).
    intros; subst.
    replace (length es0 - length es1) with (S (length es0 - S (length es1))).
    rewrite inBounds_up'; auto.
    apply Forall_app; auto.
    constructor; auto; simpl.
    pre_nomega.
    rewrite wordToNat_wplus in H0; auto.
    eapply goodSize_weaken with (wordToNat ilen); eauto.
    omega.
  Qed.

  Hint Resolve inBounds_up.

  Lemma length_updateN : forall pos len cols col,
    length (updateN cols col pos len) = length cols.
    induction cols; destruct col; simpl; intuition.
  Qed.

  Lemma length_update : forall pos len cols col,
    length (update cols col pos len) = length cols.
    intros; apply length_updateN.
  Qed.

  Hint Rewrite length_update : sepFormula.

  Ltac firstnify :=
    match goal with
      | [ col := _ |- context C[match ?E with nil => nil | a :: l => a :: firstn ?N l end] ] =>
        let G := context C[firstn (S N) E] in
          change G; unfold col; rewrite moveS'
    end.

  Ltac t := pre; prep; evalu; repeat (my_descend; my_step); my_descend; try nomega; try firstnify;
    eauto using inBounds_up.
  Ltac u := solve [ t ].

  Opaque mult.

  Lemma use_inputOk : forall V es pos len n,
    inputOk V es
    -> In (Input pos len) es
    -> n = wordToNat (sel V "len")
    -> (wordToNat (sel V pos) + wordToNat (sel V len) <= n)%nat.
    intros; subst; eapply Forall_forall in H0; eauto; auto.
  Qed.

  Hint Immediate use_inputOk.

  Section writeExps_correct.
    Variable mn : string.
    Variable im : LabelMap.t assert.
    Variable H : importsGlobal im.
    Variable ns : list string.
    Variable res : nat.

    Hypothesis not_rp : ~In "rp" ns.
    Hypothesis included : incl baseVars ns.
    Hypothesis reserved : (res >= 10)%nat.
    Hypothesis wellFormed : wfExps ns es.

    Hypothesis weakenPre : (forall a V V', (forall x, x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> sel V x = sel V' x)
    -> invPre a V ===> invPre a V').

    Hypothesis weakenPost : (forall a V V' R, (forall x, x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> sel V x = sel V' x)
    -> invPost a V R = invPost a V' R).

    Hypothesis copy : "array8"!"copy" ~~ im ~~> ArrayOps.copyS.

    Ltac v := abstract t.

    Lemma writeExp_correct_vcs : forall e col pre,
      wfExp ns e
      -> In e es
      -> (forall specs st,
        interp specs (pre st)
        -> interp specs (winv col ns res st))
      -> vcs (VerifCond (toCmd (writeExp col e) mn (im := im) H ns res pre)).
      destruct e; wrap0.

      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
    Qed.

    Lemma writeExp_correct_post : forall e col pre,
      wfExp ns e
      -> In e es
      -> (forall specs st,
        interp specs (pre st)
        -> interp specs (winv col ns res st))
      -> forall specs st,
        interp specs (Postcondition (toCmd (writeExp col e) mn (im := im) H ns res pre) st)
        -> interp specs (winv col ns res st).
      destruct e; wrap0.

      v.
      v.
      v.
    Qed.

    Lemma wfExps_inv2 : forall ns e es,
      wfExps ns (e :: es)
      -> wfExps ns es.
      inversion 1; auto.
    Qed.

    Hint Immediate wfExps_inv1 wfExps_inv2.

    Hypothesis length_es : length es = length sch.
    Hypothesis goodSize_sch : goodSize (length sch).

    Ltac split_IH := intros;
      match goal with
        | [ IH : forall pre : settings * state -> PropX _ _, _ |- _ ] =>
          generalize (fun a b c d e => proj1 (IH a b c d e));
            generalize (fun a b c d e => proj2 (IH a b c d e));
              clear IH; intros
      end;
      match goal with
        | [ H : incl (_ :: _) _ |- _ ] => apply incl_peel in H; destruct H
      end.

    Ltac basic_eauto :=
      match goal with
        | [ |- forall x, _ ] => idtac
        | [ |- Logic.ex _ ] => idtac
        | _ => simpl in *; eauto
      end.

    Lemma inBounds_move : forall ilen n m ls,
      inBounds ilen (firstn (S (n - S m)) ls)
      -> (S m <= n)%nat
      -> inBounds ilen (firstn (n - m) ls).
      intros; replace (n - m) with (S (n - S m)) by omega; auto.
    Qed.

    Hint Immediate inBounds_move.

    Lemma inBounds_wiggle : forall ilen n m col ls,
      inBounds ilen (firstn m ls)
      -> col = m - S n
      -> (S n <= m)%nat
      -> inBounds ilen (match ls with nil => nil | x :: ls' => x :: firstn (n + col) ls' end).
      intros; subst; replace m with (S (n + (m - S n))) in * |- by omega; auto.
    Qed.

    Hint Immediate inBounds_wiggle.

    Hint Rewrite Minus.le_plus_minus_r using (simpl in *; omega) : sepFormula.

    Ltac use_IH :=
      match goal with
        | [ col := ?E |- _ ] =>
          match goal with
            | [ |- appcontext[writeExps (S col)] ] =>
              change (writeExps (S col)) with (writeExps (S E))
          end; rewrite moveS by assumption;
          match goal with
            | [ H : forall x : settings * state -> PropX _ _, _ |- _ ] =>
              apply H; basic_eauto
          end

        | [ H : interp _ (Postcondition (toCmd (writeExps (S ?col) _) _ _ _ _ _) _),
            H' : forall a, wfExps _ _ -> _ |- _ ] =>
          unfold col in H; rewrite moveS in H by (simpl in *; omega);
            eapply H' in H; basic_eauto

        | _ => eapply writeExp_correct_vcs; basic_eauto
        | [ H : interp _ (Postcondition _ _) |- _ ] => eapply writeExp_correct_post in H; basic_eauto
      end; pre.

    Ltac we := repeat use_IH; t.
    Ltac swe := solve [ we ].
    Ltac awe := abstract we.

    Lemma writeExps_correct : forall es0 pre,
      wfExps ns es0
      -> incl es0 es
      -> (length es0 <= length es)%nat
      -> let col := length es - length es0 in
        (forall specs st,
          interp specs (pre st)
          -> interp specs (winv col ns res st))
        -> vcs (VerifCond (toCmd (writeExps col es0) mn (im := im) H ns res pre))
        /\ (forall specs st,
          interp specs (Postcondition (toCmd (writeExps col es0) mn (im := im) H ns res pre) st)
          -> interp specs (winv (length es0 + col) ns res st)).
      induction es0.

      wrap0.

      split_IH.

      wrap0.
      wrap0.

      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
    Qed.
  End writeExps_correct.

  Notation InsertVcs := (fun im ns res =>
    (~In "rp" ns) :: incl baseVars ns
    :: (forall a V V', (forall x, x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> sel V x = sel V' x)
      -> invPre a V ===> invPre a V')
    :: (forall a V V' R, (forall x, x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> sel V x = sel V' x)
      -> invPost a V R = invPost a V' R)
    :: (res >= 10)%nat
    :: (bufSize >= natToW 2)
    :: goodSize (2 + length sch + length sch)
    :: goodSize (4 * wordToNat bufSize)
    :: wfExps ns es
    :: "buffers"!"bmalloc" ~~ im ~~> bmallocS
    :: "malloc"!"malloc" ~~ im ~~> mallocS
    :: "array8"!"copy" ~~ im ~~> ArrayOps.copyS
    :: (length es = length sch)
    :: goodSize (length sch)
    :: nil).

  Hint Immediate incl_refl.

  Lemma div2_double : forall n, div2 (n + n) = n.
    apply div2_double'.
  Qed.

  Hint Rewrite div2_double : sepFormula.
 
  Lemma four_duh : forall n,
    goodSize (4 * wordToNat bufSize)
    -> n = wordToNat bufSize * 4
    -> n = wordToNat (natToW 4 ^* bufSize).
    intros; subst.
    rewrite wordToNat_wmult.
    change (wordToNat (natToW 4)) with 4; omega.
    auto.
  Qed.

  Hint Immediate four_duh.

  Lemma inBounds_nil : forall n, inBounds n nil.
    intros; hnf; auto.
  Qed.

  Hint Immediate inBounds_nil.

  Lemma firstn_all : forall A (ls : list A) n,
    n = length ls
    -> firstn n ls = ls.
    intros; subst; induction ls; simpl; intuition.
  Qed.

  Hint Rewrite firstn_all using congruence : sepFormula.

  Ltac writeExps' :=
    try match goal with
          | [ H : ?E = _ |- match ?E with None => _ | _ => _ end ] =>
            rewrite H; post
        end;
    edestruct writeExps_correct; repeat rewrite Minus.minus_diag, Plus.plus_0_r in *;
      try match goal with
            | [ |- vcs _ ] => eauto
            | [ H : interp _ (Postcondition _ _), H' : _ |- _ ] => apply H' in H
          end; eauto; try rewrite Minus.minus_diag in *.

  Ltac writeExps :=
    match goal with
      | [ |- context[writeExps] ] => writeExps'
      | [ _ : context[writeExps] |- _ ] => writeExps'
    end.

  Lemma prove_freeable8 : forall p size,
    freeable p (wordToNat size)
    -> goodSize (4 * wordToNat size)
    -> freeable8 p (wordToNat (natToW 4 ^* size)).
    intros; rewrite wordToNat_wmult; change (wordToNat (natToW 4)) with 4; hnf; eauto.
  Qed.

  Hint Immediate prove_freeable8.

  Ltac i := abstract (try writeExps; t).

  Definition Insert : chunk.
    refine (WrapC Insert'
      invar
      invar
      InsertVcs
      _ _).

    wrap0; i.

    wrap0.

    i.
    i.
    i.
    i.
    i.
    i.
    i.
    i.
    i.
    i.
    i.
    i.
    i.
    i.
    i.
    i.
    i.
  Defined.

End Insert.
