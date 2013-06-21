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
    * [| buf <> 0 |] * [| freeable buf (length bs) |].

  Theorem row_fwd : forall p,
    row p ===> Ex buf, Ex len, Ex cols, Ex bs,
    (p ==*> buf, len) * array (posl cols) (p ^+ $8) * array (lenl cols) (p ^+ $8 ^+ $(length s * 4)) * array8 bs buf
    * [| length bs = wordToNat len |] * [| length cols = length s |] * [| inBounds len cols |]
    * [| p <> 0 |] * [| freeable p (2 + length s + length s) |]
    * [| buf <> 0 |] * [| freeable buf (length bs) |].
    unfold row; sepLemma.
  Qed.

  Theorem row_bwd : forall p,
    (Ex buf, Ex len, Ex cols, Ex bs,
    (p ==*> buf, len) * array (posl cols) (p ^+ $8) * array (lenl cols) (p ^+ $8 ^+ $(length s * 4)) * array8 bs buf
    * [| length bs = wordToNat len |] * [| length cols = length s |] * [| inBounds len cols |]
    * [| p <> 0 |] * [| freeable p (2 + length s + length s) |]
    * [| buf <> 0 |] * [| freeable buf (length bs) |]) ===> row p.
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

Definition hints : TacPackage.
  prepare (nil_fwd, cons_fwd, table_fwd, row_fwd)
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
          * [| V "ibuf" <> 0 |] * [| freeable (V "ibuf") (wordToNat (V "ilen")) |]
          * [| inBounds (V "ilen") (firstn col cols) |] * [| inputOk V es |] * invPre (snd p) V)%Sep
        (fun (p : list B * A) V R => array8 (fst p) (V "buf") * mallocHeap 0 * table sch tptr
          * Ex cols, (V "row" ==*> V "ibuf", V "ilen") * array (posl cols) (V "row" ^+ $8)
          * array (lenl cols) (V "row" ^+ $8 ^+ $(length sch * 4))
          * [| length cols = length sch |]
          * [| inBounds (V "ilen") cols |] * invPost (snd p) V R)%Sep
      | Input start len =>
        "tmp" <- "ilen" - "ipos";;
        If (len < "tmp") {
          Call "array8"!"copy"("ibuf", "ipos", "buf", start, len)
          [Al a : A, Al bs, Al bsI,
            PRE[V] array8 bs (V "buf") * table sch tptr
              * [| V "ipos" <= V "ilen" |]%word
              * array8 bsI (V "ibuf") * [| length bsI = wordToNat (V "ilen") |] * [| V "ibuf" <> 0 |]
              * [| freeable (V "ibuf") (wordToNat (V "ilen")) |]
              * Ex cols, (V "row" ==*> V "ibuf", V "ilen") * array (posl cols) (V "row" ^+ $8)
              * array (lenl cols) (V "row" ^+ $8 ^+ $(length sch * 4))
              * [| length bs = wordToNat (V "len") |] * [| length cols = length sch |]
              * [| V "row" <> 0 |] * [| freeable (V "row") (2 + length sch + length sch) |]
              * [| V "ibuf" <> 0 |] * [| freeable (V "ibuf") (wordToNat (V "ilen")) |]
              * [| inBounds (V "ilen") (firstn col cols) |] * [| inputOk V es |] * invPre a V * mallocHeap 0
            POST[R] Ex bsI', array8 bs (V "buf") * table sch tptr
              * array8 bsI' (V "ibuf") * [| length bsI' = wordToNat (V "ilen") |]
              * Ex cols, (V "row" ==*> V "ibuf", V "ilen") * array (posl cols) (V "row" ^+ $8)
              * array (lenl cols) (V "row" ^+ $8 ^+ $(length sch * 4))
              * [| length cols = length sch |]
              * [| inBounds (V "ilen") cols |] * mallocHeap 0 * invPost a V R]
        } else {
          "overflowed" <- 1
        }
    end%SP.

  Definition lengthOf (e : exp) : rvalue' :=
    match e with
      | Const s => String.length s
      | Input _ len => len
    end%SP.

  Fixpoint writeExps (col : nat) (es : list exp) {struct es} : chunk :=
    match es with
      | nil => Skip
      | e :: es' =>
        writeExp col e;;
        "tmp" <- "row" + 8;;
        "tmp" + (4 * col)%nat *<- "ipos";;
        "tmp" <- "tmp" + (length sch * 4)%nat;;
        "tmp" + (4 * col)%nat *<- lengthOf e;;
        "tmp" <- "ilen" - "ipos";;
        If ("tmp" < lengthOf e) {
          "overflowed" <- 1
        } else {
          "ipos" <- "ipos" + lengthOf e;;
          writeExps (S col) es'
        }
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
    :: wfExps es
    :: "buffers"!"bmalloc" ~~ im ~~> bmallocS
    :: "malloc"!"malloc" ~~ im ~~> mallocS
    :: "array8"!"copy" ~~ im ~~> ArrayOps.copyS
    :: nil).

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
         end; clear_fancy; unfold lvalIn, regInL, immInR in *; prep_locals;
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
      | _ => evaluate hints
    end;
    repeat match goal with
             | [ H : @In string _ _ |- _ ] => clear H
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
             | [ H : evalCond _ _ _ _ _ = _ |- _ ] => clear H
           end; state_apart;
    fold (@firstn (W * W)) in *; fold (@length (W * W)) in *.

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

  Ltac my_cancel :=
    match goal with
      | [ |- interp _ (?pre ---> ?post)%PropX ] =>
        match post with
          | context[locals ?ns ?vs ?avail _] =>
            match pre with
              | context[excessStack _ ns avail ?ns' ?avail'] =>
                match avail' with
                  | avail => fail 1
                  | _ =>
                    match pre with
                      | context[locals ns ?vs' 0 ?sp] =>
                        match goal with
                          | [ _ : _ = sp |- _ ] => fail 1
                          | _ => equate vs vs';
                            let offset := eval simpl in (4 * List.length ns) in
                              rewrite (create_locals_return ns' avail' ns avail offset);
                                assert (ok_return ns ns' avail avail' offset)%nat by (split; [
                                  simpl; omega
                                  | reflexivity ] ); autorewrite with sepFormula
                        end
                    end
                end
            end
        end
    end;
    cancel hints.

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
  
  Ltac updify :=
    match goal with
      | [ |- himp _ ?pre _ ] =>
        match pre with
          | context[Array.upd (posl _) _ _] =>
            erewrite upd_posl; erewrite upd_lenl
          end
    end.

  Ltac my_step := (unfold natToW in *; congruence) || weaken_invPre || weaken_invPost
    || ((my_cancel || (try updify; step hints)); fold (@firstn (W * W))).

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

  Ltac pre := try discriminate; try prove_Himp;
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

  Ltac t := pre; prep; evalu; repeat (my_descend; my_step); my_descend; try nomega; eauto using inBounds_up.
  Ltac u := solve [ t ].

  Opaque mult.

  Definition winv (col : nat) :=
    (Al a : A, Al bs, Al bsI,
      PRE[V] array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * array8 bsI (V "ibuf") * [| length bsI = wordToNat (V "ilen") |]
        * [| V "ipos" <= V "ilen" |]
        * Ex cols, (V "row" ==*> V "ibuf", V "ilen") * array (posl cols) (V "row" ^+ $8)
        * array (lenl cols) (V "row" ^+ $8 ^+ $(length sch * 4))
        * [| length bs = wordToNat (V "len") |] * [| length cols = length sch |]
        * [| V "row" <> 0 |] * [| freeable (V "row") (2 + length sch + length sch) |]
        * [| V "ibuf" <> 0 |] * [| freeable (V "ibuf") (wordToNat (V "ilen")) |]
        * [| inBounds (V "ilen") (firstn col cols) |] * [| inputOk V es |] * invPre a V
      POST[R] Ex bsI', array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * array8 bsI' (V "ibuf") * [| length bsI' = wordToNat (V "ilen") |]
        * (Ex cols, (V "row" ==*> V "ibuf", V "ilen") * array (posl cols) (V "row" ^+ $8)
          * array (lenl cols) (V "row" ^+ $8 ^+ $(length sch * 4))
          * [| length cols = length sch |]
          * [| inBounds (V "ilen") cols |]) * invPost a V R) true (fun w => w).

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

    Lemma writeExp_correct : forall e col pre,
      wfExp ns e
      -> In e es
      -> (forall specs st,
        interp specs (pre st)
        -> interp specs (winv col ns res st))
      -> vcs (VerifCond (toCmd (writeExp col e) mn (im := im) H ns res pre))
      /\ (forall specs st,
        interp specs (Postcondition (toCmd (writeExp col e) mn (im := im) H ns res pre) st)
        -> interp specs (winv col ns res st)).
    Admitted.
      (*destruct e; wrap0; try match goal with
                             | [ |- vcs _ ] => wrap0
                           end.
    
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
      v.
      v.
    Qed.*)

    Lemma wfExps_inv2 : forall ns e es,
      wfExps ns (e :: es)
      -> wfExps ns es.
      inversion 1; auto.
    Qed.

    Hint Immediate wfExps_inv1 wfExps_inv2.

    Hypothesis length_es : length es = length sch.
    Hypothesis goodSize_sch : goodSize (length sch).

    Ltac split_IH :=
      match goal with
        | [ IH : forall pre : settings * state -> PropX _ _, _ |- _ ] =>
          generalize (fun a b c d e => proj1 (IH a b c d e));
            generalize (fun a b c d e => proj2 (IH a b c d e));
              clear IH; intros
      end;
      match goal with
        | [ H : incl (_ :: _) _ |- _ ] => apply incl_peel in H; destruct H
      end;
      match goal with
        | [ H : _ |- _ ] => eapply writeExp_correct in H; eauto; destruct H
      end.

    Ltac use_IH :=
      match goal with
        | [ col := ?E |- _ ] =>
          match goal with
            | [ |- appcontext[writeExps (S col)] ] =>
              change (writeExps (S col)) with (writeExps (S E))
          end; rewrite moveS by assumption;
          match goal with
            | [ H : forall x : settings * state -> PropX _ _, _ |- _ ] =>
              apply H; match goal with
                         | [ |- forall x, _ ] => idtac
                         | _ => simpl in *; eauto
                       end
          end
      end.

    Ltac we := try use_IH; t.
    Ltac swe := solve [ we ].

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

      intros.
      split_IH.

      wrap0.
      wrap0.

      swe.
      swe.
      swe.
      swe.
      swe.
      swe.
      swe.
      swe.
      swe.

      admit.
      admit.
    Qed.
  End writeExps_correct.
 
  Definition Insert : chunk.
    refine (WrapC Insert'
      invar
      invar
      InsertVcs
      _ _).

    wrap0; u.

    wrap0.

    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    admit.
    admit.
    admit.
    u.
    u.
    u.
    u.
  Defined.

End Insert.
