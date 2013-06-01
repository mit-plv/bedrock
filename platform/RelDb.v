Require Import AutoSep Wrap StringOps Malloc ArrayOps Bags SinglyLinkedList.

Set Implicit Arguments.


(** * Database schemas and query/command types *)

Definition schema := list string.

Inductive exp :=
| Const (s : string)
| Input (pos len : string).

Definition wfExp (e : exp) :=
  match e with
    | Const s => goodSize (String.length s)
    | Input _ _ => True
  end.

Definition wfExps := List.Forall wfExp.

Section preds.
  Open Scope Sep_scope.

  Definition posl := map (@fst W W).
  Definition lenl := map (@snd W W).

  Definition inBounds (len : W) (cols : list (W * W)) :=
    List.Forall (fun col => wordToNat (fst col) + wordToNat (snd col) <= wordToNat len)%nat cols.

  Variable s : schema.

  Definition row (p : W) :=
    Ex buf, Ex len, Ex cols, Ex bs,
    (p ==*> buf, len) * array (posl cols) (p ^+ $8) * array (lenl cols) (p ^+ $(length s * 4 + 8)) * array8 bs buf
    * [| length bs = wordToNat len |] * [| length cols = length s |] * [| inBounds len cols |]
    * [| p <> 0 |] * [| freeable p (length s * 4 + length s * 4 + 8) |]
    * [| buf <> 0 |] * [| freeable buf (length bs) |].

  Theorem row_fwd : forall p,
    row p ===> Ex buf, Ex len, Ex cols, Ex bs,
    (p ==*> buf, len) * array (posl cols) (p ^+ $8) * array (lenl cols) (p ^+ $(length s * 4 + 8)) * array8 bs buf
    * [| length bs = wordToNat len |] * [| length cols = length s |] * [| inBounds len cols |]
    * [| p <> 0 |] * [| freeable p (length s * 4 + length s * 4 + 8) |]
    * [| buf <> 0 |] * [| freeable buf (length bs) |].
    unfold row; sepLemma.
  Qed.

  Theorem row_bwd : forall p,
    (Ex buf, Ex len, Ex cols, Ex bs,
    (p ==*> buf, len) * array (posl cols) (p ^+ $8) * array (lenl cols) (p ^+ $(length s * 4 + 8)) * array8 bs buf
    * [| length bs = wordToNat len |] * [| length cols = length s |] * [| inBounds len cols |]
    * [| p <> 0 |] * [| freeable p (length s * 4 + length s * 4 + 8) |]
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

Definition inputOk (V : vals) :=
  List.Forall (fun e => match e with
                          | Const _ => True
                          | Input pos len => wordToNat (sel V pos) + wordToNat (sel V len) < wordToNat (V "len")
                        end)%nat.


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
        (fun (p : list B * A) V => array8 (fst p) (V "buf")
          * Ex cols, (V "row" ==*> V "ibuf", V "ilen") * array (posl cols) (V "row" ^+ $8)
          * array (lenl cols) (V "row" ^+ $(length sch * 4 + 8))
          * [| length (fst p) = wordToNat (V "len") |] * [| length cols = length sch |]
          * [| V "row" <> 0 |] * [| freeable (V "row") (length sch * 4 + length sch * 4 + 8) |]
          * [| V "ibuf" <> 0 |] * [| freeable (V "ibuf") (wordToNat (V "ilen")) |]
          * [| inBounds (V "ilen") (firstn col cols) |] * invPre (snd p) V)%Sep
        (fun (p : list B * A) V R => array8 (fst p) (V "buf")
          * Ex cols, (V "row" ==*> V "ibuf", V "ilen") * array (posl cols) (V "row" ^+ $8)
          * array (lenl cols) (V "row" ^+ $(length sch + 8))
          * [| length cols = length sch |]
          * [| inBounds (V "ilen") cols |] * invPost (snd p) V R)%Sep
      | Input _ _ => Diverge
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
        "row" + (col * 4 + 8)%nat *<- "ipos";;
        "row" + (col * 4 + length sch * 4 + 8)%nat *<- lengthOf e;;
        "tmp" <- "ilen" - "ipos";;
        If ("tmp" < lengthOf e) {
          "overflowed" <- 1
        } else {
          "ipos" <- "ipos" + lengthOf e;;
          writeExps (S col) es'
        }
    end%SP.

  Definition Insert' : chunk := (
    "ibuf" <-- Call "malloc"!"malloc"(0, bufSize)
    [Al a : A, Al bs,
      PRE[V, R] R =?> wordToNat bufSize * [| R <> 0 |] * [| freeable R (wordToNat bufSize) |]
        * array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * [| length bs = wordToNat (V "len") |] * [| inputOk V es |] * invPre a V
      POST[R'] array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * invPost a V R'];;

    "row" <-- Call "malloc"!"malloc"(0, (length sch * 4 + length sch * 4 + 8)%nat)
    [Al a : A, Al bs,
      PRE[V, R] V "ibuf" =?> wordToNat bufSize * [| V "ibuf" <> 0 |]
        * [| freeable (V "ibuf") (wordToNat bufSize) |]
        * R =?> (length sch * 4 + length sch * 4 + 8)%nat * [| R <> 0 |]
        * [| freeable R (length sch * 4 + length sch * 4 + 8)%nat |]
        * array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * [| length bs = wordToNat (V "len") |] * [| inputOk V es |] * invPre a V
      POST[R'] array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * invPost a V R'];;

    "row" *<- "ibuf";;
    "ilen" <- (length sch * 4 + length sch * 4 + 8)%nat;;
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

  Definition baseVars := "ibuf" :: "row" :: "ilen" :: "overflowed" :: "tmp" :: "ipos" :: "buf" :: "len" :: nil.

  Notation InsertVcs := (fun im ns res =>
    (~In "rp" ns) :: incl baseVars ns
    :: (forall a V V', (forall x, x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> sel V x = sel V' x)
      -> invPre a V ===> invPre a V')
    :: (forall a V V' R, (forall x, x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> sel V x = sel V' x)
      -> invPost a V R = invPost a V' R)
    :: (res >= 7)%nat
    :: wfExps es
    :: "malloc"!"malloc" ~~ im ~~> mallocS
    :: nil).

  Opaque mult.

  Definition Insert : chunk.
    refine (WrapC Insert'
      invar
      invar
      InsertVcs
      _ _).

    wrap0.
    post.

    Lemma incl_peel : forall A (x : A) ls ls',
      incl (x :: ls) ls'
      -> In x ls' /\ incl ls ls'.
      unfold incl; intuition.
    Qed.

    repeat match goal with
             | [ H : incl nil _ |- _ ] => clear H
             | [ H : incl _ _ |- _ ] => apply incl_peel in H; destruct H
           end.

    clear H10.
    clear_fancy.

    unfold lvalIn, regInL, immInR in *.
    prep_locals.

    Lemma invPre_sel : forall a V, invPre a (sel V) = invPre a V.
      auto.
    Qed.

    Lemma invPost_sel : forall a V R, invPost a (sel V) R = invPost a V R.
      auto.
    Qed.

    Lemma inputOk_sel : forall V es, inputOk (sel V) es = inputOk V es.
      auto.
    Qed.

    rewrite invPre_sel in *.
    rewrite inputOk_sel in *.
    evaluate hints.
    repeat match goal with
             | [ H : In _ _ |- _ ] => clear H
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
           end.
    destruct st; simpl in *.
    descend.

    match goal with
      | [ _ : interp _ (?P ?x) |- interp _ (?Q ?x) ] =>
        match P with
          | context[locals _ ?V ?res _] =>
            match Q with
              | context[locals _ ?V' res _] => equate V' V; descend
            end
        end
    end.

    rewrite invPre_sel; rewrite inputOk_sel.
    autorewrite with sepFormula in *.
    step hints.
    admit.
    step hints.
    apply himp_star_frame; try reflexivity.
    apply H6.
    descend.
    descend; step hints.
    descend; step hints.
    descend; step hints.
    descend; step hints.
    unfold natToW in *; congruence.
    do 2 rewrite invPost_sel.
    descend; step hints.
    apply himp_refl.
    apply H7.
    descend.

    admit.
  Defined.

End Insert.
