Require Import AutoSep Wrap StringOps Malloc ArrayOps Buffers Bags.
Require Import SinglyLinkedList ListSegment RelDb.

Set Implicit Arguments.


(** * Iterating over matching rows of a table *)

Opaque mult.
Local Infix ";;" := SimpleSeq : SP_scope.

Section Select.
  Variable A : Type.
  Variable invPre : A -> vals -> HProp.
  Variable invPost : A -> vals -> W -> HProp.

  Variable tptr : W.
  Variable sch : schema.

  (* Store a pointer to the current linked list node and actual row data, respectively,
   * in these variables. *)
  Variables rw data : string.

  (* Test to use in filtering rows *)
  Variable cond : condition.

  (* Run this command on every matching row. *)
  Variable body : (W -> W -> HProp) -> chunk.
  (* The argument to [body] is an invariant to preserve.
   * Its inputs are the values of [rw] and [data]. *)

  Section compileEquality.
    (* One field test, storing Boolean result in "matched" *)
    Definition compileEquality (e : equality) : chunk :=
      match resolve sch (fst e) with
        | None => Fail
        | Some offset =>
          "tmp" <- data;;
          "ibuf" <-* "tmp";;
          "ilen" <-* "tmp" + 4;;

          Assert [Al bs, Al a : A, Al head, Al done, Al remaining, Al rcols, Al rbs,
            PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |]
              * [| inputOk V (exps cond) |]
              * [| V rw <> 0 |] * tptr =*> head * lseg done head (V rw) * sll (V data :: remaining) (V rw)
              * rows sch head remaining * rows sch head done * invPre a V
              * (V data ==*> V "ibuf", V "ilen") * array (posl rcols) (V data ^+ $8)
              * array (lenl rcols) (V data ^+ $8 ^+ $(length sch * 4)) * array8 rbs (V "ibuf")
              * [| length rbs = wordToNat (V "ilen") |] * [| length rcols = length sch |]
              * [| inBounds (V "ilen") rcols |] * [| V data <> 0 |]
              * [| freeable (V data) (2 + length sch + length sch) |]
              * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (length rbs) |]
              * [| natToW offset < natToW (length (posl rcols)) |]%word
            POST[R] array8 bs (V "buf") * invPost a V R];;

          "tmp" <- data + 8;;
          "ipos" <-* "tmp" + (4 * offset)%nat;;

          Assert [Al bs, Al a : A, Al head, Al done, Al remaining, Al rcols, Al rbs,
            PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |]
              * [| inputOk V (exps cond) |]
              * [| V rw <> 0 |] * tptr =*> head * lseg done head (V rw) * sll (V data :: remaining) (V rw)
              * rows sch head remaining * rows sch head done * invPre a V
              * (V data ==*> V "ibuf", V "ilen") * array (posl rcols) (V data ^+ $8)
              * array (lenl rcols) (V data ^+ $8 ^+ $(length sch * 4)) * array8 rbs (V "ibuf")
              * [| length rbs = wordToNat (V "ilen") |] * [| length rcols = length sch |]
              * [| inBounds (V "ilen") rcols |] * [| V data <> 0 |]
              * [| freeable (V data) (2 + length sch + length sch) |]
              * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (length rbs) |]
              * [| V "ipos" = Array.selN (posl rcols) offset |]
              * [| natToW offset < natToW (length (lenl rcols)) |]%word
            POST[R] array8 bs (V "buf") * invPost a V R];;

          "tmp" <- data + 8;;
          "tmp" <- "tmp" + (length sch * 4)%nat;;
          "tmp" <-* "tmp" + (4 * offset)%nat;;

          Assert [Al bs, Al a : A, Al head, Al done, Al remaining, Al rcols, Al rbs,
            PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |]
              * [| inputOk V (exps cond) |]
              * [| V rw <> 0 |] * tptr =*> head * lseg done head (V rw) * sll (V data :: remaining) (V rw)
              * rows sch head remaining * rows sch head done * invPre a V
              * (V data ==*> V "ibuf", V "ilen") * array (posl rcols) (V data ^+ $8)
              * array (lenl rcols) (V data ^+ $8 ^+ $(length sch * 4)) * array8 rbs (V "ibuf")
              * [| length rbs = wordToNat (V "ilen") |] * [| length rcols = length sch |]
              * [| inBounds (V "ilen") rcols |] * [| V data <> 0 |]
              * [| freeable (V data) (2 + length sch + length sch) |]
              * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (length rbs) |]
              * [| V "ipos" = Array.selN (posl rcols) offset |]
              * [| V "tmp" = Array.selN (lenl rcols) offset |]
            POST[R] array8 bs (V "buf") * invPost a V R];;

          match snd e with
            | Const s =>
              If ("tmp" <> String.length s) {
                (* Field value has wrong length to match. *)
                "matched" <- 0
              } else {
                StringEq "ibuf" "ilen" "ipos" "matched" s
                (fun (a_bs : A * list B) V => array8 (snd a_bs) (V "buf")
                  * [| length (snd a_bs) = wordToNat (V "len") |]
                  * [| inputOk V (exps cond) |]
                  * Ex head, Ex done, Ex remaining, Ex rcols,
                    [| V rw <> 0 |] * tptr =*> head * lseg done head (V rw)
                    * sll (V data :: remaining) (V rw)
                    * rows sch head remaining * rows sch head done
                    * invPre (fst a_bs) V
                    * (V data ==*> V "ibuf", V "ilen") * array (posl rcols) (V data ^+ $8)
                    * array (lenl rcols) (V data ^+ $8 ^+ $(length sch * 4))
                    * [| length rcols = length sch |]
                    * [| inBounds (V "ilen") rcols |] * [| V data <> 0 |]
                    * [| freeable (V data) (2 + length sch + length sch) |]
                    * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (wordToNat (V "ilen")) |]
                    * [| V "ipos" = Array.selN (posl rcols) offset |])%Sep
                (fun _ a_bs V R => array8 (snd a_bs) (V "buf") * invPost (fst a_bs) V R)%Sep
              }
            | Input pos len =>
              If ("tmp" <> len) {
                "matched" <- 0
              } else {
                "matched" <-- Call "array8"!"equal"("ibuf", "ipos", "buf", pos, len)
                [Al bs, Al a : A, Al head, Al done, Al remaining,
                  PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |]
                    * [| inputOk V (exps cond) |]
                    * [| V rw <> 0 |] * tptr =*> head * lseg done head (V rw)
                    * sll (V data :: remaining) (V rw)
                    * rows sch head remaining * rows sch head done * row sch (V data) * invPre a V
                  POST[R] array8 bs (V "buf") * invPost a V R]
              }
          end
      end%SP.

    Variable mn : string.
    Variable im : LabelMap.t assert.
    Variable H : importsGlobal im.
    Variable ns : list string.
    Variable res : nat.

    Definition eqinv' := Al bs, Al a : A, Al head, Al done, Al remaining,
      PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |]
        * [| inputOk V (exps cond) |]
        * [| V rw <> 0 |] * tptr =*> head * lseg done head (V rw) * sll (V data :: remaining) (V rw)
        * rows sch head remaining * rows sch head done * row sch (V data) * invPre a V
      POST[R] array8 bs (V "buf") * invPost a V R.

    Definition eqinv := eqinv' true (fun w => w).

    Hypothesis not_rp : ~In "rp" ns.
    Hypothesis included : incl baseVars ns.
    Hypothesis reserved : (res >= 10)%nat.
    Hypothesis wellFormed : wfEqualities ns sch cond.

    Hypothesis weakenPre : (forall a V V', (forall x, x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> x <> "matched" -> sel V x = sel V' x)
    -> invPre a V ===> invPre a V').

    Hypothesis weakenPost : (forall a V V' R, (forall x, x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> x <> "matched" -> sel V x = sel V' x)
    -> invPost a V R = invPost a V' R).

    Lemma resolve_ok : forall e s,
      wfEquality ns s e
      -> exists offset, resolve s (fst e) = Some offset
        /\ (offset < length s)%nat.
      unfold wfEquality; induction s; simpl; intuition subst;
        match goal with
          | [ |- context[if ?E then _ else _] ] => destruct E
        end; intuition eauto.
      destruct H1; intuition idtac.
      rewrite H3; eauto.
    Qed.

    Hypothesis matched_rw : "matched" <> rw.
    Hypothesis matched_data : "matched" <> data.

    Lemma compileEquality_post : forall e pre,
      wfEquality ns sch e
      -> (forall specs st,
        interp specs (pre st)
        -> interp specs (eqinv ns res st))
      -> forall specs st,
        interp specs (Postcondition (toCmd (compileEquality e) mn (im := im) H ns res pre) st)
        -> interp specs (eqinv ns res st).
      unfold compileEquality; intros.
      match goal with
        | [ H : _ |- _ ] => destruct (resolve_ok H); intuition idtac; destruct H
      end.
      match goal with
        | [ H : resolve _ _ = _ |- _ ] => rewrite H in *
      end.
      destruct e as [ ? [ ] ]; simpl in *; intuition idtac.

      v.
      v.
    Qed.

    Hypothesis equal : "array8"!"equal" ~~ im ~~> ArrayOps.equalS.

    Hypothesis data_rp : data <> "rp".
    Hypothesis data_ibuf : data <> "ibuf".
    Hypothesis data_ipos : data <> "ipos".
    Hypothesis data_ilen : data <> "ilen".
    Hypothesis data_tmp : data <> "tmp".
    Hypothesis data_ns : In data ns.

    Hypothesis rw_rp : rw <> "rp".
    Hypothesis rw_ibuf : rw <> "ibuf".
    Hypothesis rw_ipos : rw <> "ipos".
    Hypothesis rw_ilen : rw <> "ilen".
    Hypothesis rw_tmp : rw <> "tmp".

    Hypothesis goodSize_sch : goodSize (length sch).

    Lemma length_posl : forall ls, length (posl ls) = length ls.
      clear; induction ls; simpl; intuition.
    Qed.

    Lemma length_lenl : forall ls, length (lenl ls) = length ls.
      clear; induction ls; simpl; intuition.
    Qed.

    Lemma length_match : forall x (ls : list (W * W)),
      (x < length sch)%nat
      -> length ls = length sch
      -> natToW x < natToW (Datatypes.length ls).
      generalize goodSize_sch; clear; intros.
      pre_nomega.
      rewrite wordToNat_natToWord_idempotent.
      rewrite wordToNat_natToWord_idempotent.
      congruence.
      rewrite H0; assumption.
      change (goodSize x); eapply goodSize_weaken; eauto.
    Qed.

    Lemma length_match_posl : forall x ls,
      (x < length sch)%nat
      -> length ls = length sch
      -> natToW x < natToW (Datatypes.length (posl ls)).
      intros; rewrite length_posl; auto using length_match.
    Qed.

    Lemma length_match_lenl : forall x ls,
      (x < length sch)%nat
      -> length ls = length sch
      -> natToW x < natToW (Datatypes.length (lenl ls)).
      intros; rewrite length_lenl; auto using length_match.
    Qed.

    Hint Immediate length_match_posl length_match_lenl.

    Lemma selN_col : forall x ls,
      (x < length sch)%nat
      -> Array.sel ls (natToW x) = selN ls x.
      generalize goodSize_sch; clear; unfold Array.sel; intros; f_equal.
      apply wordToNat_natToWord_idempotent.
      change (goodSize x).
      eapply goodSize_weaken; eauto.
    Qed.

    Hint Immediate selN_col.

    Lemma inBounds_selN' : forall len cols,
      inBounds len cols
      -> forall col, (col < length cols)%nat
        -> (wordToNat (selN (posl cols) col) + wordToNat (selN (lenl cols) col) <= wordToNat len)%nat.
      clear; induction cols; inversion 1; simpl; intuition; destruct col; intuition.
    Qed.

    Lemma inBounds_selN : forall len cols,
      inBounds len cols
      -> forall col a b c, a = selN (posl cols) col
        -> b = selN (lenl cols) col
        -> c = wordToNat len
        -> (col < length cols)%nat
        -> (wordToNat a + wordToNat b <= c)%nat.
      intros; subst; eauto using inBounds_selN'.
    Qed.

    Hint Extern 1 (_ + _ <= _)%nat =>
      eapply inBounds_selN; try eassumption; (cbv beta; congruence).

    Lemma weakened_bound : forall pos cols x len,
      inBounds len cols
      -> pos = selN (posl cols) x
      -> (x < length cols)%nat
      -> pos <= len.
      clear; intros; subst.
      eapply inBounds_selN in H; try (reflexivity || eassumption).
      nomega.
    Qed.

    Hint Extern 1 (_ <= _) => eapply weakened_bound; try eassumption; (cbv beta; congruence).

    Hint Resolve use_inputOk.

    Lemma In_exps : forall s e c,
      In (s, e) c
      -> In e (exps c).
      clear; induction c; simpl; intuition (subst; auto).
    Qed.

    Hint Immediate In_exps.

    Lemma compileEquality_vcs : forall e pre,
      wfEquality ns sch e
      -> In e cond
      -> (forall specs st,
        interp specs (pre st)
        -> interp specs (eqinv ns res st))
      -> vcs (VerifCond (toCmd (compileEquality e) mn (im := im) H ns res pre)).
        unfold compileEquality; intros.
        match goal with
          | [ H : _ |- _ ] => destruct (resolve_ok H); intuition idtac; destruct H
        end.
        match goal with
          | [ H : resolve _ _ = _ |- _ ] => rewrite H in *
        end.
        wrap0.

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

        destruct e as [ ? [ ] ]; simpl in *; intuition idtac.
        
        repeat match goal with
                 | [ |- vcs _ ] => constructor
               end; intros.

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

        repeat match goal with
                 | [ |- vcs _ ] => constructor
               end; intros.

        (* Something bizarre is happening here, with [destruct] not clearing a hypothesis
         * within [propxFo]. *)
        apply simplify_fwd in H25.
        repeat match goal with
                 | [ H : simplify _ (Ex x, _) _ |- _ ] => destruct H
               end.
        apply simplify_bwd in H25.
        v.

        v.
        v.
        v.
        v.
    Qed.

    Fixpoint compileEqualities (es : condition) : chunk :=
      match es with
        | nil => "matched" <- 1
        | e :: es' =>
          compileEquality e;;
          If ("matched" = 0) {
            Skip
          } else {
            compileEqualities es'
          }
      end%SP.

    Lemma wfEqualities_inv1 : forall ns sch e es,
      wfEqualities ns sch (e :: es)
      -> wfEquality ns sch e.
      inversion 1; auto.
    Qed.

    Lemma wfEqualities_inv2 : forall ns sch e es,
      wfEqualities ns sch (e :: es)
      -> wfEqualities ns sch es.
      inversion 1; auto.
    Qed.

    Hint Immediate wfEqualities_inv1 wfEqualities_inv2.

    Lemma compileEqualities_post : forall es pre,
      wfEqualities ns sch es
      -> (forall specs st,
        interp specs (pre st)
        -> interp specs (eqinv ns res st))
      -> forall specs st,
        interp specs (Postcondition (toCmd (compileEqualities es) mn (im := im) H ns res pre) st)
        -> interp specs (eqinv ns res st).
      induction es; simpl; intuition idtac;
        (pre;
          repeat (match goal with
                    | [ H : interp _ (Postcondition (toCmd (compileEquality _) _ _ _ _ _) _) |- _ ] =>
                      apply compileEquality_post in H
                    | [ IH : forall pre : _ -> _, _, H : interp _ (Postcondition _ _) |- _ ] =>
                      apply IH in H
                  end; eauto; pre); t).
    Qed.

    Lemma compileEqualities_vcs : forall es pre,
      wfEqualities ns sch es
      -> incl es cond
      -> (forall specs st,
        interp specs (pre st)
        -> interp specs (eqinv ns res st))
      -> vcs (VerifCond (toCmd (compileEqualities es) mn (im := im) H ns res pre)).
      induction es; intros; try match goal with
                                  | [ H : incl _ cond |- _ ] => apply incl_peel in H
                                end; wrap0;
      (repeat (match goal with
                 | _ => apply compileEquality_vcs
                 | [ H : interp _ (Postcondition (toCmd (compileEquality _) _ _ _ _ _) _) |- _ ] =>
                   apply compileEquality_post in H
                 | [ IH : forall pre : _ -> _, _ |- vcs _ ] =>
                   apply IH
               end; eauto; pre); t).
    Qed.
  End compileEquality.

  Definition Select' : chunk := (
    rw <-* tptr;;

    [Al bs, Al a : A, Al head, Al done, Al remaining,
      PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
        * tptr =*> head * lseg done head (V rw) * sll remaining (V rw)
        * rows sch head done * rows sch head remaining * invPre a V
      POST[R] array8 bs (V "buf") * invPost a V R]
    While (rw <> 0) {
      data <-* rw;;

      Assert [Al bs, Al a : A, Al head, Al done, Al remaining,
        PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
          * [| V rw <> 0 |] * tptr =*> head * lseg done head (V rw) * sll (V data :: remaining) (V rw)
          * rows sch head remaining * rows sch head done * row sch (V data) * invPre a V
        POST[R] array8 bs (V "buf") * invPost a V R];;

      compileEqualities cond;;

      If ("matched" = 0) {
        Skip
      } else {
        body (fun V_rw V_data => Ex head, Ex done, Ex remaining, Ex p,
          tptr =*> head * lseg done head V_rw
          * (V_rw ==*> V_data, p) * sll remaining p
          * rows sch head done * rows sch head remaining
          * [| freeable V_rw 2 |] * [| V_rw <> 0 |])%Sep
      };;

      rw <-* rw + 4;;

      Assert [Al bs, Al a : A, Al head, Al done, Al remaining,
        PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
          * tptr =*> head * lseg_append (done ++ V data :: nil) head (V rw) * sll remaining (V rw)
          * rows sch head (done ++ V data :: nil) * rows sch head remaining * invPre a V
        POST[R] array8 bs (V "buf") * invPost a V R]
    }
  )%SP.

  Definition sinvar :=
    Al bs, Al a : A,
    PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
      * table sch tptr * invPre a V
    POST[R] array8 bs (V "buf") * invPost a V R.

  Definition spost inv :=
    Al bs, Al a : A,
    PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
      * row sch (V data) * inv (V rw) (V data) * invPre a V
    POST[R] array8 bs (V "buf") * invPost a V R.

  Notation svars := (rw :: data :: nil).

  Definition noOverlapExp (e : exp) :=
    match e with
      | Const _ => True
      | Input pos len => pos <> rw /\ pos <> data /\ len <> rw /\ len <> data
    end.

  Definition noOverlapExps := List.Forall noOverlapExp.

  Notation SelectVcs := (fun im ns res =>
    (~In "rp" ns) :: incl svars ns :: (rw <> "rp")%type :: (data <> "rp")%type
    :: incl baseVars ns
    :: (rw <> data)%type
    :: (forall a V V', (forall x, x <> rw -> x <> data
      -> x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> x <> "matched" -> sel V x = sel V' x)
      -> invPre a V ===> invPre a V')
    :: (forall a V V' R, (forall x, x <> rw -> x <> data
      -> x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> x <> "matched" -> sel V x = sel V' x)
      -> invPost a V R = invPost a V' R)
    :: (forall inv pre mn H,
      (forall specs st, interp specs (pre st)
        -> interp specs (spost inv true (fun w => w) ns res st))
      -> vcs (VerifCond (toCmd (body inv) mn (im := im) H ns res pre)))
    :: (forall specs inv pre mn H st,
      interp specs (Postcondition (toCmd (body inv) mn (im := im) H ns res pre) st)
      -> interp specs (spost inv true (fun w => w) ns res st))
    :: "array8"!"equal" ~~ im ~~> ArrayOps.equalS
    :: (res >= 10)%nat
    :: wfEqualities ns sch cond
    :: ("matched" <> rw)%type
    :: ("matched" <> data)%type
    :: (data <> "ibuf")%type
    :: (data <> "ipos")%type
    :: (data <> "ilen")%type
    :: (data <> "tmp")%type
    :: (data <> "len")%type
    :: (data <> "buf")%type
    :: In data ns
    :: (rw <> "rp")%type
    :: (rw <> "ibuf")%type
    :: (rw <> "ipos")%type
    :: (rw <> "ilen")%type
    :: (rw <> "tmp")%type
    :: (rw <> "len")%type
    :: (rw <> "buf")%type
    :: goodSize (length sch)
    :: noOverlapExps (exps cond)
    :: nil).

  Hint Immediate incl_refl.

  Theorem Forall_impl3 : forall A (P Q R S : A -> Prop) ls,
    List.Forall P ls
    -> List.Forall Q ls
    -> List.Forall R ls
    -> (forall x : A, P x -> Q x -> R x -> S x)
    -> List.Forall S ls.
    induction 1; inversion 1; inversion 1; auto.
  Qed.

  Theorem inputOk_weaken_params : forall ns V V' es,
    inputOk V es
    -> noOverlapExps es
    -> wfExps ns es
    -> (forall x, x <> rw -> x <> data -> sel V x = sel V' x)
    -> rw <> "len"
    -> data <> "len"
    -> inputOk V' es.
    intros; eapply Forall_impl3; [ apply H | apply H0 | apply H1 | ].
    intro e; destruct e; simpl; intuition idtac.
    repeat rewrite <- H2 by (simpl; congruence); assumption.
  Qed.

  Hint Extern 2 (inputOk _ _) => eapply inputOk_weaken_params; try eassumption;
    try (eapply wfEqualities_wfExps; eassumption); [ descend ].

  Hint Resolve compileEqualities_vcs.

  Ltac q :=
    repeat match goal with
             | [ H : interp _ _, _ : context[Binop _ _ Plus (immInR (natToW 4) _)] |- _ ] =>
               apply compileEqualities_post in H; auto; pre; prep; evalu;
                 match goal with
                   | [ _ : _ = _ :: ?ls |- _ ] => do 4 eexists; exists ls
                 end
             | [ H : interp _ _ |- _ ] => apply compileEqualities_post in H; auto
             | [ H : _ |- vcs _ ] => apply H; pre
           end; t.

  Definition Select : chunk.
    refine (WrapC Select'
      sinvar
      sinvar
      SelectVcs
      _ _); abstract (wrap0; abstract q).
  Defined.
End Select.
