Require Import AutoSep Wrap StringOps XmlLex SinglyLinkedList Malloc ArrayOps.
Require Import RelDb RelDbCondition.

Set Implicit Arguments.


(** * A language for generating XML code *)

Inductive xml :=
| Cdata (const : string)
| Var (start len : string)
| Tag (tag : string) (inner : list xml)
| Column (data : string) (sch : schema) (col : string).

Section ForallR.
  Variable A : Type.
  Variable P : A -> Prop.

  Fixpoint ForallR (ls : list A) : Prop :=
    match ls with
      | nil => True
      | x :: ls' => P x /\ ForallR ls'
    end.

  Theorem Forall_ForallR : forall ls, List.Forall P ls -> ForallR ls.
    induction 1; simpl; intuition.
  Qed.

  Theorem ForallR_Forall : forall ls, ForallR ls -> List.Forall P ls.
    induction ls; simpl; intuition.
  Qed.

  Fixpoint ExistsR (ls : list A) : Prop :=
    match ls with
      | nil => False
      | x :: ls' => P x \/ ExistsR ls'
    end.

  Theorem Exists_ExistsR : forall ls, List.Exists P ls -> ExistsR ls.
    induction 1; simpl; intuition.
  Qed.

  Theorem ExistsR_Exists : forall ls, ExistsR ls -> List.Exists P ls.
    induction ls; simpl; intuition.
  Qed.
End ForallR.

Fixpoint wf (xm : xml) : Prop :=
  match xm with
    | Cdata const => goodSize (String.length const)
    | Var _ _ => True
    | Tag tag inner => goodSize (String.length tag + 3) /\ ForallR wf inner
    | Column _ sch col => goodSize (length sch) /\ In col sch
  end.

Fixpoint freeVar (xm : xml) (xs : string * string) : Prop :=
  match xm with
    | Cdata _ => False
    | Var start len => xs = (start, len)
    | Tag _ inner => ExistsR (fun xm' => freeVar xm' xs) inner
    | Column _ _ _ => False
  end.

Fixpoint freeRowVar (xm : xml) (xs : string * schema) : Prop :=
  match xm with
    | Cdata _ => False
    | Var _ _ => False
    | Tag _ inner => ExistsR (fun xm' => freeRowVar xm' xs) inner
    | Column data sch _ => xs = (data, sch)
  end.

Section xml_ind'.
  Variable P : xml -> Prop.

  Hypothesis H_Cdata : forall const, P (Cdata const).

  Hypothesis H_Var : forall start len, P (Var start len).

  Hypothesis H_Tag : forall tag inner, List.Forall P inner -> P (Tag tag inner).

  Hypothesis H_Column : forall data sch col, P (Column data sch col).

  Fixpoint xml_ind' (xm : xml) : P xm :=
    match xm with
      | Cdata const => H_Cdata const
      | Var start len => H_Var start len
      | Tag tag inner => H_Tag tag ((fix xmls_ind (xms : list xml) : List.Forall P xms :=
        match xms with
          | nil => Forall_nil _
          | xm :: xms' => Forall_cons _ (xml_ind' xm) (xmls_ind xms')
        end) inner)
      | Column data sch col => H_Column data sch col
    end.
End xml_ind'.

Opaque xml_ind'.

Definition inBounds (cdatas : list (string * string)) (V : vals) :=
  List.Forall (fun p => wordToNat (V (fst p)) + wordToNat (V (snd p)) <= wordToNat (V "len"))%nat
  cdatas.

Require Import Bags.


(** * Compiling XML snippets into Bedrock chunks *)

Section Out.
  Variable A : Type.
  Variable invPre : A -> vals -> HProp.
  Variable invPost : A -> vals -> W -> HProp.

  Variable data : string.
  Variable sch : schema.

  (* Precondition and postcondition of generation *)
  Definition invar cdatas :=
    Al a : A, Al bsI, Al bsO,
    PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf") * row sch (V data)
      * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
      * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |] * invPre a V
    POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf") * [| length bsO' = length bsO |] * invPost a V R.

  Infix ";;" := SimpleSeq : SP_scope.

  Section OutList.
    Variable Out' : xml -> chunk.

    Fixpoint OutList (xms : list xml) : chunk :=
      match xms with
        | nil => Skip
        | xm :: xms' => (Out' xm;; OutList xms')
      end%SP.
  End OutList.

  Fixpoint findCol (sch : schema) (s : string) : nat :=
    match sch with
      | nil => O
      | s' :: sch' => if string_dec s s' then O else S (findCol sch' s)
    end.

  Inductive reveal_row : Prop := RevealRow.
  Hint Constructors reveal_row.

  Fixpoint Out' (cdatas : list (string * string)) (xm : xml) : chunk :=
    match xm with
      | Cdata const => StringWrite "obuf" "olen" "opos" "overflowed" const
        (fun (p : list B * A) V => array8 (fst p) (V "buf") * [| length (fst p) = wordToNat (V "len") |]
          * [| inBounds cdatas V |] * invPre (snd p) V * row sch (V data))%Sep
        (fun _ (p : list B * A) V R => Ex bs', array8 bs' (V "obuf") * [| length bs' = wordToNat (V "olen") |]
          * array8 (fst p) (V "buf") * invPost (snd p) V R)%Sep
      | Var start len =>
        "tmp" <- "olen" - "opos";;
        If (len < "tmp") {
          Call "array8"!"copy"("obuf", "opos", "buf", start, len)
          [Al a : A, Al bsI, Al bsO,
            PRE[V] [| V len < V "olen" ^- V "opos" |]%word * array8 bsI (V "buf") * array8 bsO (V "obuf")
              * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
              * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word * invPre a V * row sch (V data)
            POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf") * [| length bsO' = length bsO |]
              * invPost a V R];;
          "opos" <- "opos" + len
        } else {
          "overflowed" <- 1
        }
      | Tag tag inner =>
        StringWrite "obuf" "olen" "opos" "overflowed" ("<" ++ tag ++ ">")
        (fun (p : list B * A) V => array8 (fst p) (V "buf") * [| length (fst p) = wordToNat (V "len") |]
          * invPre (snd p) V * [| inBounds cdatas V |] * row sch (V data))%Sep
        (fun _ (p : list B * A) V R => Ex bs', array8 bs' (V "obuf") * [| length bs' = wordToNat (V "olen") |]
          * array8 (fst p) (V "buf") * invPost (snd p) V R)%Sep;;
        OutList (Out' cdatas) inner;;
        StringWrite "obuf" "olen" "opos" "overflowed" ("</" ++ tag ++ ">")
        (fun (p : list B * A) V => array8 (fst p) (V "buf") * [| length (fst p) = wordToNat (V "len") |]
          * invPre (snd p) V * [| inBounds cdatas V |] * row sch (V data))%Sep
        (fun _ (p : list B * A) V R => Ex bs', array8 bs' (V "obuf") * [| length bs' = wordToNat (V "olen") |]
          * array8 (fst p) (V "buf") * invPost (snd p) V R)%Sep
      | Column data sch col =>
        Note [reveal_row];;

        Assert [Al a : A, Al bsI, Al bsO,
          PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
            * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
            * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word * invPre a V
            * Ex buf, Ex len, Ex cols, Ex bs,
              (V data ==*> buf, len) * array (posl cols) (V data ^+ $8)
              * array (lenl cols) (V data ^+ $8 ^+ $(length sch * 4)) * array8 bs buf
              * [| length bs = wordToNat len |] * [| length cols = length sch |] * [| RelDb.inBounds len cols |]
              * [| V data <> 0 |] * [| freeable (V data) (2 + length sch + length sch) |]
              * [| buf <> 0 |] * [| freeable8 buf (length bs) |]
              * [| natToW (findCol sch col) < natToW (length (lenl cols)) |]%word
          POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
            * [| length bsO' = length bsO |] * invPost a V R];;

        "matched" <- data + 8;;
        "matched" <- "matched" + (length sch * 4)%nat;;
        "matched" <-* "matched" + (4 * findCol sch col)%nat;;

        "tmp" <- "olen" - "opos";;
        If ("matched" < "tmp") {
          Assert [Al a : A, Al bsI, Al bsO,
            PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
              * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
              * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word * invPre a V
              * Ex buf, Ex len, Ex cols, Ex bs,
                (V data ==*> buf, len) * array (posl cols) (V data ^+ $8)
                * array (lenl cols) (V data ^+ $8 ^+ $(length sch * 4)) * array8 bs buf
                * [| length bs = wordToNat len |] * [| length cols = length sch |] * [| RelDb.inBounds len cols |]
                * [| V data <> 0 |] * [| freeable (V data) (2 + length sch + length sch) |]
                * [| buf <> 0 |] * [| freeable8 buf (length bs) |]
                * [| V "matched" = Array.selN (lenl cols) (findCol sch col) |]
                * [| natToW (findCol sch col) < natToW (length (posl cols)) |]%word
                * [| V "matched" < V "olen" ^- V "opos" |]%word
            POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
              * [| length bsO' = length bsO |] * invPost a V R];;

          "tmp" <- data + 8;;
          "tmp" <-* "tmp" + (4 * findCol sch col)%nat;;

          Assert [Al a : A, Al bsI, Al bsO,
            PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
              * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
              * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word * invPre a V
              * Ex buf, Ex len, Ex cols, Ex bs,
                (V data ==*> buf, len) * array (posl cols) (V data ^+ $8)
                * array (lenl cols) (V data ^+ $8 ^+ $(length sch * 4)) * array8 bs buf
                * [| length bs = wordToNat len |] * [| length cols = length sch |] * [| RelDb.inBounds len cols |]
                * [| V data <> 0 |] * [| freeable (V data) (2 + length sch + length sch) |]
                * [| buf <> 0 |] * [| freeable8 buf (length bs) |]
                * [| V "matched" = Array.selN (lenl cols) (findCol sch col) |]
                * [| V "tmp" = Array.selN (posl cols) (findCol sch col) |]
                * [| V "matched" < V "olen" ^- V "opos" |]%word
            POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf")
              * [| length bsO' = length bsO |] * invPost a V R];;

          Note [reveal_row];;
          "res" <-* data;;

          Call "array8"!"copy"("obuf", "opos", "res", "tmp", "matched")
          [Al a : A, Al bsI, Al bsO,
            PRE[V] [| V "matched" < V "olen" ^- V "opos" |]%word * array8 bsI (V "buf") * array8 bsO (V "obuf")
              * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
              * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word * invPre a V * row sch (V data)
            POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf") * [| length bsO' = length bsO |]
              * invPost a V R];;
          "opos" <- "opos" + "matched"
        } else {
          Note [reveal_row];;

          "overflowed" <- 1
        }
    end%SP.

  Opaque mult.

  Lemma invPre_sel : forall a V, invPre a (sel V) = invPre a V.
    auto.
  Qed.

  Lemma invPost_sel : forall a V R, invPost a (sel V) R = invPost a V R.
    auto.
  Qed.

  Lemma inBounds_sel : forall cdatas V, inBounds cdatas (sel V) = inBounds cdatas V.
    auto.
  Qed.

  Ltac prep :=
    clear_fancy; repeat match goal with
                          | [ H : LabelMap.find _ _ = _ |- _ ] => try rewrite H; clear H
                          | [ st : (settings * state)%type |- _ ] => destruct st; simpl in *
                        end.

  Ltac reger := repeat match goal with
                         | [ H : Regs _ _ = _ |- _ ] => rewrite H
                       end.

  Ltac simp :=
    repeat match goal with
             | [ H : context[invPre ?a (sel ?V)] |- _ ] => rewrite (invPre_sel a V) in H
             | [ |- context[invPre ?a (sel ?V)] ] => rewrite (invPre_sel a V)
             | [ H : context[invPost ?a (sel ?V) ?R] |- _ ] => rewrite (invPost_sel a V R) in H
             | [ |- context[invPost ?a (sel ?V) ?R] ] => rewrite (invPost_sel a V R)
             | [ H : context[inBounds ?x (sel ?V)] |- _ ] => rewrite (inBounds_sel x V) in H
             | [ |- context[inBounds ?x (sel ?V)] ] => rewrite (inBounds_sel x V)
           end; reger.

  Lemma mult4_S : forall n, 4 * S n = S (S (S (S (4 * n)))).
    simpl; intros; omega.
  Qed.

  Definition cdatasGood (cdatas : list (string * string)) :=
    List.Forall (fun p => fst p <> "opos" /\ fst p <> "overflowed" /\ fst p <> "tmp" /\ fst p <> "matched"
      /\ fst p <> "res"
      /\ snd p <> "opos" /\ snd p <> "overflowed" /\ snd p <> "tmp" /\ snd p <> "matched"
      /\ snd p <> "res") cdatas.

  Ltac prepl := post; unfold lvalIn, regInL, immInR in *;
    repeat match goal with
             | [ H : ForallR _ _ |- _ ] => clear H
             | [ H : List.Forall _ _ |- _ ] => clear H
             | [ H : importsGlobal _ |- _ ] =>
               repeat match goal with
                        | [ H' : context[H] |- _ ] => clear H'
                      end; clear H
           end; prep_locals; simp; try rewrite mult4_S in *;
    try match goal with
          | [ H : cdatasGood _, H' : In _ _ |- _ ] =>
            specialize (proj1 (Forall_forall _ _) H _ H'); simpl; intuition idtac
        end;
    try rewrite natToW_4times in *.

  Ltac my_descend :=
    try match goal with
          | [ H : inBounds _ _, H' : In _ _ |- _ ] =>
            rewrite <- inBounds_sel in H;
              specialize (proj1 (Forall_forall _ _) H _ H'); simpl; intuition idtac;
                rewrite inBounds_sel in H
        end;
    repeat match goal with
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
             | [ H : evalCond _ _ _ _ _ = _ |- _ ] => clear H
             | [ H : In _ ?ls |- _ ] =>
               match ls with
                 | sch => fail 1
                 | _ => clear H
               end
             | [ x : (_ * _)%type |- _ ] => destruct x; simpl in *
           end;
    unfold invar, localsInvariant; descend;
      simp; reger;
      try match goal with
            | [ |- context[@fst ?A ?B ?U] ] =>
              let x := fresh in let y := fresh in
                evar (x : A); evar (y : B); let x' := eval unfold x in x in
                  let y' := eval unfold y in y in equate U (x', y'); clear x y; simpl
          end; autorewrite with sepFormula in *.

  Ltac deSpec :=
    repeat match goal with
             | [ H : LabelMap.find _ _ = _ |- _ ] => try rewrite H; clear H
           end.

  Ltac invoke1 :=
    match goal with
      | [ H : interp _ _, H' : _ |- _ ] => apply H' in H; clear H'
      | [ |- vcs (_ :: _) ] => wrap0; try discriminate
      | [ H : _ |- vcs _ ] => apply vcs_app_fwd || apply H
    end; post.

  Ltac bash :=
    try match goal with
          | [ _ : inBounds ?cdatas _ |- interp _ (![?pre] _ ---> ![?post] _)%PropX ] =>
            match post with
              | context[locals ?ns _ _ _] =>
                match pre with
                  | context[locals ns ?vs _ _] =>
                    assert (inBounds cdatas vs) by eauto
                end
            end
          | [ H : context[invPost] |- ?P = ?Q ] =>
            match P with
              | context[invPost ?a ?V _] =>
                match Q with
                  | context[invPost a ?V' _] =>
                    rewrite (H a V V') by intuition; reflexivity
                end
            end
        end;

    try match goal with
          | [ |- interp _ (![?pre] _ ---> ![?post] _)%PropX ] =>
            match post with
              | context[locals ?ns _ _ _] =>
                match pre with
                  | context[locals ns ?vs _ _] =>
                    match pre with
                      | context[invPre ?a ?vs'] =>
                        assert (unit -> invPre a vs' ===> invPre a vs) by
                          match goal with
                            | [ H : _ |- _ ] => intro; apply H; intuition descend
                          end
                      | context[invPost ?a ?vs' ?r] =>
                        assert (unit -> invPost a vs' r = invPost a vs r) by
                          match goal with
                            | [ H : _ |- _ ] => intro; apply H; intuition descend
                          end
                    end
                end
            end
        end;

    match goal with
      | _ => weaken_invPre
      | [ _ : context[reveal_row] |- _ ] => try match_locals; step RelDb.hints
      | _ => try match_locals; step auto_ext
    end.

  Ltac t := post; repeat invoke1; prep; propxFo;
    repeat invoke1; prepl;
      match goal with
        | [ _ : context[reveal_row] |- _ ] => evaluate RelDb.hints
        | _ => evaluate auto_ext
      end; my_descend; (repeat (bash; my_descend); eauto).

  Notation "l ~~ im ~~> s" := (LabelMap.find l%SP im = Some (Precondition s None)) (at level 0).

  Section Out_correct.
    Variables (im : LabelMap.t assert) (mn : string) (H : importsGlobal im) (ns : list string) (res : nat).

    Hypothesis Hrp : ~In "rp" ns.
    Hypothesis Hobuf : In "obuf" ns.
    Hypothesis Holen : In "olen" ns.
    Hypothesis Hopos : In "opos" ns.
    Hypothesis Hoverflowed : In "overflowed" ns.
    Hypothesis Htmp : In "tmp" ns.
    Hypothesis Hbuf : In "buf" ns.
    Hypothesis Hmatched : In "matched" ns.
    Hypothesis HresV : In "res" ns.
    Hypothesis Hdata : In data ns.

    Hypothesis Hnot_rp : data <> "rp".
    Hypothesis Hnot_obuf : data <> "obuf".
    Hypothesis Hnot_opos : data <> "opos".
    Hypothesis Hnot_overflowed : data <> "overflowed".
    Hypothesis Hnot_tmp : data <> "tmp".
    Hypothesis Hnot_buf : data <> "buf".
    Hypothesis Hnot_matched : data <> "matched".
    Hypothesis Hnot_res : data <> "res".

    Hypothesis HinvPre : forall a V V', (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp"
      -> x <> "matched" -> x <> "res" -> sel V x = sel V' x)
    -> invPre a V ===> invPre a V'.
    Hypothesis HinvPost : forall a V V' R, (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp"
      -> x <> "matched" -> x <> "res" -> sel V x = sel V' x)
    -> invPost a V R = invPost a V' R.
    Hypothesis Hres : (res >= 7)%nat.

    Ltac split_IH :=
      match goal with
        | [ IH : forall pre : settings * state -> _, _ |- _ ] =>
          (generalize (fun a b => proj1 (IH a b));
            generalize (fun a b => proj2 (IH a b)))
          || (generalize (fun a b c => proj1 (IH a b c));
            generalize (fun a b c => proj2 (IH a b c))); clear IH; intros
        | [ H : forall start len : string, _ |- _ ] =>
          generalize (fun start len H' => H start len (or_introl _ H'));
            specialize (fun start len H' => H start len (or_intror _ H')); intro
        | [ H : forall (data : string) (sch : schema), _ |- _ ] =>
          generalize (fun start len H' => H start len (or_introl _ H'));
            specialize (fun start len H' => H start len (or_intror _ H')); intro
      end.

    Lemma OutList_correct : forall cdatas, cdatasGood cdatas
      -> forall xms,
        List.Forall
        (fun xm => forall pre, wf xm
          -> (forall start len, freeVar xm (start, len) -> In (start, len) cdatas)
          -> (forall start len, freeVar xm (start, len) -> In start ns /\ In len ns)
          -> (forall specs st, interp specs (pre st)
            -> interp specs (invar cdatas true (fun x => x) ns res st))
          -> (forall data' sch', freeRowVar xm (data', sch') -> data' = data /\ sch' = sch)
          -> (forall specs st,
            interp specs (Postcondition (toCmd (Out' cdatas xm) mn H ns res pre) st)
            -> interp specs (invar cdatas true (fun x => x) ns res st))
          /\ vcs (VerifCond (toCmd (Out' cdatas xm) mn H ns res pre))) xms
        -> ForallR wf xms
        -> forall pre,
          (forall start len, ExistsR (fun xm => freeVar xm (start, len)) xms -> In (start, len) cdatas)
          -> (forall start len, ExistsR (fun xm => freeVar xm (start, len)) xms -> In start ns /\ In len ns)
          -> (forall specs st, interp specs (pre st)
            -> interp specs (invar cdatas true (fun x => x) ns res st))
          -> (forall data' sch', ExistsR (fun xm => freeRowVar xm (data', sch')) xms -> data' = data /\ sch' = sch)
          -> (forall specs st, interp specs (Postcondition (toCmd (OutList (Out' cdatas) xms) mn H ns res pre) st)
            -> interp specs (invar cdatas true (fun x => x) ns res st))
          /\ vcs (VerifCond (toCmd (OutList (Out' cdatas) xms) mn H ns res pre)).
      induction 2; post; intuition; repeat split_IH; t.
    Qed.

    Hint Constructors unit.

    Lemma length_append : forall s1 s2, String.length (s1 ++ s2) = String.length s1 + String.length s2.
      induction s1; simpl; intuition.
    Qed.

    Hint Rewrite length_append : sepFormula.

    Hint Extern 1 (goodSize _) => eapply goodSize_weaken; [ eassumption | omega ].

    Lemma Forall_impl2 : forall A (P Q R : A -> Prop) ls,
      List.Forall P ls
      -> List.Forall Q ls
      -> (forall x, P x -> Q x -> R x)
      -> List.Forall R ls.
      induction 1; inversion 1; eauto.
    Qed.

    Lemma inBounds_weaken : forall cdatas V V',
      cdatasGood cdatas
      -> inBounds cdatas V
      -> (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp" -> x <> "matched"
        -> x <> "res" -> sel V x = sel V' x)
      -> inBounds cdatas V'.
      intros; rewrite <- inBounds_sel in *;
        eapply Forall_impl2; [ match goal with
                                 | [ H : cdatasGood _ |- _ ] => apply H
                               end
          | match goal with
              | [ H : inBounds _ _ |- _ ] => apply H
            end
          | ]; cbv beta; intuition idtac;
        match goal with
          | [ H : forall x : string, _ |- _ ] => repeat rewrite <- H by congruence; assumption
        end.
    Qed.

    Hint Extern 1 (inBounds _ _) => eapply inBounds_weaken; [ eassumption | eassumption
      | descend ].

    Ltac deDouble :=
      repeat match goal with
               | [ H : forall start len : string, _ |- _ ] =>
                   specialize (H _ _ eq_refl)
               | [ H : forall (data' : string) (sch' : schema), _ |- _ ] =>
                   specialize (H _ _ eq_refl)
             end.

    Ltac clear_fancier :=
      repeat match goal with
               | [ H : ForallR _ _ |- _ ] => clear H
               | [ H : List.Forall _ _ |- _ ] => clear H
             end; clear_fancy.

    Ltac proveHimp :=
      simpl; repeat match goal with
                      | [ V : vals |- _ ] =>
                        progress repeat match goal with
                                          | [ |- context[V ?x] ] => change (V x) with (sel V x)
                                        end
                    end;
      try match goal with
            | [ H : forall x : string, _ |- _ ] => repeat rewrite H by congruence
          end;
      try match goal with
            | [ H : context[invPost] |- context[?P = ?Q] ] =>
              match P with
                | context[invPost ?a ?V ?r] =>
                  match Q with
                    | context[invPost a ?V' r] =>
                      rewrite (H a V V') by intuition
                  end
              end
          end; reflexivity || clear_fancier; sepLemma; eauto.

    Lemma convert : forall a b c : W,
      a < b ^- c
      -> c <= b
      -> c ^+ a <= b.
      clear; intros.
      pre_nomega.
      rewrite wordToNat_wplus in *.
      omega.
      apply goodSize_weaken with (wordToNat b); eauto.
    Qed.

    Hint Immediate convert.

    Hint Extern 1 (himp _ _ _) =>
      apply himp_star_frame; try reflexivity; [].

    Hint Extern 1 (himp _ (invPre _ _) (invPre _ _)) =>
      match goal with
        | [ H : _ |- _ ] => apply H; solve [ descend; auto 1 ]
      end.

    Hint Extern 1 (himp _ (invPost ?a ?b ?c) (invPost ?a ?b' ?c)) =>
      rewrite (HinvPost a b b' c) by descend; reflexivity.

    Lemma convert' : forall (a b c : W) n,
      a < b ^- c
      -> c <= b
      -> n = wordToNat b
      -> (wordToNat c + wordToNat a <= n)%nat.
      clear; intros; subst.
      pre_nomega.
      omega.
    Qed.

    Hint Immediate convert'.

    Lemma wplus_wminus : forall u v : W, u ^+ v ^- v = u.
      intros; words.
    Qed.

    Hint Rewrite wplus_wminus mult4_S : sepFormula.

    Lemma findCol_bound : forall s col,
      In col s
      -> (findCol s col < length s)%nat.
      clear; induction s; simpl; intuition subst;
        match goal with
          | [ |- context[if ?E then _ else _] ] => destruct E
        end; intuition.
    Qed.

    Lemma findCol_bound_natToW : forall col n,
      In col sch
      -> goodSize (Datatypes.length sch)
      -> n = length sch
      -> natToW (findCol sch col) < natToW n.
      clear; intros; subst.
      pre_nomega.
      rewrite wordToNat_natToWord_idempotent.
      rewrite wordToNat_natToWord_idempotent.
      eauto using findCol_bound.
      apply findCol_bound in H; congruence.
      change (goodSize (findCol sch col)); eapply goodSize_weaken; eauto.
      apply findCol_bound in H; auto.
    Qed.

    Lemma findCol_posl : forall col cols,
      In col sch
      -> goodSize (Datatypes.length sch)
      -> length cols = length sch
      -> natToW (findCol sch col) < natToW (length (posl cols)).
      intros; rewrite length_posl; eauto using findCol_bound_natToW.
    Qed.

    Lemma findCol_lenl : forall col cols,
      In col sch
      -> goodSize (Datatypes.length sch)
      -> length cols = length sch
      -> natToW (findCol sch col) < natToW (length (lenl cols)).
      intros; rewrite length_lenl; eauto using findCol_bound_natToW.
    Qed.

    Hint Immediate findCol_posl findCol_lenl.

    Lemma selN_col : forall col cols,
      In col sch
      -> goodSize (length sch)
      -> length cols = length sch
      -> Array.sel cols (natToW (findCol sch col)) = selN cols (findCol sch col).
      clear; unfold Array.sel; intros; f_equal.
      apply wordToNat_natToWord_idempotent.
      change (goodSize (findCol sch col)).
      eapply goodSize_weaken; eauto.
      apply findCol_bound in H; auto.
    Qed.

    Lemma selN_posl : forall col cols,
      In col sch
      -> goodSize (length sch)
      -> length cols = length sch
      -> Array.sel (posl cols) (natToW (findCol sch col)) = selN (posl cols) (findCol sch col).
      intros; apply selN_col; auto; rewrite length_posl; auto.
    Qed.

    Lemma selN_lenl : forall col cols,
      In col sch
      -> goodSize (length sch)
      -> length cols = length sch
      -> Array.sel (lenl cols) (natToW (findCol sch col)) = selN (lenl cols) (findCol sch col).
      intros; apply selN_col; auto; rewrite length_lenl; auto.
    Qed.

    Hint Immediate selN_posl selN_lenl.

    Lemma inBounds_selN : forall len cols,
      RelDb.inBounds len cols
      -> forall col a b c, a = selN (posl cols) (findCol sch col)
        -> b = selN (lenl cols) (findCol sch col)
        -> c = wordToNat len
        -> In col sch
        -> length cols = length sch
        -> (wordToNat a + wordToNat b <= c)%nat.
      intros; eapply inBounds_selN; try eassumption.
      rewrite H5; eapply findCol_bound; auto.
    Qed.

    Hint Extern 1 (_ + _ <= _)%nat =>
      eapply inBounds_selN; try eassumption; (cbv beta; congruence).

    Lemma Out_correct : forall cdatas, cdatasGood cdatas
      -> "array8"!"copy" ~~ im ~~> copyS
      -> forall xm pre,
        wf xm
        -> (forall start len, freeVar xm (start, len) -> In (start, len) cdatas)
        -> (forall start len, freeVar xm (start, len) -> In start ns /\ In len ns)
        -> (forall specs st, interp specs (pre st)
          -> interp specs (invar cdatas true (fun x => x) ns res st))
        -> (forall data' sch', freeRowVar xm (data', sch') -> data' = data /\ sch' = sch)
        -> (forall specs st, interp specs (Postcondition (toCmd (Out' cdatas xm) mn H ns res pre) st)
          -> interp specs (invar cdatas true (fun x => x) ns res st))
        /\ vcs (VerifCond (toCmd (Out' cdatas xm) mn H ns res pre)).
      induction xm using xml_ind';
        abstract (post; try match goal with
                              | [ |- vcs (_ :: _) ] => wrap0; try discriminate
                            end;
        abstract (deDouble; deSpec; intuition subst;
          solve [ t | proveHimp |
            match goal with
              | [ H : List.Forall _ _ |- _ ] =>
                eapply OutList_correct in H; [ destruct H; eauto | auto | auto | auto | auto | | auto ]
            end; t ])).
    Qed.
  End Out_correct.

  Notation OutVcs cdatas xm := (fun im ns res =>
    (~In "rp" ns) :: In "obuf" ns :: In "olen" ns :: In "opos" ns :: In "overflowed" ns
    :: In "tmp" ns :: In "buf" ns :: In "matched" ns :: In "res" ns :: In data ns
    :: (data <> "rp")%type
    :: (data <> "obuf")%type
    :: (data <> "opos")%type
    :: (data <> "overflowed")%type
    :: (data <> "tmp")%type
    :: (data <> "buf")%type
    :: (data <> "matched")%type
    :: (data <> "res")%type
    :: (forall a V V', (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp"
      -> x <> "matched" -> x <> "res" -> sel V x = sel V' x)
      -> invPre a V ===> invPre a V')
    :: (forall a V V' R, (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp" ->
         x <> "matched" -> x <> "res" -> sel V x = sel V' x)
       -> invPost a V R = invPost a V' R)
    :: (res >= 7)%nat
    :: wf xm
    :: (forall start len, freeVar xm (start, len) -> In (start, len) cdatas)
    :: (forall start len, freeVar xm (start, len) -> In start ns /\ In len ns)
    :: (forall data' sch', freeRowVar xm (data', sch') -> data' = data /\ sch' = sch)
    :: cdatasGood cdatas
    :: "array8"!"copy" ~~ im ~~> copyS
    :: nil).

  Definition Out (cdatas : list (string * string)) (xm : xml) : chunk.
    refine (WrapC (Out' cdatas xm)
      (invar cdatas)
      (invar cdatas)
      (OutVcs cdatas xm)
      _ _); abstract (wrap0;
        match goal with
          | [ H : wf _ |- _ ] => eapply Out_correct in H; eauto
        end; t).
  Defined.

End Out.
