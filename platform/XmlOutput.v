Require Import AutoSep Wrap StringOps XmlLex SinglyLinkedList Malloc ArrayOps.

Set Implicit Arguments.


(** * A language for generating XML code *)

Inductive xml :=
| Cdata (const : string)
| Var (start len : string)
| Tag (tag : string) (inner : list xml).

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
  end.

Fixpoint freeVar (xm : xml) (xs : string * string) : Prop :=
  match xm with
    | Cdata _ => False
    | Var start len => xs = (start, len)
    | Tag _ inner => ExistsR (fun xm' => freeVar xm' xs) inner
  end.

Section mapConcat.
  Variables A B : Type.
  Variable f : A -> list B.

  Fixpoint mapConcat (ls : list A) : list B :=
    match ls with
      | nil => nil
      | x :: ls' => f x ++ mapConcat ls'
    end.
End mapConcat.

Section xml_ind'.
  Variable P : xml -> Prop.

  Hypothesis H_Cdata : forall const, P (Cdata const).

  Hypothesis H_Var : forall start len, P (Var start len).

  Hypothesis H_Tag : forall tag inner, List.Forall P inner -> P (Tag tag inner).

  Fixpoint xml_ind' (xm : xml) : P xm :=
    match xm with
      | Cdata const => H_Cdata const
      | Var start len => H_Var start len
      | Tag tag inner => H_Tag tag ((fix xmls_ind (xms : list xml) : List.Forall P xms :=
        match xms with
          | nil => Forall_nil _
          | xm :: xms' => Forall_cons _ (xml_ind' xm) (xmls_ind xms')
        end) inner)
    end.
End xml_ind'.

Opaque xml_ind'.

Definition inBounds (cdatas : list (string * string)) (V : vals) :=
  List.Forall (fun p => wordToNat (V (fst p)) + wordToNat (V (snd p)) <= wordToNat (V "len"))%nat
  cdatas.


(** * Compiling XML snippets into Bedrock chunks *)

Section Out.
  Variable A : Type.
  Variable invPre : A -> vals -> HProp.
  Variable invPost : A -> vals -> W -> HProp.

  (* Precondition and postcondition of generation *)
  Definition invar cdatas :=
    Al a : A, Al bsI, Al bsO,
    PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf")
      * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
      * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |] * invPre a V
    POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf") * [| length bsO' = length bsO |] * invPost a V R.

  (* Alternate sequencing operator, which generates twistier code but simpler postconditions and VCs *)
  Definition SimpleSeq (ch1 ch2 : chunk) : chunk := fun ns res =>
    Structured nil (fun im mn H => Seq_ H (toCmd ch1 mn H ns res) (toCmd ch2 mn H ns res)).

  Infix ";;" := SimpleSeq : SP_scope.

  Section OutList.
    Variable Out' : xml -> chunk.

    Fixpoint OutList (xms : list xml) : chunk :=
      match xms with
        | nil => Skip
        | xm :: xms' => (Out' xm;; OutList xms')
      end%SP.
  End OutList.

  Fixpoint Out' (cdatas : list (string * string)) (xm : xml) : chunk :=
    match xm with
      | Cdata const => StringWrite "obuf" "olen" "opos" "overflowed" const
        (fun (p : list B * A) V => array8 (fst p) (V "buf") * [| length (fst p) = wordToNat (V "len") |]
          * [| inBounds cdatas V |] * invPre (snd p) V)%Sep
        (fun (p : list B * A) V R => Ex bs', array8 bs' (V "obuf") * [| length bs' = wordToNat (V "olen") |]
          * array8 (fst p) (V "buf") * invPost (snd p) V R)%Sep
      | Var start len =>
        "tmp" <- "olen" - "opos";;
        If (len < "tmp") {
          Call "array8"!"copy"("obuf", "opos", "buf", start, len)
          [Al a : A, Al bsI, Al bsO,
            PRE[V] [| V len < V "olen" ^- V "opos" |]%word * array8 bsI (V "buf") * array8 bsO (V "obuf")
              * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
              * [| inBounds cdatas V |] * [| V "opos" <= V "olen" |]%word * invPre a V
            POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf") * [| length bsO' = length bsO |]
              * invPost a V R];;
          "opos" <- "opos" + len
        } else {
          "overflowed" <- 1
        }
      | Tag tag inner =>
        StringWrite "obuf" "olen" "opos" "overflowed" ("<" ++ tag ++ ">")
        (fun (p : list B * A) V => array8 (fst p) (V "buf") * [| length (fst p) = wordToNat (V "len") |]
          * invPre (snd p) V * [| inBounds cdatas V |])%Sep
        (fun (p : list B * A) V R => Ex bs', array8 bs' (V "obuf") * [| length bs' = wordToNat (V "olen") |]
          * array8 (fst p) (V "buf") * invPost (snd p) V R)%Sep;;
        OutList (Out' cdatas) inner;;
        StringWrite "obuf" "olen" "opos" "overflowed" ("</" ++ tag ++ ">")
        (fun (p : list B * A) V => array8 (fst p) (V "buf") * [| length (fst p) = wordToNat (V "len") |]
          * invPre (snd p) V * [| inBounds cdatas V |])%Sep
        (fun (p : list B * A) V R => Ex bs', array8 bs' (V "obuf") * [| length bs' = wordToNat (V "olen") |]
          * array8 (fst p) (V "buf") * invPost (snd p) V R)%Sep
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
    List.Forall (fun p => fst p <> "opos" /\ fst p <> "overflowed" /\ fst p <> "tmp"
      /\ snd p <> "opos" /\ snd p <> "overflowed" /\ snd p <> "tmp") cdatas.

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
        end.

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
             | [ H : In _ _ |- _ ] => clear H
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

    step auto_ext.

  Ltac t := post; repeat invoke1; prep; propxFo;
    repeat invoke1; prepl;
      evaluate auto_ext; my_descend; (repeat (bash; my_descend); eauto).

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
    Hypothesis HinvPre : forall a V V', (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp"
      -> sel V x = sel V' x)
    -> invPre a V ===> invPre a V'.
    Hypothesis HinvPost : forall a V V' R, (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp"
      -> sel V x = sel V' x)
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
      end.

    Lemma OutList_correct : forall cdatas, cdatasGood cdatas
      -> forall xms,
        List.Forall
        (fun xm => forall pre, wf xm
          -> (forall start len, freeVar xm (start, len) -> In (start, len) cdatas)
          -> (forall start len, freeVar xm (start, len) -> In start ns /\ In len ns)
          -> (forall specs st, interp specs (pre st)
            -> interp specs (invar cdatas true (fun x => x) ns res st))
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
      -> (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp" -> sel V x = sel V' x)
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
      rewrite wordToNat_wminus in * by nomega.
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
      rewrite wordToNat_wminus in * by nomega.
      omega.
    Qed.

    Hint Immediate convert'.

    Lemma wplus_wminus : forall u v : W, u ^+ v ^- v = u.
      intros; words.
    Qed.

    Hint Rewrite wplus_wminus mult4_S : sepFormula.

    Lemma Out_correct : forall cdatas, cdatasGood cdatas
      -> "array8"!"copy" ~~ im ~~> copyS
      -> forall xm pre,
        wf xm
        -> (forall start len, freeVar xm (start, len) -> In (start, len) cdatas)
        -> (forall start len, freeVar xm (start, len) -> In start ns /\ In len ns)
        -> (forall specs st, interp specs (pre st)
          -> interp specs (invar cdatas true (fun x => x) ns res st))
        -> (forall specs st, interp specs (Postcondition (toCmd (Out' cdatas xm) mn H ns res pre) st)
          -> interp specs (invar cdatas true (fun x => x) ns res st))
        /\ vcs (VerifCond (toCmd (Out' cdatas xm) mn H ns res pre)).
      induction xm using xml_ind'; (post; try match goal with
                                                | [ |- vcs (_ :: _) ] => wrap0; try discriminate
                                              end; deDouble; deSpec);
      abstract solve [ t | proveHimp |
        match goal with
          | [ H : List.Forall _ _ |- _ ] =>
            eapply OutList_correct in H; [ destruct H; eauto | auto | auto | auto | auto | ]
        end; t ].
    Qed.
  End Out_correct.

  Notation OutVcs cdatas xm := (fun im ns res =>
    (~In "rp" ns) :: In "obuf" ns :: In "olen" ns :: In "opos" ns :: In "overflowed" ns
    :: In "tmp" ns :: In "buf" ns
    :: (forall a V V', (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp" -> sel V x = sel V' x)
      -> invPre a V ===> invPre a V')
    :: (forall a V V' R, (forall x, x <> "overflowed" -> x <> "opos" -> x <> "tmp" -> sel V x = sel V' x)
      -> invPost a V R = invPost a V' R)
    :: (res >= 7)%nat
    :: wf xm
    :: (forall start len, freeVar xm (start, len) -> In (start, len) cdatas)
    :: (forall start len, freeVar xm (start, len) -> In start ns /\ In len ns)
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
