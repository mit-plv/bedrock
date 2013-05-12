Require Import AutoSep Wrap StringOps XmlLex SinglyLinkedList Malloc.

Set Implicit Arguments.


(** * A language for generating XML code *)

Inductive xml :=
| Cdata (data : string)
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
End ForallR.

Fixpoint wf (xm : xml) : Prop :=
  match xm with
    | Cdata data => goodSize (String.length data)
    | Tag tag inner => goodSize (String.length tag + 3) /\ ForallR wf inner
  end.

Section xml_ind'.
  Variable P : xml -> Prop.

  Hypothesis H_Cdata : forall data, P (Cdata data).

  Hypothesis H_Tag : forall tag inner, List.Forall P inner -> P (Tag tag inner).

  Fixpoint xml_ind' (xm : xml) : P xm :=
    match xm with
      | Cdata data => H_Cdata data
      | Tag tag inner => H_Tag tag ((fix xmls_ind (xms : list xml) : List.Forall P xms :=
        match xms with
          | nil => Forall_nil _
          | xm :: xms' => Forall_cons _ (xml_ind' xm) (xmls_ind xms')
        end) inner)
    end.
End xml_ind'.

Opaque xml_ind'.


(** * Compiling XML snippets into Bedrock chunks *)

Section Out.
  Variable A : Type.
  Variable invPre : A -> vals -> HProp.
  Variable invPost : A -> vals -> W -> HProp.

  (* Precondition and postcondition of generation *)
  Definition invar :=
    Al a : A, Al bs,
    PRE[V] array8 bs (V "obuf") * [| length bs = wordToNat (V "olen") |]
      * [| V "opos" <= V "olen" |] * invPre a V
    POST[R] Ex bs', array8 bs' (V "obuf") * [| length bs' = length bs |] * invPost a V R.

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

  Fixpoint Out' (xm : xml) : chunk :=
    match xm with
      | Cdata data => StringWrite "obuf" "olen" "opos" "overflowed" data
        invPre invPost
      | Tag tag inner =>
        (StringWrite "obuf" "olen" "opos" "overflowed" ("<" ++ tag ++ ">")
          invPre invPost;;
         OutList Out' inner;;
         StringWrite "obuf" "olen" "opos" "overflowed" ("</" ++ tag ++ ">")
          invPre invPost)
    end%SP.

  Notation OutVcs xm := (fun im ns res =>
    (~In "rp" ns) :: In "obuf" ns :: In "olen" ns :: In "opos" ns :: In "overflowed" ns
    :: (forall a V V', (forall x, x <> "overflowed" -> x <> "opos" -> sel V x = sel V' x)
      -> invPre a V ===> invPre a V')
    :: (forall a V V' R, (forall x, x <> "overflowed" -> x <> "opos" -> sel V x = sel V' x)
      -> invPost a V R = invPost a V' R)
    :: wf xm
    :: nil).

  Opaque mult.

  Lemma invPre_sel : forall a V, invPre a (sel V) = invPre a V.
    auto.
  Qed.

  Lemma invPost_sel : forall a V R, invPost a (sel V) R = invPost a V R.
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
             | [ H : context[invPost ?a (sel ?V) _] |- _ ] => rewrite (invPost_sel a V) in H
             | [ |- context[invPost ?a (sel ?V) _] ] => rewrite (invPost_sel a V)
           end; reger.

  Ltac prepl := post; unfold lvalIn, regInL, immInR in *;
    repeat match goal with
             | [ H : ForallR _ _ |- _ ] => clear H
             | [ H : List.Forall _ _ |- _ ] => clear H
             | [ H : importsGlobal _ |- _ ] =>
               repeat match goal with
                        | [ H' : context[H] |- _ ] => clear H'
                      end; clear H
           end; prep_locals; simp.

  Ltac my_descend :=
    repeat match goal with
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
             | [ H : In _ _ |- _ ] => clear H
           end;
    unfold invar, localsInvariant; descend; simp; reger.

  Ltac invoke1 :=
    match goal with
      | [ H : interp _ _, H' : _ |- _ ] => apply H' in H; clear H'
      | [ |- vcs (_ :: _) ] => wrap0; try discriminate
      | [ H : _ |- vcs _ ] => apply vcs_app_fwd || apply H
    end; post.

  Ltac t := post; repeat invoke1; prep; propxFo;
    repeat invoke1; prepl;
      evaluate auto_ext; my_descend; (repeat (step auto_ext; my_descend); auto).

  Section Out_correct.
    Variables (im : LabelMap.t assert) (mn : string) (H : importsGlobal im) (ns : list string) (res : nat).

    Hypothesis Hrp : ~In "rp" ns.
    Hypothesis Hobuf : In "obuf" ns.
    Hypothesis Holen : In "olen" ns.
    Hypothesis Hopos : In "opos" ns.
    Hypothesis Hoverflowed : In "overflowed" ns.
    Hypothesis HinvPre : forall a V V', (forall x, x <> "overflowed" -> x <> "opos" -> sel V x = sel V' x)
      -> invPre a V ===> invPre a V'.
    Hypothesis HinvPost : forall a V V' R, (forall x, x <> "overflowed" -> x <> "opos" -> sel V x = sel V' x)
      -> invPost a V R = invPost a V' R.

    Ltac split_IH :=
      match goal with
        | [ IH : forall pre : settings * state -> _, _ |- _ ] =>
          (generalize (fun a b => proj1 (IH a b));
            generalize (fun a b => proj2 (IH a b)))
          || (generalize (fun a b c => proj1 (IH a b c));
            generalize (fun a b c => proj2 (IH a b c))); clear IH; intros
      end.

    Lemma OutList_correct : forall xms,
      List.Forall
      (fun xm => forall pre, wf xm
        -> (forall specs st, interp specs (pre st)
          -> interp specs (invar true (fun x => x) ns res st))
        -> (forall specs st,
          interp specs (Postcondition (toCmd (Out' xm) mn H ns res pre) st)
          -> interp specs (invar true (fun x => x) ns res st))
        /\ vcs (VerifCond (toCmd (Out' xm) mn H ns res pre))) xms
      -> ForallR wf xms
      -> forall pre,
        (forall specs st, interp specs (pre st)
          -> interp specs (invar true (fun x => x) ns res st))
        -> (forall specs st, interp specs (Postcondition (toCmd (OutList Out' xms) mn H ns res pre) st)
            -> interp specs (invar true (fun x => x) ns res st))
          /\ vcs (VerifCond (toCmd (OutList Out' xms) mn H ns res pre)).
      induction 1; post; intuition; repeat split_IH; t.
    Qed.

    Hint Constructors unit.

    Lemma length_append : forall s1 s2, String.length (s1 ++ s2) = String.length s1 + String.length s2.
      induction s1; simpl; intuition.
    Qed.

    Hint Rewrite length_append : sepFormula.

    Hint Extern 1 (goodSize _) => eapply goodSize_weaken; [ eassumption | omega ].

    Lemma Out_correct : forall xm pre,
      wf xm
      -> (forall specs st, interp specs (pre st)
        -> interp specs (invar true (fun x => x) ns res st))
      -> (forall specs st, interp specs (Postcondition (toCmd (Out' xm) mn H ns res pre) st)
        -> interp specs (invar true (fun x => x) ns res st))
      /\ vcs (VerifCond (toCmd (Out' xm) mn H ns res pre)).
      induction xm using xml_ind'; (post; try match goal with
                                                | [ |- vcs (_ :: _) ] => wrap0; try discriminate
                                              end;
      solve [ t | match goal with
                    | [ H : List.Forall _ _ |- _ ] =>
                      eapply OutList_correct in H; [ destruct H; eauto | auto | ]
                  end; t ]).
    Qed.
  End Out_correct.

  Definition Out (xm : xml) : chunk.
    refine (WrapC (Out' xm)
      invar
      invar
      (OutVcs xm)
      _ _); abstract (wrap0;
        match goal with
          | [ H : wf _ |- _ ] => eapply Out_correct in H; eauto
        end; t).
  Defined.

End Out.
