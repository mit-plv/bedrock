Require Import AutoSep Wrap StringOps XmlLex SinglyLinkedList Malloc.

Set Implicit Arguments.


(** * Compiling patterns into Bedrock chunks *)

Section Out.
  Variables start len : string.

  Variable inv : vals -> HProp.

  (* Precondition and postcondition of generation *)
  Definition invar :=
    Al bs,
    PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |]
      * [| wordToNat (V start) + wordToNat (V len) <= wordToNat (V "len") |]%nat * inv V
    POST[_] array8 bs (V "buf") * mallocHeap 0.

  (* Alternate sequencing operator, which generates twistier code but simpler postconditions and VCs *)
  Definition SimpleSeq (ch1 ch2 : chunk) : chunk := fun ns res =>
    Structured nil (fun im mn H => Seq_ H (toCmd ch1 mn H ns res) (toCmd ch2 mn H ns res)).

  Infix ";;" := SimpleSeq : SP_scope.

  Notation "l ~~ im ~~> s" := (LabelMap.find l%SP im = Some (Precondition s None)) (at level 0).

  Notation OutVcs := (fun im ns res =>
    (~In "rp" ns) :: In "buf" ns :: In "len" ns :: In "tmp" ns :: In start ns :: In len ns
    :: NoDup ("buf" :: "len" :: "tmp" :: start :: len :: nil)
    :: (res >= 4)%nat
    :: "sys"!"printInt" ~~ im ~~> printIntS
    :: nil).

  Opaque mult.

  Lemma inv_sel : forall V, inv (sel V) = inv V.
    auto.
  Qed.

  Lemma wplus_wminus : forall u v : W,
    u ^+ v ^- v = u.
    intros; words.
  Qed.

  Hint Rewrite wplus_wminus : sepFormula.

  Lemma mult4_S : forall n,
    4 * S n = S (S (S (S (4 * n)))).
    simpl; intros; omega.
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
             | [ H : context[inv (sel ?V)] |- _ ] => rewrite (inv_sel V) in H
             | [ |- context[inv (sel ?V)] ] => rewrite (inv_sel V)
           end; repeat rewrite <- mult4_S in *; reger.

  Ltac prepl := post; unfold lvalIn, regInL, immInR in *; prep_locals; simp.

  Ltac my_descend :=
    repeat match goal with
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
             | [ H : In _ _ |- _ ] => clear H
           end;
    unfold invar, localsInvariant; descend; simp; reger.

  Ltac invoke1 :=
    match goal with
      | [ H : interp _ _, H' : _ |- _ ] => apply H' in H; clear H'
    end; post.

  Ltac t := post; repeat invoke1; prep; propxFo;
    repeat invoke1; prepl;
      evaluate auto_ext; my_descend; (repeat (step auto_ext; my_descend); auto).

  Definition Out : chunk.
    refine (WrapC (Call "sys"!"printInt"(start)
                   [invar];;
                   Call "sys"!"printInt"(len)
                   [invar])%SP
      invar
      invar
      OutVcs
      _ _); abstract (wrap0; t).
  Defined.

End Out.
