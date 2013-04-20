Require Import AutoSep Wrap StringMatch XmlLex.

Set Implicit Arguments.


(** * Definition of XML search language *)

Inductive pat :=

(* Record CDATA at this position via two variables. *)
| Cdata (start len : string)

(* Match a specific tag at this level in the XML tree, then continue into its children. *)
| Tag (tag : string) (inner : pat)

(* Match two different patterns at this level of the tree. *)
| Both (p1 p2 : pat).

(** Which program variables appear free in a pattern? *)
Fixpoint freeVar (p : pat) (x : string) : Prop :=
  match p with
    | Cdata start len => x = start \/ x = len
    | Tag _ inner => freeVar inner x
    | Both p1 p2 => freeVar p1 x \/ freeVar p2 x
  end.

(** Does the pattern avoid double-binding a program variable? *)
Fixpoint wf (p : pat) : Prop :=
  match p with
    | Cdata start len => start <> len
    | Tag _ inner => wf inner
    | Both p1 p2 => wf p1 /\ wf p2 /\ (forall x, freeVar p1 x -> ~freeVar p2 x)
  end%type.

(** Executing a pattern requires keeping a stack of saved positions.
    This function calculates the precise stack depth that we need. *)
Fixpoint stackDepth (p : pat) : nat :=
  match p with
    | Cdata _ _ => O
    | Tag _ p => stackDepth p
    | Both p1 p2 => S (max (stackDepth p1) (stackDepth p2))
  end.

(** All pairs of start-length variables in a pattern *)
Fixpoint allCdatas (p : pat) : list (string * string) :=
  match p with
    | Cdata start len => (start, len) :: nil
    | Tag _ inner => allCdatas inner
    | Both p1 p2 => allCdatas p2 ++ allCdatas p1
  end.


(** * Compiling patterns into Bedrock chunks *)

Section Pat.
  Definition inBounds (cdatas : list (string * string)) (V : vals) :=
    List.Forall (fun p => wordToNat (V (fst p)) + wordToNat (V (snd p)) <= wordToNat (V "len"))%nat
    cdatas.

  (* Primary invariant, recording that a set of CDATA positions is in bounds. *)
  Definition inv cdatas :=
    Al bs,
    PRE[V] array8 bs (V "buf") * xmlp (V "len") (V "lex") * [| length bs = wordToNat (V "len") |]
      * [| inBounds cdatas V |]
    POST[_] array8 bs (V "buf").

  Definition maybeInBounds (cdatas : list (string * string)) (V : vals) :=
    V "matched" = 1 -> inBounds cdatas V.

  (* Condition that should hold after a pattern match. *)
  Definition post cdatas :=
    Al bs,
    PRE[V] array8 bs (V "buf") * xmlp (V "len") (V "lex")
      * [| maybeInBounds cdatas V |]
    POST[_] array8 bs (V "buf").

  (* Intermediate invariant, to use right after reading token position from the lexer. *)
  Definition invP cdatas :=
    Al bs,
    PRE[V, R] array8 bs (V "buf") * xmlp' (V "len") R (V "lex") * [| length bs = wordToNat (V "len") |]
      * [| inBounds cdatas V |]
    POST[_] array8 bs (V "buf").

  (* Intermediater invariant, to use right after reading token length from the lexer. *)
  Definition invL cdatas start :=
    Al bs,
    PRE[V, R] array8 bs (V "buf") * xmlp (V "len") (V "lex") * [| length bs = wordToNat (V "len") |]
      * [| inBounds cdatas V |] * [| wordToNat (V start) + wordToNat R <= wordToNat (V "len") |]%nat
    POST[_] array8 bs (V "buf").

  Fixpoint Pat' (p : pat) (level : nat) (cdatas : list (string * string)) : chunk :=
    match p with
      | Cdata start len =>
        "res" <-- Call "xml_lex"!"next"("buf", "lex")
        [inv cdatas];;

        If ("res" = 2) {
          (* This is indeed CDATA!  Save the position and signal success. *)
          start <-- Call "xml_lex"!"tokenStart"("lex")
          [invP cdatas];;

          len <-- Call "xml_lex"!"tokenStart"("lex")
          [invL cdatas start];;

          "matched" <- 1
        } else {
          "matched" <- 0
        }
      | _ => Diverge
    end%SP.

  Notation baseVars := ("buf" :: "len" :: "lex" :: "res" :: "matched" :: nil).

  Definition noConflict pt := List.Forall (fun p => ~In (fst p) baseVars /\ ~In (snd p) baseVars
    /\ ~freeVar pt (fst p) /\ ~freeVar pt (snd p)).

  Notation PatVcs' p cdatas := (fun ns =>
    (~In "rp" ns) :: In "buf" ns :: In "len" ns :: In "lex" ns :: In "res" ns :: In "matched" ns
    :: (forall x, freeVar p x -> In x ns /\ ~In x baseVars /\ x <> "rp")
    :: wf p
    :: noConflict p cdatas
    :: nil).

  Lemma inBounds_sel : forall cdatas V, inBounds cdatas (sel V) = inBounds cdatas V.
    auto.
  Qed.

  Lemma maybeInBounds_sel : forall cdatas V, maybeInBounds cdatas (sel V) = maybeInBounds cdatas V.
    auto.
  Qed.

  Lemma Forall_impl2 : forall A (P Q R : A -> Prop) ls,
    List.Forall P ls
    -> List.Forall Q ls
    -> (forall x, P x -> Q x -> R x)
    -> List.Forall R ls.
    induction 1; inversion 1; eauto.
  Qed.

  Ltac deDouble := repeat match goal with
                            | [ H : forall x, x = _ \/ x = _ -> _ |- _ ] =>
                              generalize (H _ (or_introl _ eq_refl)); intro;
                                specialize (H _ (or_intror _ eq_refl))
                          end;
  intuition idtac; repeat match goal with
                            | [ H : False -> False |- _ ] => clear H
                          end.

  Ltac evalu :=
    match goal with
      | [ ns : list string |- _ ] =>
        repeat match goal with
                 | [ H : In _ ns |- _ ] => clear H
               end
    end; repeat rewrite inBounds_sel in *; evaluate auto_ext;
    repeat match goal with
             | [ H : In _ _ |- _ ] => clear H
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
           end;
    match goal with
      | [ st : (settings * state)%type |- _ ] => destruct st; simpl in *
    end.

  Ltac finish := descend; repeat (step auto_ext; descend); auto.

  Lemma maybeDefinitely : forall cdatas V,
    inBounds cdatas V
    -> maybeInBounds cdatas V.
    red; auto.
  Qed.

  Lemma maybeNope : forall cdatas V,
    sel V "matched" = 0
    -> maybeInBounds cdatas V.
    red; unfold sel; intros.
    rewrite H in H0.
    discriminate.
  Qed.

  Ltac inBounds :=
    try solve [ apply maybeNope; descend ];
    (try apply maybeDefinitely; rewrite <- inBounds_sel;
      repeat match goal with
               | [ H : inBounds _ ?X |- _ ] =>
                 match X with
                   | sel _ => fail 1
                   | _ => rewrite <- inBounds_sel in H
                 end
             end;
      constructor; [ descend |
        match goal with
          | [ H : inBounds _ _, H' : noConflict _ _ |- _ ] =>
            eapply Forall_impl2; [ apply H | apply H' | cbv beta; simpl; intuition descend ]
        end ]).

  Local Hint Extern 1 (@eq W _ _) => unfold natToW in *; words.

  Opaque mult.

  Definition PatR (p : pat) (level : nat) (cdatas : list (string * string)) : chunk.
    refine (WrapC (Pat' p level cdatas)
      (inv cdatas)
      (post (allCdatas p ++ cdatas))
      (PatVcs' p cdatas)
      _ _).

    generalize dependent cdatas; generalize dependent level;
      induction p; (wrap0; (deDouble; simp; evalu; descend;
        (try rewrite maybeInBounds_sel; descend; step auto_ext; eauto; inBounds || finish))).

    admit.
  Defined.

  Notation PatVcs p := (fun ns =>
    (~In "rp" ns) :: In "buf" ns :: In "len" ns :: In "lex" ns :: In "res" ns :: In "matched" ns
    :: (forall x, freeVar p x -> In x ns /\ ~In x baseVars)
    :: wf p
    :: nil).

  Definition Pat (p : pat) : chunk.
    refine (WrapC (PatR p 0 nil)
      (inv nil)
      (post (allCdatas p))
      (PatVcs p)
      _ _).

    wrap0; simp; descend;
    try match goal with
          | [ H : interp _ _ |- _ ] => rewrite maybeInBounds_sel; rewrite maybeInBounds_sel in H
        end; step auto_ext; try fold (@app (string * string)) in *; try rewrite app_nil_r in *; finish.

    wrap0; try (app; subst; tauto); constructor.
  Defined.

End Pat.
