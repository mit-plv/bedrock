Require Import AutoSep Wrap StringMatch XmlLex SinglyLinkedList Malloc.

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

  Definition stackOk (ls : list W) (len : W) :=
    List.Forall (fun x => x <= len) ls.

  (* Precondition and postcondition of search *)
  Definition invar :=
    Al bs, Al ls,
    PRE[V] array8 bs (V "buf") * xmlp (V "len") (V "lex") * sll ls (V "stack")
      * [| length bs = wordToNat (V "len") |] * [| stackOk ls (V "len") |]
    POST[_] array8 bs (V "buf").

  (* Primary invariant, recording that a set of CDATA positions is in bounds. *)
  Definition inv cdatas :=
    Al bs, Al ls,
    PRE[V] array8 bs (V "buf") * xmlp (V "len") (V "lex") * sll ls (V "stack")
      * [| length bs = wordToNat (V "len") |] * [| inBounds cdatas V |]
      * [| stackOk ls (V "len") |]
    POST[_] array8 bs (V "buf").

  (* Intermediate invariant, to use right after reading token position from the lexer. *)
  Definition invP cdatas :=
    Al bs, Al ls,
    PRE[V, R] array8 bs (V "buf") * xmlp' (V "len") R (V "lex")
      * sll ls (V "stack")
      * [| length bs = wordToNat (V "len") |] * [| inBounds cdatas V |]
      * [| stackOk ls (V "len") |]
    POST[_] array8 bs (V "buf").

  (* Intermediater invariant, to use right after reading token length from the lexer. *)
  Definition invL cdatas start :=
    Al bs, Al ls,
    PRE[V, R] array8 bs (V "buf") * xmlp (V "len") (V "lex") * sll ls (V "stack")
      * [| length bs = wordToNat (V "len") |] * [| inBounds cdatas V |]
      * [| stackOk ls (V "len") |]
      * [| wordToNat (V start) + wordToNat R <= wordToNat (V "len") |]%nat
    POST[_] array8 bs (V "buf").

  Fixpoint Pat' (p : pat) (level : nat) (cdatas : list (string * string))
    (onSuccess : chunk) : chunk :=
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

          onSuccess
        } else {
          Skip
        }

      | Tag tag inner =>
        "level" <- level;;

        [inv cdatas]
        While ("level" >= level) {
          "res" <-- Call "xml_lex"!"next"("buf", "lex")
          [inv cdatas];;

          If ("res" = 1) {
            (* Open tag -- does it match? *)
            "level" <- "level" + 1;;

            If ("level" > level) {
              (* We've descended too deep, so this position doesn't qualify. *)
              Skip
            } else {
              "tagStart" <-- Call "xml_lex"!"tokenStart"("lex")
              [invP cdatas];;

              "tagLen" <-- Call "xml_lex"!"tokenStart"("lex")
              [invL cdatas "tagStart"];;

              StringEq "buf" "len" "tagStart" "matched" tag
              (A := unit)
              (fun _ V => xmlp (V "len") (V "lex")
                * [| inBounds cdatas V |])%Sep
              (fun _ V _ => xmlp (V "len") (V "lex")
                * [| inBounds cdatas V |])%Sep;;

              If ("matched" = 0) {
                Skip
              } else {
                Pat' inner (S level) cdatas onSuccess
              }
            }
          } else {
            If ("res" = 3) {
              (* Close tag *)
              "level" <- "level" - 1
            } else {
              If ("res" = 0) {
                (* Done parsing.  Force exit from the loop. *)
                "level" <- 0
              } else {
                Skip
              }
            }
          }
        }

      | Both p1 p2 =>
        (* Warning: shameless reuse here of variables for new purposes *)

        "tagLen" <-- Call "xml_lex"!"position"("lex")
        [Al bs, Al ls,
          PRE[V, R] array8 bs (V "buf") * xmlp (V "len") (V "lex")
            * sll ls (V "stack") * [| R <= V "len" |]%word
            * [| length bs = wordToNat (V "len") |] * [| inBounds cdatas V |]
            * [| stackOk ls (V "len") |]
          POST[_] array8 bs (V "buf")];;

        "tagStart" <-- Call "malloc"!"malloc"(0, 2)
        [Al bs, Al ls,
          PRE[V, R] array8 bs (V "buf") * xmlp (V "len") (V "lex")
            * sll ls (V "stack") * [| V "tagLen" <= V "len" |]%word
            * [| R <> 0 |] * [| freeable R 2 |]
            * [| length bs = wordToNat (V "len") |] * [| inBounds cdatas V |]
            * [| stackOk ls (V "len") |]
          POST[_] array8 bs (V "buf")];;

        "tagStart" *<- "tagLen";;
        "tagStart" *<- "stack";;
        "stack" <- "tagStart";;

        Pat' p1 level cdatas
        (If ("stack" = 0) {
          Call "sys"!"abort"()
          [PREonly[_] [| False |]]
        } else {
          "tagLen" <-* "stack";;
          "tagStart" <- "stack";;
          "stack" <-* "stack"+4;;

          Call "malloc"!"free"(0, "tagStart", 2)
          [Al bs, Al ls,
            PRE[V] array8 bs (V "buf") * xmlp (V "len") (V "lex")
              * sll ls (V "stack") * [| V "tagLen" <= V "len" |]%word
              * [| length bs = wordToNat (V "len") |] * [| inBounds cdatas V |]
              * [| stackOk ls (V "len") |]
          POST[_] array8 bs (V "buf")];;

          Call "xml_lex"!"setPosition"("lex", "tagLen")
          [inv cdatas];;

          Pat' p2 level (allCdatas p1 ++ cdatas)
          onSuccess
        })
    end%SP.

  Notation baseVars := ("buf" :: "len" :: "lex" :: "res"
    :: "tagStart" :: "tagLen" :: "matched" :: nil).

  Definition noConflict pt := List.Forall (fun p => ~In (fst p) baseVars /\ ~In (snd p) baseVars
    /\ ~freeVar pt (fst p) /\ ~freeVar pt (snd p)).

  Notation PatVcs' p cdatas onSuccess := (fun ns =>
    (~In "rp" ns) :: In "buf" ns :: In "len" ns :: In "lex" ns :: In "res" ns :: In "matched" ns
    :: (forall x, freeVar p x -> In x ns /\ ~In x baseVars /\ x <> "rp")
    :: wf p
    :: noConflict p cdatas
    :: (forall specs im mn H res pre st,
      interp specs (Postcondition (toCmd onSuccess (im := im) mn H ns res pre) st)
      -> interp specs (inv cdatas true (fun w => w) ns res st))
    :: nil).

  Lemma inBounds_sel : forall cdatas V, inBounds cdatas (sel V) = inBounds cdatas V.
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

  Ltac inBounds :=
    rewrite <- inBounds_sel;
      repeat match goal with
               | [ H : inBounds _ ?X |- _ ] =>
                 match X with
                   | sel _ => fail 1
                   | _ => rewrite <- inBounds_sel in H
                 end
             end;
      try (constructor; [ descend | ]);
        match goal with
          | [ H : inBounds _ _, H' : noConflict _ _ |- _ ] =>
            eapply Forall_impl2; [ apply H | apply H' | cbv beta; simpl; intuition descend ]
        end.

  Local Hint Extern 1 (@eq W _ _) => unfold natToW in *; words.

  Opaque mult.

  Definition PatR (p : pat) (level : nat) (cdatas : list (string * string))
    (onSuccess : chunk) : chunk.
    refine (WrapC (Pat' p level cdatas onSuccess)
      (inv cdatas)
      (inv cdatas)
      (PatVcs' p cdatas onSuccess)
      _ _).

    generalize dependent cdatas; generalize dependent level; induction p;
      (wrap0; deDouble; try solve [ app; simp ];
        simp; evalu; descend; (try rewrite inBounds_sel; descend; step auto_ext; eauto; inBounds || finish)).

    admit.
  Defined.

  Notation PatVcs p := (fun ns =>
    (~In "rp" ns) :: In "buf" ns :: In "len" ns :: In "lex" ns :: In "res" ns :: In "matched" ns
    :: (forall x, freeVar p x -> In x ns /\ ~In x baseVars)
    :: wf p
    :: (forall specs im mn H res pre st,
      interp specs (Postcondition (toCmd onSuccess (im := im) mn H ns res pre) st)
      -> interp specs (invar true (fun w => w) ns res st))
    :: nil).

  Definition Pat (p : pat) : chunk.
    refine (WrapC (PatR p 1 nil)
      invar
      invar
      (PatVcs p)
      _ _).

    wrap0; simp; descend;
    try match goal with
          | [ H : interp _ _ |- _ ] => rewrite inBounds_sel in H
        end; step auto_ext; try fold (@app (string * string)) in *; try rewrite app_nil_r in *; finish.

    wrap0; try (app; subst; tauto); try constructor;
      (app; simp; descend; try rewrite inBounds_sel; finish; constructor).
  Defined.

End Pat.
