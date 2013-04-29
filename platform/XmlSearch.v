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
  (* Do all start-length pairs in a list denote valid spans in a string of length "len"? *)
  Definition inBounds (cdatas : list (string * string)) (V : vals) :=
    List.Forall (fun p => wordToNat (V (fst p)) + wordToNat (V (snd p)) <= wordToNat (V "len"))%nat
    cdatas.

  (* Are all saved positions in a list valid pointers within a string of a given length? *)
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

  (* Alternate sequencing operator, which generates twistier code but simpler postconditions and VCs *)
  Definition SimpleSeq (ch1 ch2 : chunk) : chunk := fun ns res =>
    Structured nil (fun im mn H => Seq_ H (toCmd ch1 mn H ns res) (toCmd ch2 mn H ns res)).

  Infix ";;" := SimpleSeq : SP_scope.

  (* Workhorse pattern compilation function, taking as input:
   * p: an XML pattern to compile
   * level: tree depth at which this pattern is applied (starts at 1 for top-level pattern)
   * cdatas: list of start-length pairs denoting spans within the string we match against,
   *         set by earlier successfull matches of subpatterns
   * onSuccess: continuation code to run when the pattern matches fully
   *)
  Fixpoint Pat' (p : pat) (level : nat) (cdatas : list (string * string))
    (onSuccess : chunk) : chunk :=
    match p with
      | Cdata start len =>
        (* Read next token. *)
        "res" <-- Call "xml_lex"!"next"("buf", "lex")
        [inv cdatas];;

        (* What type of token is it? *)
        If ("res" = 2) {
          (* This is indeed CDATA!  Save the position and signal success. *)
          start <-- Call "xml_lex"!"tokenStart"("lex")
          [invP cdatas];;

          len <-- Call "xml_lex"!"tokenLength"("lex")
          [invL cdatas start];;

          onSuccess
        } else {
          (* It's not CDATA.  Pattern doesn't match. *)
          Skip
        }

      | Tag tag inner =>
        (* Initialize a variable storing the tree depth of our current position.
         * We'll consult this variable to see when we're at the proper depth for matching
         * the current pattern. *)
        "level" <- level;;

        (* Loop until level drops below the starting level (after which the pattern never applies again). *)
        [inv cdatas]
        While ("level" >= level) {
          (* Lex next token. *)
          "res" <-- Call "xml_lex"!"next"("buf", "lex")
          [inv cdatas];;

          (* What type of token is it? *)
          If ("res" = 1) {
            (* Open tag -- does it match? *)
            "level" <- "level" + 1;;

            If ("level" > level) {
              (* We've descended too deep, so this position doesn't qualify. *)
              Skip
            } else {
              (* We may have a match!  First, grab the boundaries of the matching string. *)
              "tagStart" <-- Call "xml_lex"!"tokenStart"("lex")
              [invP cdatas];;

              "tagLen" <-- Call "xml_lex"!"tokenStart"("lex")
              [invL cdatas "tagStart"];;

              (* Now check if the tag name here matches the name from the pattern. *)
              StringEq "buf" "len" "tagStart" "matched" tag
              (A := unit)
              (fun _ V => xmlp (V "len") (V "lex")
                * [| inBounds cdatas V |])%Sep
              (fun _ V _ => xmlp (V "len") (V "lex")
                * [| inBounds cdatas V |])%Sep;;

              If ("matched" = 0) {
                (* Nope, not equal. *)
                Skip
              } else {
                (* Equal!  Continue with the nested pattern. *)
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
                (* Ignore any other kind of token. *)
                Skip
              }
            }
          }
        }

      | Both p1 p2 =>
        (* Warning: shameless reuse here of variables for new purposes *)

        (* Get the current position, which we will save to return to later. *)
        "tagLen" <-- Call "xml_lex"!"position"("lex")
        [Al bs, Al ls,
          PRE[V, R] array8 bs (V "buf") * xmlp (V "len") (V "lex")
            * sll ls (V "stack") * [| R <= V "len" |]%word
            * [| length bs = wordToNat (V "len") |] * [| inBounds cdatas V |]
            * [| stackOk ls (V "len") |]
          POST[_] array8 bs (V "buf")];;

        (* Allocate a new entry for the position stack. *)
        "tagStart" <-- Call "malloc"!"malloc"(0, 2)
        [Al bs, Al ls,
          PRE[V, R] array8 bs (V "buf") * xmlp (V "len") (V "lex")
            * sll ls (V "stack") * [| V "tagLen" <= V "len" |]%word
            * R =?> 2 * [| R <> 0 |] * [| freeable R 2 |]
            * [| length bs = wordToNat (V "len") |] * [| inBounds cdatas V |]
            * [| stackOk ls (V "len") |]
          POST[_] array8 bs (V "buf")];;

        (* Save the current position in this entry, then push it onto the stack. *)
        "tagStart" *<- "tagLen";;
        "tagStart"+4 *<- "stack";;
        "stack" <- "tagStart";;

        (* Try matching the first pattern. *)
        Pat' p1 level cdatas
        ((* Make sure the stack is nonempty afterward.
          * Only buggy code here could lead to that outcome, but we aren't verifying at that level
          * of detail yet, so we use a run-time check. *)
        If ("stack" = 0) {
          (* We hope this case is impossible. *)
          Call "sys"!"abort"()
          [PREonly[_] [| False |]]
        } else {
          (* Stack nonempty!  Pop position off of stack (into "tagLen"). *)
          "tagLen" <-* "stack";;
          "tagStart" <- "stack";;
          "stack" <-* "stack"+4;;

          (* Free the popped stack entry. *)
          Call "malloc"!"free"(0, "tagStart", 2)
          [Al bs, Al ls,
            PRE[V] array8 bs (V "buf") * xmlp (V "len") (V "lex")
              * sll ls (V "stack") * [| V "tagLen" <= V "len" |]%word
              * [| length bs = wordToNat (V "len") |] * [| inBounds cdatas V |]
              * [| stackOk ls (V "len") |]
          POST[_] array8 bs (V "buf")];;

          (* Restore the position we popped. *)
          Call "xml_lex"!"setPosition"("lex", "tagLen")
          [inv cdatas];;

          (* Now try matching the second pattern from the same initial position. *)
          Pat' p2 level (allCdatas p1 ++ cdatas)
          onSuccess
        })
    end%SP.

  Notation baseVars := ("buf" :: "len" :: "lex" :: "res"
    :: "tagStart" :: "tagLen" :: "matched" :: "stack" :: nil).

  Definition noConflict pt := List.Forall (fun p => ~In (fst p) baseVars /\ ~In (snd p) baseVars
    /\ ~freeVar pt (fst p) /\ ~freeVar pt (snd p)).

  Notation PatVcs' p cdatas onSuccess := (fun ns =>
    (~In "rp" ns) :: incl baseVars ns
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

  Lemma incl_peel : forall A (x : A) ls ls',
    incl (x :: ls) ls'
    -> In x ls' /\ incl ls ls'.
    unfold incl; intuition.
  Qed.

  Ltac deDouble := repeat match goal with
                            | [ H : incl nil _ |- _ ] => clear H
                            | [ H : incl _ _ |- _ ] => apply incl_peel in H; destruct H
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

  Lemma stackOk_cons : forall w len ws,
    w <= len
    -> stackOk ws len
    -> stackOk (w :: ws) len.
    constructor; auto.
  Qed.

  Local Hint Immediate stackOk_cons.

  Definition PatR (p : pat) (level : nat) (cdatas : list (string * string))
    (onSuccess : chunk) : chunk.
    refine (WrapC (Pat' p level cdatas onSuccess)
      (inv cdatas)
      (inv cdatas)
      (PatVcs' p cdatas onSuccess)
      _ _).

    generalize dependent onSuccess; generalize dependent cdatas; generalize dependent level; induction p;
      wrap0; deDouble.

    Ltac t := simp; evalu; descend; (try rewrite inBounds_sel; descend; step SinglyLinkedList.hints;
      try step SinglyLinkedList.hints; eauto; inBounds || finish).

    try solve [ app; simp ]; t.
    try solve [ app; simp ]; t.

    app.
    t.
    t.
    admit.

    admit.
  Defined.

  Notation PatVcs p onSuccess := (fun ns =>
    (~In "rp" ns) :: incl baseVars ns
    :: (forall x, freeVar p x -> In x ns /\ ~In x baseVars)
    :: wf p
    :: (forall specs im mn H res pre st,
      interp specs (Postcondition (toCmd onSuccess (im := im) mn H ns res pre) st)
      -> interp specs (invar true (fun w => w) ns res st))
    :: nil).

  Definition Pat (p : pat) (onSuccess : chunk) : chunk.
    refine (WrapC (PatR p 1 nil onSuccess)
      invar
      invar
      (PatVcs p onSuccess)
      _ _).

    wrap0; simp; descend;
    try match goal with
          | [ H : interp _ _ |- _ ] => rewrite inBounds_sel in H
        end; step auto_ext; try fold (@app (string * string)) in *; try rewrite app_nil_r in *; finish.

    wrap0; try (app; subst; tauto); try constructor;
      (app; simp; descend; try rewrite inBounds_sel; finish; constructor).
  Defined.

End Pat.
