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

              "tagLen" <-- Call "xml_lex"!"tokenLength"("lex")
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
              * [| length bs = wordToNat (V "len") |] * [| inBounds (allCdatas p1 ++ cdatas) V |]
              * [| stackOk ls (V "len") |]
          POST[_] array8 bs (V "buf")];;

          (* Restore the position we popped. *)
          Call "xml_lex"!"setPosition"("lex", "tagLen")
          [inv (allCdatas p1 ++ cdatas)];;

          (* Now try matching the second pattern from the same initial position. *)
          Pat' p2 level (allCdatas p1 ++ cdatas)
          onSuccess
        })
    end%SP.

  Notation baseVars := ("buf" :: "len" :: "lex" :: "res"
    :: "tagStart" :: "tagLen" :: "matched" :: "stack" :: nil).

  Definition noConflict pt := List.Forall (fun p => ~In (fst p) baseVars /\ ~In (snd p) baseVars
    /\ ~freeVar pt (fst p) /\ ~freeVar pt (snd p)).

  Notation "l ~~ im ~~> s" := (LabelMap.find l%SP im = Some (Precondition s None)) (at level 0).

  Notation PatVcs' p cdatas onSuccess := (fun im ns res =>
    (~In "rp" ns) :: incl baseVars ns
    :: (forall x, freeVar p x -> In x ns /\ ~In x baseVars /\ x <> "rp")
    :: wf p
    :: noConflict p cdatas
    :: (forall specs im mn H res pre st,
      interp specs (Postcondition (toCmd onSuccess (im := im) mn H ns res pre) st)
      -> interp specs (inv (allCdatas p ++ cdatas) true (fun w => w) ns res st))
    :: (res >= 11)%nat
    :: "xml_lex"!"next" ~~ im ~~> nextS
    :: "xml_lex"!"position" ~~ im ~~> positionS
    :: "xml_lex"!"setPosition" ~~ im ~~> positionS
    :: "xml_lex"!"tokenStart" ~~ im ~~> tokenStartS
    :: "xml_lex"!"tokenLength" ~~ im ~~> tokenLengthS
    :: "malloc"!"malloc" ~~ im ~~> mallocS
    :: "malloc"!"free" ~~ im ~~> freeS
    :: "sys"!"abort" ~~ im ~~> abortS
    :: (forall specs im mn H res pre,
      (forall st, interp specs (pre st)
        -> interp specs (inv (allCdatas p ++ cdatas) true (fun w => w) ns res st))
      -> vcs (VerifCond (toCmd onSuccess (im := im) mn H ns res pre)))
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
                            | [ H : LabelMap.find _ _ = _ |- _ ] => try rewrite H; clear H
                            | [ H : incl nil _ |- _ ] => clear H
                            | [ H : incl _ _ |- _ ] => apply incl_peel in H; destruct H
                            | [ H : forall x, x = _ \/ x = _ -> _ |- _ ] =>
                              generalize (H _ (or_introl _ eq_refl)); intro;
                                specialize (H _ (or_intror _ eq_refl))
                            | [ H : forall x, freeVar _ _ \/ freeVar _ _ -> _ |- _ ] =>
                              generalize (fun x H0 => H x (or_introl _ H0)); intro;
                                specialize (fun x H0 => H x (or_intror _ H0))
                          end;
  intuition idtac; repeat match goal with
                            | [ H : False -> False |- _ ] => clear H
                          end.

  Lemma mult4_S : forall n,
    4 * S n = S (S (S (S (4 * n)))).
    simpl; intros; omega.
  Qed.

  Ltac evalu :=
    match goal with
      | [ ns : list string |- _ ] =>
        repeat match goal with
                 | [ H : In _ ns |- _ ] => clear H
               end
    end; try rewrite mult4_S in *; repeat rewrite inBounds_sel in *;
    match goal with
      | [ _ : evalInstrs _ _ _ = _ |- _ ] => evaluate auto_ext
      | _ => idtac
    end;
    repeat match goal with
             | [ H : In _ _ |- _ ] => clear H
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
           end;
    try match goal with
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

  Hint Extern 1 (@eq W _ _) => unfold natToW in *; words.

  Opaque mult.

  Lemma stackOk_cons : forall w len ws,
    w <= len
    -> stackOk ws len
    -> stackOk (w :: ws) len.
    constructor; auto.
  Qed.

  Hint Immediate stackOk_cons.

  Ltac noConflict := unfold noConflict; intros; eapply Forall_impl; [ | eauto ]; (cbv beta; simpl; tauto).

  Lemma noConflict_Both1 : forall p1 p2 cdatas,
    noConflict (Both p1 p2) cdatas
    -> noConflict p1 cdatas.
    noConflict.
  Qed.

  Lemma noConflict_Both2' : forall p1 p2 cdatas,
    noConflict (Both p1 p2) cdatas
    -> noConflict p2 cdatas.
    noConflict.
  Qed.

  Ltac allCdatas_freeVar := intros ? p;
    induction p; simpl; intuition; subst; auto;
      match goal with
        | [ H : _ |- _ ] => apply in_app_or in H; tauto
      end.

  Lemma allCdatas_freeVar1 : forall xy p,
    In xy (allCdatas p) -> freeVar p (fst xy).
    allCdatas_freeVar.
  Qed.

  Lemma allCdatas_freeVar2 : forall xy p,
    In xy (allCdatas p) -> freeVar p (snd xy).
    allCdatas_freeVar.
  Qed.

  Lemma noConflict_Both2 : forall p1 p2 cdatas,
    noConflict (Both p1 p2) cdatas
    -> (forall x, freeVar p1 x -> freeVar p2 x -> False)
    -> (forall x, freeVar p1 x -> ~In x baseVars)
    -> noConflict p2 (allCdatas p1 ++ cdatas).
    intros; apply Forall_app.
    2: eapply noConflict_Both2'; eauto.
    apply Forall_forall; intros.
    generalize (allCdatas_freeVar1 _ _ H2); intro.
    apply allCdatas_freeVar2 in H2.
    intuition eauto.
  Qed.

  Hint Immediate noConflict_Both1.
  Hint Extern 1 (noConflict _ (_ ++ _)) => eapply noConflict_Both2; [ eassumption | eassumption |
    simpl; intros; app; tauto ].

  Hint Extern 1 (incl _ _) => hnf; simpl; intuition congruence.

  Lemma Forall_app1 : forall A P (ls1 ls2 : list A),
    List.Forall P (ls1 ++ ls2)
    -> List.Forall P ls1.
    induction ls1; inversion 1; eauto.
  Qed.

  Lemma Forall_app2 : forall A P (ls1 ls2 : list A),
    List.Forall P (ls1 ++ ls2)
    -> List.Forall P ls2.
    induction ls1; inversion 1; eauto.
  Qed.

  Lemma inBounds_app1 : forall ls1 ls2 x,
    inBounds (ls1 ++ ls2) x
    -> inBounds ls1 x.
    intros; eapply Forall_app1; eauto.
  Qed.

  Lemma inBounds_app2 : forall ls1 ls2 x,
    inBounds (ls1 ++ ls2) x
    -> inBounds ls2 x.
    intros; eapply Forall_app2; eauto.
  Qed.

  Hint Immediate inBounds_app1 inBounds_app2.

  Lemma inBounds_decons : forall x cdatas y,
    inBounds (x :: cdatas) y
    -> inBounds cdatas y.
    inversion 1; auto.
  Qed.

  Hint Immediate inBounds_decons.

  Lemma inBounds_assoc : forall ls1 ls2 ls3 x,
    inBounds ((ls1 ++ ls2) ++ ls3) x
    -> inBounds (ls1 ++ ls2 ++ ls3) x.
    intros; rewrite app_assoc; assumption.
  Qed.

  Hint Immediate inBounds_assoc.

  Ltac finale := simp; evalu; try tauto; descend;
    (try rewrite inBounds_sel in *; descend; step SinglyLinkedList.hints;
      try step SinglyLinkedList.hints; eauto; inBounds || finish).

  Ltac PatR_post :=
    match goal with
      | [ H : interp _ (Postcondition _ _) |- _ ] => app
      | [ |- vcs _ ] => wrap0; eauto
      | _ => finale
    end.

  Lemma wplus_wminus : forall u v : W,
    u ^+ v ^- v = u.
    intros; words.
  Qed.

  Hint Rewrite wplus_wminus mult4_S : sepFormula.

  Ltac reger := repeat match goal with
                         | [ H : Regs _ _ = _ |- _ ] => rewrite H
                       end.

  Ltac bash :=
    unfold inv, invP, invL, localsInvariant; try rewrite mult4_S in *; reger; descend;
      try rewrite inBounds_sel; step auto_ext.

  Definition PatR (p : pat) (level : nat) (cdatas : list (string * string))
    (onSuccess : chunk) : chunk.
    refine (WrapC (Pat' p level cdatas onSuccess)
      (inv cdatas)
      (inv cdatas)
      (PatVcs' p cdatas onSuccess)
      _ _).

    admit.
    (*generalize dependent onSuccess; generalize dependent cdatas; generalize dependent level; induction p;
      (wrap0; deDouble; repeat PatR_post).*)

    generalize dependent onSuccess; generalize dependent cdatas; generalize dependent level; induction p.

    wrap0.

    Ltac PatR_vc := deDouble; propxFo; app; simp; evalu; repeat bash; eauto.

    PatR_vc.
    PatR_vc.
    PatR_vc.
    PatR_vc.
    PatR_vc.

    deDouble.
    propxFo.
    app.
    simp.
    evalu.
    descend.
    step auto_ext.
    step auto_ext.
    step auto_ext.
    unfold inv, invP, invL, localsInvariant; try rewrite mult4_S in *; reger; descend.
    step auto_ext.
    unfold inv, invP, invL, localsInvariant; try rewrite mult4_S in *; reger; descend.
    rewrite inBounds_sel.

    assert (inBounds cdatas (upd x4 "res" 2)).
    inBounds.

    Ltac considerImp pre post :=
      try match post with
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
                                    | reflexivity ] ); autorewrite with sepFormula;
                                  generalize dependent vs'; intros
                          end
                      end
                  end
              end
          end;
      try rewrite mult4_S in *;
      progress cancel auto_ext.

    match goal with
      | [ |- interp _ (![?pre]%PropX _ ---> ![?post]%PropX _) ] => considerImp pre post
    end.
    bash.
    repeat bash; auto.

    (* OK, so that was seriously grungy.  The function return logic in PreAutoSep generalizes over
     * a variable environment as an optimization, but here the details of that environment remain
     * relevant, for proving an [inBounds]. *)

    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
  Defined.

  Notation PatVcs p onSuccess := (fun im ns res =>
    (~In "rp" ns) :: incl baseVars ns
    :: (forall x, freeVar p x -> In x ns /\ ~In x baseVars)
    :: wf p
    :: (forall specs im mn H res pre st,
      interp specs (Postcondition (toCmd onSuccess (im := im) mn H ns res pre) st)
      -> interp specs (inv (allCdatas p) true (fun w => w) ns res st))
    :: (res >= 11)%nat
    :: "xml_lex"!"next" ~~ im ~~> nextS
    :: "xml_lex"!"position" ~~ im ~~> positionS
    :: "xml_lex"!"setPosition" ~~ im ~~> positionS
    :: "xml_lex"!"tokenStart" ~~ im ~~> tokenStartS
    :: "xml_lex"!"tokenLength" ~~ im ~~> tokenLengthS
    :: "malloc"!"malloc" ~~ im ~~> mallocS
    :: "malloc"!"free" ~~ im ~~> freeS
    :: "sys"!"abort" ~~ im ~~> abortS
    :: (forall specs im mn H res pre,
      (forall st, interp specs (pre st)
        -> interp specs (inv (allCdatas p) true (fun w => w) ns res st))
      -> vcs (VerifCond (toCmd onSuccess (im := im) mn H ns res pre)))
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
      (try rewrite app_nil_r; app; simp; descend; try rewrite inBounds_sel; finish; constructor).
  Defined.

End Pat.
