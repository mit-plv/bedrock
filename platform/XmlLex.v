Require Import AutoSep Malloc MoreArrays.


(** Basic token-level XML parsing *)

Module Type XMLP.
  Variable xmlp : W -> W -> HProp.

  Axiom xmlp_fwd : forall len p, xmlp len p
    ===> Ex pos, Ex selStart, Ex selLen, (p ==*> len, pos, selStart, selLen)
    * [| pos <= len |] * [| (wordToNat selStart + wordToNat selLen <= wordToNat len)%nat |]
    * [| p <> 0 |] * [| freeable p 4 |].

  Axiom xmlp_bwd : forall len p, (Ex pos, Ex selStart, Ex selLen, (p ==*> len, pos, selStart, selLen)
    * [| pos <= len |] * [| (wordToNat selStart + wordToNat selLen <= wordToNat len)%nat |]
    * [| p <> 0 |] * [| freeable p 4 |]) ===> xmlp len p.
End XMLP.

Module Xmlp : XMLP.
  Open Scope Sep_scope.

  Definition xmlp (len p : W) : HProp :=
    Ex pos, Ex selStart, Ex selLen, (p ==*> len, pos, selStart, selLen)
    * [| pos <= len |] * [| (wordToNat selStart + wordToNat selLen <= wordToNat len)%nat |]
    * [| p <> 0 |] * [| freeable p 4 |].

  Theorem xmlp_fwd : forall len p, xmlp len p
    ===> Ex pos, Ex selStart, Ex selLen, (p ==*> len, pos, selStart, selLen)
    * [| pos <= len |] * [| (wordToNat selStart + wordToNat selLen <= wordToNat len)%nat |]
    * [| p <> 0 |] * [| freeable p 4 |].
    unfold xmlp; sepLemma.
  Qed.

  Theorem xmlp_bwd : forall len p, (Ex pos, Ex selStart, Ex selLen, (p ==*> len, pos, selStart, selLen)
    * [| pos <= len |] * [| (wordToNat selStart + wordToNat selLen <= wordToNat len)%nat |]
    * [| p <> 0 |] * [| freeable p 4 |]) ===> xmlp len p.
    unfold xmlp; sepLemma.
  Qed.
End Xmlp.

Import Xmlp.
Export Xmlp.

Definition hints : TacPackage.
  prepare xmlp_fwd xmlp_bwd.
Defined.


(** * Specs *)

Require Import Ascii.
Definition W_of_ascii (ch : ascii) : W := N_of_ascii ch.
Coercion W_of_ascii : ascii >-> W.

Definition initS := SPEC("len") reserving 8
  PRE[V] mallocHeap 0
  POST[R] xmlp (V "len") R * mallocHeap 0.

Definition deleteS := SPEC("p") reserving 6
  Al len,
  PRE[V] xmlp len (V "p") * mallocHeap 0
  POST[_] mallocHeap 0.

Definition nextS := SPEC("buf", "p") reserving 8
  Al bs, Al len,
  PRE[V] array8 bs (V "buf") * xmlp len (V "p") * [| length bs = wordToNat len |]
  POST[_] array8 bs (V "buf") * xmlp len (V "p").
(* Return value is:
   0: done parsing
   1: read an open tag
   2: read CDATA
   3: read a close tag
   4: read a <? ... ?> tag *)


(** * Implementation *)

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "xmlparse" {{
    bfunction "init"("len", "r") [initS]
      "r" <-- Call "malloc"!"malloc"(0, 4)
      [PRE[V, R] [| R <> 0 |] * [| freeable R 4 |] * R =?> 4
       POST[R'] xmlp (V "len") R'];;

      "r" *<- "len";;
      "r"+4 *<- 0;;
      "r"+8 *<- 0;;
      "r"+12 *<- 0;;
      Return "r"
    end with bfunction "delete"("p") [deleteS]
      Call "malloc"!"free"(0, "p", 4)
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
    end with bfunction "next"("buf", "p", "len", "pos", "start", "ch") [nextS]
      "len" <-* "p";;
      "pos" <-* "p"+4;;
      "start" <- "pos";;

      [Al bs, Al pos, Al selStart, Al selLen,
        PRE[V] (V "p" ==*> V "len", pos, selStart, selLen) * [| length bs = wordToNat (V "len") |]
          * [| V "p" <> 0 |] * [| freeable (V "p") 4 |] * [| V "start" <= V "pos" |]%word
          * [| V "pos" <= V "len" |]%word * array8 bs (V "buf")
        POST[_] array8 bs (V "buf") * xmlp (V "len") (V "p")]
      While ("pos" < "len") {
        Assert [Al bs, Al pos, Al selStart, Al selLen,
          PRE[V] (V "p" ==*> V "len", pos, selStart, selLen) * [| length bs = wordToNat (V "len") |]
            * [| V "pos" < natToW (length bs) |]%word
            * [| V "p" <> 0 |] * [| freeable (V "p") 4 |] * [| V "start" <= V "pos" |]%word
            * array8 bs (V "buf")
          POST[_] array8 bs (V "buf") * xmlp (V "len") (V "p")];;

        "ch" <- "buf" + "pos";;
        "ch" <-*8 "ch";;

        If ("ch" = " "%char) {
          Skip
        } else {
          If ("ch" = 9 (* tab *)) {
            Skip
          } else {
            If ("ch" = 10 (* newline *)) {
              Skip
            } else {
              If ("ch" = 13 (* carriage return [yes, we still need to handle this in 2013 (?!?!)] *)) {
                Skip
              } else {
                If ("ch" = "<"%char) {
                  (* Found a tag! *)

                  Diverge
                } else {
                  (* Found CDATA! *)

                  "p"+8 *<- "start";;
                  "pos" <- "pos" + 1;;
                  [Al bs, Al pos, Al selLen,
                    PRE[V] (V "p" ==*> V "len", pos, V "start", selLen) * [| length bs = wordToNat (V "len") |]
                      * [| V "p" <> 0 |] * [| freeable (V "p") 4 |] * [| (V "start" <= V "pos")%word |]
                      * [| (V "pos" <= V "len")%word |] * array8 bs (V "buf")
                    POST[_] array8 bs (V "buf") * xmlp (V "len") (V "p")]
                  While ("pos" < "len") {
                    Assert [Al bs, Al pos, Al selLen,
                      PRE[V] (V "p" ==*> V "len", pos, V "start", selLen) * [| length bs = wordToNat (V "len") |]
                        * [| V "pos" < natToW (length bs) |]%word
                        * [| V "p" <> 0 |] * [| freeable (V "p") 4 |] * [| (V "start" <= V "pos")%word |]
                        * [| (V "pos" <= V "len")%word |] * array8 bs (V "buf")
                      POST[_] array8 bs (V "buf") * xmlp (V "len") (V "p")];;

                    "ch" <- "buf" + "pos";;
                    "ch" <-*8 "ch";;

                    If ("ch" = "<"%char) {
                      (* End of CDATA. *)

                      "p"+4 *<- "pos";;
                      "pos" <- "pos" - "start";;
                      "p"+12 *<- "pos";;
                      Return 2
                    } else {
                      "pos" <- "pos" + 1
                    }
                  };;

                  "p"+4 *<- "len";;
                  "len" <- "len" - "start";;
                  "p"+12 *<- "len";;
                  Return 2
                }
              }
            }
          }
        };;

        "pos" <- "pos" + 1
      };;

      "p"+4 *<- "len";;
      "p"+8 *<- "len";;
      "p"+12 *<- 0;;
      Return 0
    end
  }}.


(** * Proof *)

Local Hint Extern 1 (@eq W _ _) => words.

Lemma zero_le : forall w : W, natToW 0 <= w.
  intros; pre_nomega; rewrite roundTrip_0; auto.
Qed.

Local Hint Immediate zero_le.

Hint Rewrite roundTrip_0 : N.

Lemma wle_plus1 : forall u v w,
  u <= v
  -> v < w
  -> u <= v ^+ natToW 1.
  intros; pre_nomega; rewrite wordToNat_wplus; auto;
    apply goodSize_weaken with (wordToNat w); eauto; rewrite roundTrip_1; auto.
Qed.

Lemma quite_so_old_fellow : forall pos n n',
  pos < n'
  -> n = wordToNat n'
  -> pos < natToW n.
  intros; subst; unfold natToW; rewrite natToWord_wordToNat; auto.
Qed.

Local Hint Immediate wle_plus1 quite_so_old_fellow inc.

Ltac t := sep hints; eauto; nomega || rewrite wordToNat_wminus; nomega.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.
