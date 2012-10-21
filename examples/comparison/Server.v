Require Import Arith AutoSep Malloc SinglyLinkedList.
Import SinglyLinkedList.SinglyLinkedList.


(* Requests that the server may receive.
 * (W is the type of machine words.) *)
Inductive req :=
| ValueIsGe (index valueLowerBound : W)
(* Test if the value stored at this index is at least as large as this value. *)

| MaxInRange (lowerBound upperBound : W)
(* Find the maximum value within the given range of values. *)

| CollectBelow (indexLowerBound valueUpperBound : W)
(* Collect a list of all values satisfying the given bounds on index and value. *).

(* Mathematical function to represent requests as lists of machine words.
 * (Dollar-sign operator is for machine word constants.) *)
Definition encode (r : req) : list W :=
  match r with
    | ValueIsGe a b => $0 :: a :: b :: nil
    | MaxInRange a b => $1 :: a :: b :: nil
    | CollectBelow a b => $2 :: a :: b :: nil
  end.

Fixpoint encodeAll (rs : list req) : list W :=
  match rs with
    | nil => nil
    | r :: rs' => encode r ++ encodeAll rs'
  end.

(* Helper functions to express semantics of requests *)

Definition valueIsGe (data : list W) (index lower : W) : W :=
  if le_lt_dec (length data) (wordToNat index)
    then $0
    else if wlt_dec (Array.sel data index) lower then $0 else $1.

Definition wmax (w w' : W) : W :=
  if wlt_dec w' w then w' else w.

Fixpoint maxInRange (lower upper : W) (data : list W) : W :=
  match data with
    | nil => O
    | w :: ws =>
      let max := maxInRange lower upper ws in
        if wlt_dec w lower
          then max
          else if wlt_dec upper w
            then max
            else wmax w max
  end.

Fixpoint collectBelow (upper : W) (data acc : list W) : list W :=
  match data with
    | nil => acc
    | w :: ws =>
      if wlt_dec upper w
        then collectBelow upper ws acc
        else collectBelow upper ws (w :: acc)
  end.

(* Mathematical function to compute the proper response to a request,
 * in terms of a transformation on a list of output values. *)
Definition response (data : list W) (acc : list W) (r : req) : list W :=
  match r with
    | ValueIsGe index lower => valueIsGe data index lower :: acc
    | MaxInRange lower upper =>
      maxInRange lower upper data :: acc
    | CollectBelow lower upper =>
      collectBelow upper (firstn (wordToNat lower) data) acc
  end.

Definition responseAll (data : list W) (rs : list req) (acc : list W) :=
  fold_left (response data) rs acc.

Definition mainS := SPEC("cmd", "cmdLen", "data", "dataLen") reserving 13
  Al r, Al d,
  PRE[V] array (encodeAll r) (V "cmd") * array d (V "data") * mallocHeap
    * [| V "cmdLen" = length (encodeAll r) |] * [| V "dataLen" = length d |]
    * [| goodSize (length (encodeAll r) + 3) |]
  POST[R] array (encodeAll r) (V "cmd") * array d (V "data") * mallocHeap
    * sll (responseAll d r nil) R.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS] ]]
  bmodule "m" {{
    bfunction "main"("cmd", "cmdLen", "data", "dataLen",
                     "output", "position", "posn", "lower", "upper",
                     "index", "value", "res") [mainS]
      "output" <- 0;;
      "position" <- 0;;

      [Al rdone, Al r, Al d, Al out,
       PRE[V] array (rdone ++ encodeAll r) (V "cmd") * array d (V "data") * mallocHeap
         * sll out (V "output") * [| V "position" = length rdone |]
         * [| V "cmdLen" = (length rdone + length (encodeAll r))%nat |] * [| V "dataLen" = length d |]
         * [| goodSize (length rdone + length (encodeAll r) + 3) |]
       POST[R] array (rdone ++ encodeAll r) (V "cmd") * array d (V "data") * mallocHeap
         * sll (responseAll d r out) R]
      While ("position" < "cmdLen") {
        Match "cmd" Size "cmdLen" Position "position" {
          (* ValueIsGe *)
          Case (0 ++ "posn" ++ "lower")
            "res" <- 0;;

            [Al rdone, Al r, Al out,
              After prefix Approaching all
                PRE[V] array (rdone ++ encodeAll (ValueIsGe (V "posn") (V "lower") :: r)) (V "cmd")
                  * mallocHeap * sll out (V "output") * [| V "position" = natToW (length rdone + 3) |]
                  * [| V "cmdLen" = (length rdone + 3 + length (encodeAll r))%nat |]
                  * [| V "dataLen" = length all |]
                  * [| V "res" = valueIsGe prefix (V "posn") (V "lower") |]
                  * [| goodSize (length rdone + 3 + length (encodeAll r) + 3) |]
                POST[R] array (rdone ++ encodeAll (ValueIsGe (V "posn") (V "lower") :: r)) (V "cmd")
                  * mallocHeap * sll (responseAll all (ValueIsGe (V "posn") (V "lower") :: r) out) R ]
            For "index" Holding "value" in "data" Size "dataLen"
              Where ((Index = "posn") && (Value >= "lower")) {
              Diverge
            };;

            Diverge
          end;;

          (* MaxInRange *)
          Case (1 ++ "lower" ++ "upper")
            Diverge
          end;;

          (* CollectBelow *)
          Case (2 ++ "lower" ++ "upper")
            Diverge
          end
        } Default {
          Diverge
        }
      };;

      Return "output"
    end
  }}.

Lemma length_nil : forall A,
  0 = length (@nil A).
  reflexivity.
Qed.

Hint Resolve length_nil.

Lemma responseAll_nil : forall data rs acc,
  length (encodeAll rs) = 0
  -> responseAll data rs acc = acc.
  destruct rs as [ | [ ] ]; simpl; intuition.
Qed.

Hint Extern 1 (length _ = 0) =>
  match goal with
    | [ H : _ <= _ |- _ ] => eapply wle_goodSize in H; [ omega | | ];
      eapply goodSize_weaken; eauto      
  end.

Hint Rewrite responseAll_nil using solve [ auto ] : Server.

Hint Rewrite natToW_plus : Server.

Lemma triple' : forall (x : W) y,
  x ^+ natToW (S (S (S y))) = x ^+ $3 ^+ natToW y.
  intros; do 3 match goal with
                 | [ |- context[S ?X] ] => rewrite (natToW_S X)
               end; words.
Qed.

Lemma triple : forall (x : W) (ws : list W),
  x ^+ natToW (S (S (S (length ws)))) = x ^+ $3 ^+ natToW (length ws).
  intros; rewrite triple'; auto.
Qed.

Hint Rewrite triple : Server.

Ltac eta_evar T k :=
  match eval cbv beta in T with
    | unit => k tt
    | @sigT ?A ?F =>
      let x' := fresh in evar (x' : A); let x := eval unfold x' in x' in clear x';
        eta_evar (F x) ltac:(fun v => k (existT F x v))
    | _ =>
      idtac "BYE";
        let x' := fresh in evar (x' : T); let x := eval unfold x' in x' in clear x';
          k x
  end.

Ltac parse1 solver :=
  match goal with
    | [ H : forall (a : _ -> _), _ |- _ ] =>
      especialize H; post;
      match goal with
        | [ H : interp ?specs (?P ---> ?Q)%PropX |- _ ] =>
          let H' := fresh in assert (H' : interp specs P) by (propxFo; step auto_ext || solver);
            specialize (Imply_sound H H'); clear H H'; intro H
      end; propxFo; autorewrite with StreamParse in *; simpl in *

    | [ H : interp _ (![ _ ] _) |- _ ] => eapply Wrap.sepFormula_Mem in H; [ | eassumption ]
  end.

Lemma suffix_app' : forall (ls2 ls1 : list W),
  suffix (length ls1) (ls1 ++ ls2) = ls2.
  induction ls1; simpl; intuition.
Qed.

Lemma suffix_app : forall (ls1 ls2 : list W) (v : W),
  v = natToW (length ls1)
  -> goodSize (length ls1)
  -> suffix (wordToNat v) (ls1 ++ ls2) = ls2.
  intros; subst; rewrite wordToNat_natToW_goodSize; auto; apply suffix_app'.
Qed.

Ltac use_match := try rewrite suffix_app in * by (assumption || eapply goodSize_weaken; eauto);
  try match goal with
        | [ H : match encodeAll ?E with nil => False | _ => _ end |- _ ] =>
          destruct E as [ | [ ] ]; simpl in *; intuition (try discriminate); subst
      end; reveal_slots; evaluate hints.

Ltac multi_ex :=
  try match goal with
        | [ _ : sigT _ |- _ ] =>
          repeat match goal with
                   | [ x : sigT _ |- _ ] => destruct x
                 end; simpl in *
      end;
  try match goal with
        | [ |- @Logic.ex ?T _ ] =>
          match T with
            | sigT _ => eta_evar T ltac:(fun v => exists v; simpl)
          end
      end.

Hint Rewrite app_length : Server.

Ltac finish :=
  repeat match goal with
           | [ H : sel _ _ = _ |- _ ] => rewrite H in *
           | [ H : Regs _ _ = sel _ _ |- _ ] => rewrite H in *
         end; try rewrite wordToNat_natToW_goodSize by (eapply goodSize_weaken; eauto);
  eauto; autorewrite with Server; simpl; autorewrite with Server; eauto; simpl;
    try solve [ auto | eapply goodSize_weaken; eauto | step hints ].


Lemma switch_sides : forall w n,
  wordToNat w = n
  -> natToW n = w.
  intros; subst; apply natToWord_wordToNat.
Qed.

Hint Immediate switch_sides.

Hint Extern 1 (weqb _ _ = true) => apply weqb_true_iff.
Hint Resolve wleb_true.

Lemma selN_beginning : forall (w : W) (ws' : list W) (ws : list W) i,
  (i < length ws)%nat
  -> Array.selN (ws ++ w :: ws') i = Array.selN ws i.
  induction ws; destruct i; simpl; intuition.
Qed.

Lemma sel_beginning : forall (ws : list W) (w : W) (ws' : list W) i,
  goodSize (length ws)
  -> i < natToW (length ws)
  -> Array.sel (ws ++ w :: ws') i = Array.sel ws i.
  unfold Array.sel; intros; apply selN_beginning; nomega.
Qed.

Lemma valueIsGe_skip : forall v ws this posn lower,
  v = valueIsGe ws posn lower
  -> goodSize (length ws)
  -> (weqb (length ws) posn = true -> wleb lower this = true -> False)
  -> v = valueIsGe (ws ++ this :: nil) posn lower.
  unfold valueIsGe; intros; autorewrite with Server; simpl.
  destruct (le_lt_dec (length ws) (wordToNat posn));
    destruct (le_lt_dec (length ws + 1) (wordToNat posn)); auto; try omega; [
      assert (wordToNat posn = length ws) by omega;
        replace posn with (natToW (length ws)) by auto;
          rewrite sel_middle by auto;
            destruct (wlt_dec this lower); eauto; elimtype False; eauto
      | destruct (eq_nat_dec (wordToNat posn) (length ws)); [
        replace posn with (natToW (length ws)) by auto;
          rewrite sel_middle by auto; nomega
        | rewrite sel_beginning; auto; nomega ] ].
Qed.

Hint Immediate valueIsGe_skip.


Theorem ok : moduleOk m.
Proof.
  vcgen; parse0; for0.

  Ltac t := post; evaluate hints; repeat (parse1 finish; use_match); multi_ex; sep hints; finish.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
Qed.
