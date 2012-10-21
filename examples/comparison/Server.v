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

Definition wmax (w w' : W) : W :=
  if wlt_dec w' w then w' else w.

Fixpoint maxInRange (lower upper : W) (data : list W) : W :=
  match data with
    | nil => O
    | w :: ws =>
      let max := maxInRange lower upper ws in
        if wlt_dec w lower
          then if wlt_dec upper w
            then wmax w max
            else max
          else max
  end.

Fixpoint collectBelow (upper : W) (data acc : list W) : list W :=
  match data with
    | nil => acc
    | w :: ws =>
      if wlt_dec upper w
        then collectBelow upper ws (w :: acc)
        else collectBelow upper ws acc
  end.

(* Mathematical function to compute the proper response to a request,
 * in terms of a transformation on a list of output values. *)
Definition response (data : list W) (acc : list W) (r : req) : list W :=
  match r with
    | ValueIsGe index lower =>
      if le_lt_dec (length data) (wordToNat index)
        then acc
        else if wlt_dec (Array.sel data index) lower
          then $1 :: acc
          else $0 :: acc
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
                    "output", "position", "posn", "lower", "upper") [mainS]
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
          Case (0 ++ "posn" ++ "lower")
            Diverge
          end;;
          Case (1 ++ "lower" ++ "upper")
            Diverge
          end;;
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

Ltac finish :=
  repeat match goal with
           | [ H : sel _ _ = _ |- _ ] => rewrite H in *
           | [ H : Regs _ _ = sel _ _ |- _ ] => rewrite H in *
         end; try rewrite wordToNat_natToW_goodSize by (eapply goodSize_weaken; eauto);
  eauto; try rewrite app_length; eauto; simpl;
    autorewrite with Server;
      try solve [ eapply goodSize_weaken; eauto | step hints ].


Theorem ok : moduleOk m.
Proof.
  vcgen; abstract (parse0; for0;
    post; evaluate hints; repeat (parse1; evaluate hints); sep hints; finish).
Qed.
