Require Import Thread StringDb.


Section strings.
  Open Scope Sep_scope.

  Fixpoint strings (n : nat) (p : W) : HProp :=
    Ex len, p =*> len
    * match n with
        | O => [| len = 0 |]
        | S n' => [| len <> 0 |] * (p ^+ $4) =?>8 wordToNat len
          * Ex len', (p ^+ $4 ^+ len) =*> len' * (p ^+ $4 ^+ len ^+ $4) =?>8 wordToNat len'
          * strings n' (p ^+ $4 ^+ len ^+ $4 ^+ len')
      end.

  Definition strings' (n : nat) (p len : W) : HProp :=
    match n with
      | O => [| len = 0 |]
      | S n' => [| len <> 0 |] * (p ^+ $4) =?>8 wordToNat len
        * Ex len', (p ^+ $4 ^+ len) =*> len' * (p ^+ $4 ^+ len ^+ $4) =?>8 wordToNat len'
        * strings n' (p ^+ $4 ^+ len ^+ $4 ^+ len')
    end.

  Theorem strings_fwd : forall n p,
    strings n p ===> Ex len, p =*> len * strings' n p len.
    destruct n; sepLemma.
  Qed.

  Theorem strings_bwd : forall n p,
    Ex len, p =*> len * strings' n p len ===> strings n p.
    destruct n; sepLemma.
  Qed.

  Theorem strings'_fwd_zero : forall n p (len : W), len = 0
    -> strings' n p len ===> Emp.
    destruct n; sepLemma.
  Qed.

  Theorem strings'_fwd_nonzero : forall n p (len : W), len <> 0
    -> strings' n p len ===> Ex n', [| n = S n' |] * [| len <> 0 |] * (p ^+ $4) =?>8 wordToNat len
    * Ex len', (p ^+ $4 ^+ len) =*> len' * (p ^+ $4 ^+ len ^+ $4) =?>8 wordToNat len'
    * strings n' (p ^+ $4 ^+ len ^+ $4 ^+ len').
    destruct n; sepLemma.
  Qed.


  Definition keyValues := starB (fun p => Ex q, Ex len, q =*> len * (q ^+ $4) =?>8 wordToNat len
    * [| p = q ^+ $4 ^+ len |] * Ex len', p =*> len' * (p ^+ $4) =?>8 wordToNat len').

  Theorem keyValues_empty_bwd : Emp ===> keyValues empty.
    apply starB_empty_bwd.
  Qed.

  Theorem keyValues_add_bwd : forall b p, keyValues b * (Ex q, Ex len, q =*> len * (q ^+ $4) =?>8 wordToNat len
    * [| p = q ^+ $4 ^+ len |] * Ex len', p =*> len' * (p ^+ $4) =?>8 wordToNat len')
    ===> keyValues (b %+ p).
    apply starB_add_bwd.
  Qed.
End strings.

Definition hints : TacPackage.
  prepare (strings_fwd, strings'_fwd_zero, strings'_fwd_nonzero)
  (strings_bwd, keyValues_empty_bwd, keyValues_add_bwd).
Defined.


Definition buildDbS := SPEC("p") reserving 23
  Al n,
  PRE[V] strings n (V "p") * mallocHeap 0
  POST[R] Ex b, Ex trailer, tree b R * keyValues b * trailer =*> 0 * mallocHeap 0.

Definition m := bimport [[ "stringdb"!"new" @ [newS], "stringdb"!"lookup" @ [lookupS],
                           "stringdb"!"insert" @ [insertS] ]]
  bmodule "web" {{
    bfunction "buildDb"("p", "len", "db", "key", "value", "vlen") [buildDbS]
      "db" <-- Call "stringdb"!"new"()
      [Al n,
        PRE[V, R] tree empty R * strings n (V "p") * mallocHeap 0
        POST[R'] Ex b, Ex trailer, tree b R' * keyValues b * trailer =*> 0 * mallocHeap 0];;

      "len" <-* "p";;
    
      [Al n, Al b,
        PRE[V] tree b (V "db") * keyValues b * V "p" =*> V "len" * strings' n (V "p") (V "len") * mallocHeap 0
        POST[R'] Ex b', Ex trailer, tree b' R' * keyValues b' * trailer =*> 0 * mallocHeap 0]
      While ("len" <> 0) {
        "key" <- "p" + 4;;
        "value" <- "key" + "len";;
        "vlen" <-* "value";;
        "p" <- "value" + 4;;
        "p" <- "p" + "vlen";;
        Call "stringdb"!"insert"("db", "key", "len", "value")
        [Al n, Al b,
          PRE[V] tree (b %+ V "value") (V "db") * keyValues (b %+ V "value") * strings n (V "p") * mallocHeap 0
          POST[R'] Ex b', Ex trailer, tree b' R' * keyValues b' * trailer =*> 0 * mallocHeap 0];;

        "len" <-* "p"
      };;

      Return "db"
    end
  }}.

Ltac t := sep hints; auto.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.
