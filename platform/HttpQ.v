Require Import AutoSep Scheduler Arrays8 MoreArrays Buffers StringOps Ascii Io.
Require Import Http SinglyLinkedList Bags ArrayOps.


Module Type S.
  Parameter buf_size : N.
  Parameters sched globalInv : bag -> HProp.

  Axiom buf_size_lower : (nat_of_N buf_size >= 2)%nat.
  Axiom buf_size_upper : goodSize (4 * nat_of_N buf_size).
End S.

Module Make(Import M : S).

Definition bsize := nat_of_N (buf_size * 4)%N.

Definition onebuf (p : W) := (p =?>8 bsize * [| p <> 0 |] * [| freeable p (nat_of_N buf_size) |])%Sep.
Definition bufs := starL onebuf.

Theorem onebuf_fwd : forall p,
  onebuf p ===> p =?>8 bsize * [| p <> 0 |] * [| freeable p (nat_of_N buf_size) |].
  unfold onebuf; sepLemma.
Qed.

Theorem onebuf_bwd : forall p,
  p =?>8 bsize * [| p <> 0 |] * [| freeable p (nat_of_N buf_size) |] ===> onebuf p.
  unfold onebuf; sepLemma.
Qed.

Module Type HTTPQ.
  Parameter httpq : W -> HProp.

  Axiom httpq_fwd : forall p, httpq p ===> Ex ls, sll ls p * bufs ls.
  Axiom httpq_bwd : forall p, Ex ls, sll ls p * bufs ls ===> httpq p.

  Definition httpqSplitMe := httpq.

  Axiom httpq_split : forall p, (Ex x, Ex ls, sll (x :: ls) p * bufs (x :: ls)) ===> httpqSplitMe p.
End HTTPQ.

Module Httpq : HTTPQ.
  Open Scope Sep_scope.

  Definition httpq (p : W) :=
    Ex ls, sll ls p * bufs ls.
  
  Theorem httpq_fwd : forall p, httpq p ===> Ex ls, sll ls p * bufs ls.
    unfold httpq; sepLemma.
  Qed.

  Theorem httpq_bwd : forall p, Ex ls, sll ls p * bufs ls ===> httpq p.
    unfold httpq; sepLemma.
  Qed.

  Definition httpqSplitMe := httpq.

  Theorem httpq_split : forall p, (Ex x, Ex ls, sll (x :: ls) p * bufs (x :: ls)) ===> httpqSplitMe p.
    sepLemma.
    etransitivity; [ | apply httpq_bwd ].
    apply himp_ex_c; exists (x0 :: x).
    sepLemma.
  Qed.
End Httpq.

Import Httpq.
Export Httpq.

Definition saveS := SPEC("q", "buf", "len") reserving 12
  Al len : W,
  PRE[V] httpq (V "q") * V "buf" =?>8 wordToNat len * [| V "len" <= len |] * mallocHeap 0
  POST[R] httpq R * V "buf" =?>8 wordToNat len * mallocHeap 0.

Definition sendGS := SPEC("q") reserving 0
  Al fs,
  PRE[V] [| V "fr" %in fs |] * httpq (V "q")
    * sched fs * globalInv fs * mallocHeap 0
  POST[_] Ex fs', [| fs %<= fs' |] * sched fs' * globalInv fs' * mallocHeap 0.

Coercion ascii_of_nat : nat >-> ascii.

Module H := Http.Make(M).
Import H.

Definition preRequest := ("POST / HTTP/1.0 HTTP/1.1 200 OK" ++ nl
  ++ "Content-Type: text/xml" ++ nl
  ++ "User-Agent: Bedrock" ++ nl
  ++ "Content-Length: ")%string.

Definition hints : TacPackage.
  prepare (httpq_fwd, onebuf_fwd, SinglyLinkedList.nil_fwd, SinglyLinkedList.cons_fwd)
  (httpq_bwd, httpq_split, onebuf_bwd, SinglyLinkedList.nil_bwd, SinglyLinkedList.cons_bwd).
Defined.

Definition m := bimport [[ "io"!"writeAll" @ [writeAllGS sched globalInv],
                           "array8"!"copy" @ [ArrayOps.copyS],
                           "http"!"itoa" @ [itoaS], "sys"!"abort" @ [abortS],
                           "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "buffers"!"bmalloc" @ [bmallocS], "buffers"!"bfree" @ [bfreeS] ]]
  bmodule "httpq" {{
    bfunction "save"("q", "buf", "len", "newbuf", "node") [saveS]
      If ("len" >= bsize) {
        (* Well, shucks.  It doesn't fit. *)
        Call "sys"!"abort"()
        [PREonly[_] [| False |] ];;
        Fail
      } else {
        "newbuf" <-- Call "buffers"!"bmalloc"(buf_size)
        [Al len : W,
          PRE[V, R] R =?>8 bsize * [| R <> 0 |] * [| freeable R (nat_of_N buf_size) |]
            * [| V "len" < natToW bsize |]%word
            * httpq (V "q") * V "buf" =?>8 wordToNat len * [| V "len" <= len |]%word * mallocHeap 0
          POST[R'] httpq R' * V "buf" =?>8 wordToNat len * mallocHeap 0];;

        Note [reveal_buffers];;
        (* Copy the input buffer into our new buffer. *)
        Call "array8"!"copy"("newbuf", 0, "buf", 0, "len")
        [Al len : W, Al ls,
          PRE[V] array8 ls (V "newbuf") * [| length ls = bsize |]
            * [| V "newbuf" <> 0 |] * [| freeable (V "newbuf") (nat_of_N buf_size) |]
            * [| V "len" < natToW (length ls) |]%word
            * httpq (V "q") * V "buf" =?>8 wordToNat len * [| V "len" <= len |]%word * mallocHeap 0
          POST[R'] httpq R' * V "buf" =?>8 wordToNat len * mallocHeap 0];;

        (* Write a terminating 0 character. *)
        "newbuf" + "len" *<-8 0;;

        Note [reveal_buffers];;
        "node" <-- Call "malloc"!"malloc"(0, 2)
        [Al len : W,
          PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |]
            * V "newbuf" =?>8 bsize * [| V "newbuf" <> 0 |] * [| freeable (V "newbuf") (nat_of_N buf_size) |]
            * httpq (V "q") * V "buf" =?>8 wordToNat len * [| V "len" <= len |]%word * mallocHeap 0
          POST[R'] httpqSplitMe R' * V "buf" =?>8 wordToNat len * mallocHeap 0];;

        "node" *<- "newbuf";;
        "node"+4 *<- "q";;

        Return "node"
      }
    end
  }}.

Hint Extern 1 (@eq W _ _) => words.

Print Ltac match_locals.

Ltac match_locals :=
  match goal with
    | [ |- interp _ (?P ---> ?Q)%PropX ] =>
      match Q with
        | context[locals ?ns ?vs _ _] =>
          match P with
            | context[locals ns ?vs' _ _] => equate vs' vs; descend
            end
      end;
      try match goal with
            | [ H : sel ?V "len" <= ?X |- context[?Y < sel ?V "len" -> False] ] =>
              equate X Y
          end
    | _ => MoreArrays.match_locals
  end.

Ltac t' :=
  try match goal with
        | [ |- context[reveal_buffers] ] => post; unfold buffer, httpqSplitMe in *
      end;
  try match goal with
        | [ _ : context[match ?st with pair _ _ => _ end] |- _ ] => destruct st; simpl in *
      end; try solve [ sep_auto; eauto ];
  post; evaluate hints; descend;
  repeat (try match_locals; step hints; descend); eauto.

Ltac t := easy || prove_irrel || t'.

Lemma buf_size_simp : wordToNat (NToW buf_size) = N.to_nat buf_size.
  unfold NToW; rewrite NToWord_nat.
  apply wordToNat_natToWord_idempotent.
  change (goodSize (N.to_nat buf_size)).
  eapply goodSize_weaken.
  apply buf_size_upper.
  auto.
Qed.

Lemma buf_size_lower' : natToW 2 <= NToW buf_size.
  pre_nomega.
  rewrite buf_size_simp.
  apply buf_size_lower.
Qed.

Local Hint Immediate buf_size_lower'.

Lemma freeable_coerce : forall p,
  freeable p (wordToNat (NToW buf_size))
  -> freeable p (N.to_nat buf_size).
  intros.
  rewrite buf_size_simp in *; auto.
Qed.

Local Hint Immediate freeable_coerce.

Lemma make_bsize : wordToNat (NToW buf_size) * 4 = bsize.
  rewrite buf_size_simp.
  unfold bsize.
  rewrite N2Nat.inj_mul.
  change (N.to_nat 4) with 4.
  omega.
Qed.

Hint Rewrite make_bsize : sepFormula.

Lemma bsize_simp : wordToNat (natToW bsize) = bsize.
  intros; apply wordToNat_natToWord_idempotent.
  change (goodSize bsize).
  eapply goodSize_weaken.
  apply buf_size_upper.
  unfold bsize.
  rewrite N2Nat.inj_mul.
  change (N.to_nat 4) with 4.
  omega.
Qed.

Lemma lt_le : forall w n,
  w < natToW bsize
  -> n = bsize
  -> (wordToNat w <= n)%nat.
  intros; subst; pre_nomega; rewrite bsize_simp in *.
  auto.
Qed.

Lemma le_le : forall n (w u : W),
  u <= w
  -> n = wordToNat w
  -> (wordToNat u <= n)%nat.
  intros; subst; nomega.
Qed.

Lemma bsize_wordToNat : forall n,
  n = bsize
  -> n = wordToNat (natToW bsize).
  intros; rewrite bsize_simp; auto.
Qed.

Local Hint Immediate lt_le le_le bsize_wordToNat.

Theorem ok : moduleOk m.
  vcgen.

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
  t.
  t.
  t.
  t.
  t.
  t.
Qed.

End Make.
