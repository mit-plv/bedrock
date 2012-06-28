Require Import AutoSep.

(** * A trivial example to make sure the array proof automation isn't completely borked *)

Definition readS : assert := st ~> ExX, Ex ls, [| $3 < natToW (length ls) |]%word
  /\ ![ ^[array ls st#Rv] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = selN ls 3 |] /\ ![ ^[array ls st#Rv] * #1 ] st').

Definition writeS : assert := st ~> ExX, Ex ls, [| $3 < natToW (length ls) |]%word
  /\ ![ ^[array ls st#Rv] * #0 ] st
  /\ st#Rp @@ (st' ~> ![ ^[array (updN ls 3 11) st#Rv] * #1 ] st').

Definition bump := map (fun w : W => w ^+ $1).

Definition bumpS : assert := st ~> ExX, Ex ls, Ex arr, Ex junk,
  ![ (st#Sp ==*> arr, $(length ls), junk) * ^[array ls arr] * #0 ] st
  /\ st#Rp @@ (st' ~> ![ ^[st#Sp =?> 3] * ^[array (bump ls) arr] * #1 ] st').

Open Scope list_scope.

Definition arrays := bmodule "read" {{
  bfunction "read" [readS] {
    Rv <- $[Rv + 12];;
    Goto Rp
  } with bfunction "write" [writeS] {
    $[Rv + 12] <- 11;;
    Goto Rp
  } with bfunction "bump" [bumpS] {
    $[Sp+8] <- 0;;
    [st ~> ExX, Ex ls, Ex done, Ex pending, Ex arr, Ex len, Ex i,
      [| len = $(length ls) /\ i = $(length done) /\ ls = done ++ pending |]
      /\ ![ (st#Sp ==*> arr, len, i) * ^[array ls arr] * #0 ] st
      /\ st#Rp @@ (st' ~> Ex ls', [| ls' = done ++ bump pending |]
        /\ ![ ^[st#Sp =?> 3] * ^[array ls' arr] * #1 ] st')]
    While ($[Sp+8] < $[Sp+4]) {
      Rv <- 4 * $[Sp+8];;
      Rv <- $[Sp] + Rv;;
      $[Rv] <- $[Rv] + 1;;
      $[Sp+8] <- $[Sp+8] + 1
    };;
    Goto Rp
  }
}}.

Lemma length_nil : forall A, natToW 0 = $(length (@nil A)).
  reflexivity.
Qed.

Lemma app_nil : forall A (ls : list A), ls = nil ++ ls.
  reflexivity.
Qed.

Hint Immediate length_nil app_nil.

Hint Rewrite app_length : sepFormula.

Ltac pure := intros; subst; autorewrite with sepFormula in *; simpl length;
  autorewrite with sepFormula; eauto 6.

Lemma shift_length : forall (done pending : list W),
  ($(length done + 1) : W)
  = $(length (done ++ (hd $0 pending ^+ natToW 1) :: nil)).
  pure.
Qed.

Hint Extern 1 (_ = _) => apply shift_length.

Hint Rewrite DepList.pf_list_simpl : sepFormula.

Lemma decomp : forall A (v : A) ls,
  (length ls > 0)%nat
  -> hd v ls :: tl ls = ls.
  destruct ls; simpl; intuition.
Qed.

Hint Rewrite decomp using solve [ eauto ] : sepFormula.

Lemma not_done_yet : forall A (done pending : list A),
  natToW (length done) < $ (length done + length pending)
  -> (length pending > 0)%nat.
  destruct pending; simpl; intuition;
    rewrite <- plus_n_O in *; unfold natToW in *; nomega.
Qed.

Hint Immediate not_done_yet.

Lemma shift_updN : forall v pending done,
  (length pending > 0)%nat
  -> updN (done ++ pending) (length done) v = done ++ v :: tl pending.
  induction done; simpl; intuition;
    destruct pending; simpl in *; auto; omega.
Qed.

Hint Resolve shift_updN.

Hint Extern 1 (_ = _) => apply shift_updN.

Theorem selN_hd : forall pending done,
  selN (done ++ pending) (length done) = hd $0 pending.
  induction done; simpl; intuition;
    destruct pending; reflexivity.
Qed.

Hint Rewrite selN_hd : sepFormula.

Lemma shift_reorg : forall pending,
  (length pending > 0)%nat
  -> hd $0 pending ^+ $1 :: bump (tl pending)
  = bump pending.
  pure; destruct pending; simpl in *; auto; omega.
Qed.

Hint Rewrite shift_reorg using solve [ eauto ] : sepFormula.

Hint Rewrite Npow2_nat wordToN_nat wordToNat_natToWord_idempotent
  using nomega : N.

Lemma now_done : forall A (done pending : list A) sz,
  natToWord sz (length done + length pending) <= $ (length done)
  -> (length done + length pending < pow2 sz)%nat
  -> pending = nil.
  destruct pending; pure; nomega.
Qed.

Hint Resolve now_done.

Lemma unbump : forall done pending,
  pending = nil
  -> done ++ pending = done ++ bump pending.
  pure.
Qed.

Hint Resolve unbump.

Ltac done_bound := intros done pending; intros;
  assert (length (done ++ pending) < pow2 32)%nat by eauto;
    rewrite app_length in *; omega.

Lemma done_bound : forall done pending P stn m specs,
  interp specs (![ P ] (stn, m))
  -> containsArray P (done ++ pending)
  -> (length done < pow2 32)%nat.
  done_bound.
Qed.

Lemma done_bound2 : forall done pending P stn m specs,
  interp specs (![ P ] (stn, m))
  -> containsArray P (done ++ pending)
  -> (length done + length pending < pow2 32)%nat.
  done_bound.
Qed.

Hint Resolve done_bound done_bound2.

Hint Extern 1 (himp _ _ _) => reflexivity.

Theorem arraysOk : moduleOk arrays.
(*TIME  Clear Timing Profile. *)
  vcgen; abstract (sep_auto; pure).
(*TIME  Print Timing Profile. *)
Qed.
