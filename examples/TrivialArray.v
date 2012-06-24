Require Import AutoSep Allocated.

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

Lemma shift_length : forall (done pending : list W),
  ($(length done) : W) ^+ natToW 1
  = $(length (done ++ (hd $0 pending ^+ natToW 1) :: nil)).
  intros; rewrite app_length; simpl; subst.
  autorewrite with sepFormula; reflexivity.
Qed.

Lemma shift_preserve : forall (done pending : list W),
  ($(length done) : W) < $(length (done ++ pending))
  -> done ++ pending = (done ++ hd $0 pending :: nil) ++ tl pending.
  intros; subst; rewrite <- app_assoc; simpl.
  destruct pending; simpl; try reflexivity.
  rewrite app_nil_r in *; unfold natToW in *; nomega.
Qed.

Hint Resolve shift_preserve.

Lemma shift_updN : forall v pending done,
  (length pending > 0)%nat
  -> updN (done ++ pending) (length done) v = (done ++ v :: nil) ++ tl pending.
  induction done; simpl; intuition.
  destruct pending; simpl in *; auto.
  omega.
Qed.

Lemma shift_upd : forall v pending done,
  natToW (length done) < $(length (done ++ pending))
  -> (length (done ++ pending) < pow2 32)%nat
  -> upd (done ++ pending) (length done) v = (done ++ v :: nil) ++ tl pending.
  intros.
  unfold upd.
  rewrite wordToNat_natToWord_idempotent.
  apply shift_updN; auto.
  destruct pending; simpl.
  rewrite <- app_nil_end in H.
  clear H0.
  unfold natToW in *.
  nomega.
  omega.

  rewrite app_length in *.
  assert (Datatypes.length done < pow2 32)%nat by omega.
  apply Nlt_in.
  rewrite Npow2_nat.
  repeat rewrite Nat2N.id.
  assumption.
Qed.

Theorem selN_hd : forall pending done,
  selN (done ++ pending) (length done) = hd $0 pending.
  induction done; simpl; intuition.
  destruct pending; reflexivity.
Qed.

Theorem sel_hd : forall pending done,
  (length (done ++ pending) < pow2 32)%nat
  -> sel (done ++ pending) (length done) = hd $0 pending.
  unfold sel; intros; subst.
  rewrite wordToNat_natToWord_idempotent.
  apply selN_hd.
  rewrite app_length in *.
  assert (Datatypes.length done < pow2 32)%nat by omega.
  apply Nlt_in.
  rewrite Npow2_nat.
  repeat rewrite Nat2N.id.
  assumption.
Qed.

Hint Resolve sel_hd.

Lemma shift_reorg : forall done pending,
  natToW (Datatypes.length done) < $ (Datatypes.length (done ++ pending))
  -> (done ++ hd $0 pending ^+ $1 :: nil) ++ bump (tl pending)
  = done ++ bump pending.
  intros; rewrite DepList.pf_list_simpl.
  destruct pending; simpl in *.
  rewrite <- app_nil_end in *; unfold natToW in *; nomega.
  reflexivity.
Qed.

Hint Resolve shift_reorg.

Hint Extern 1 (_ = _) => apply shift_length || apply shift_upd.

Lemma unbump : forall done pending,
  ($ (length (done ++ pending)) : W) <= $ (length done)
  -> (length (done ++ pending) < pow2 32)%nat
  -> done ++ pending = done ++ bump pending.
  intros; replace pending with (@nil W).
  reflexivity.
  destruct pending; auto; simpl length in *.
  rewrite app_length in *.
  simpl length in *.
  pre_nomega.
  repeat rewrite wordToN_nat in *.
  repeat rewrite Nat2N.id in *.
  rewrite wordToNat_natToWord_idempotent in *.
  rewrite wordToNat_natToWord_idempotent in *.
  elimtype False; omega.
  apply Nlt_in.
  rewrite Npow2_nat.
  rewrite Nat2N.id.
  assumption.
  apply Nlt_in.
  rewrite Npow2_nat.
  rewrite Nat2N.id.
  omega.
Qed.

Hint Resolve unbump.

Theorem arraysOk : moduleOk arrays.
(*TIME  Clear Timing Profile. *)
  vcgen; abstract (sep_auto; (subst; try rewrite sel_hd by eauto; eauto 7); sep_auto).
(*TIME  Print Timing Profile. *)
Qed.
