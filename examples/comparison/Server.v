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
  if wlt_dec w' w then w else w'.

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
      collectBelow upper (skipn (wordToNat lower) data) acc
  end.

Definition responseAll (data : list W) (rs : list req) (acc : list W) :=
  fold_left (response data) rs acc.

Definition mainS := SPEC("cmd", "cmdLen", "data", "dataLen") reserving 15
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
                     "index", "value", "res", "node") [mainS]
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
            Diverge(*
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
              "res" <- 1
            };;

            "node" <-- Call "malloc"!"malloc"(0)
            [Al rdone, Al r, Al d, Al out,
              PRE[V, MR] array (rdone ++ encodeAll r) (V "cmd") * array d (V "data") * mallocHeap
                * sll out (V "output") * [| V "position" = length rdone |]
                * [| V "cmdLen" = (length rdone + length (encodeAll r))%nat |] * [| V "dataLen" = length d |]
                * [| goodSize (length rdone + length (encodeAll r) + 3) |]
                * MR =?> 2 * [| MR <> 0 |]
              POST[R] array (rdone ++ encodeAll r) (V "cmd") * array d (V "data") * mallocHeap
                * sll (responseAll d r (V "res" :: out)) R];;

            "node" *<- "res";;
            "node" + 4 *<- "output";;
            "output" <- "node"*)
          end;;

          (* MaxInRange *)
          Case (1 ++ "lower" ++ "upper")
            Diverge(*
            "res" <- 0;;

            [Al rdone, Al r, Al out,
              After prefix Approaching all
                PRE[V] array (rdone ++ encodeAll (MaxInRange (V "lower") (V "upper") :: r)) (V "cmd")
                  * mallocHeap * sll out (V "output") * [| V "position" = natToW (length rdone + 3) |]
                  * [| V "cmdLen" = (length rdone + 3 + length (encodeAll r))%nat |]
                  * [| V "dataLen" = length all |]
                  * [| V "res" = maxInRange (V "lower") (V "upper") prefix |]
                  * [| goodSize (length rdone + 3 + length (encodeAll r) + 3) |]
                POST[R] array (rdone ++ encodeAll (MaxInRange (V "lower") (V "upper") :: r)) (V "cmd")
                  * mallocHeap * sll (responseAll all (MaxInRange (V "lower") (V "upper") :: r) out) R ]
            For "index" Holding "value" in "data" Size "dataLen"
              Where (("lower" <= Value) && (Value <= "upper") && (Value >= "res")) {
              "res" <- "value"
            };;

            "node" <-- Call "malloc"!"malloc"(0)
            [Al rdone, Al r, Al d, Al out,
              PRE[V, MR] array (rdone ++ encodeAll r) (V "cmd") * array d (V "data") * mallocHeap
                * sll out (V "output") * [| V "position" = length rdone |]
                * [| V "cmdLen" = (length rdone + length (encodeAll r))%nat |] * [| V "dataLen" = length d |]
                * [| goodSize (length rdone + length (encodeAll r) + 3) |]
                * MR =?> 2 * [| MR <> 0 |]
              POST[R] array (rdone ++ encodeAll r) (V "cmd") * array d (V "data") * mallocHeap
                * sll (responseAll d r (V "res" :: out)) R];;

            "node" *<- "res";;
            "node" + 4 *<- "output";;
            "output" <- "node"*)
          end;;

          (* CollectBelow *)
          Case (2 ++ "lower" ++ "upper")
            [Al rdone, Al r, Al out,
              After prefix Approaching all
                PRE[V] array (rdone ++ encodeAll (CollectBelow (V "lower") (V "upper") :: r)) (V "cmd")
                  * mallocHeap
                  * sll (collectBelow (V "upper") (skipn (wordToNat (V "lower")) prefix) out) (V "output")
                  * [| V "position" = natToW (length rdone + 3) |]
                  * [| V "cmdLen" = (length rdone + 3 + length (encodeAll r))%nat |]
                  * [| V "dataLen" = length all |]
                  * [| goodSize (length rdone + 3 + length (encodeAll r) + 3) |]
                POST[R] array (rdone ++ encodeAll (CollectBelow (V "lower") (V "upper") :: r)) (V "cmd")
                  * mallocHeap * sll (responseAll all r
                    (collectBelow (V "upper")
                      (skipn (wordToNat (V "lower")) all) out)) R ]
            For "index" Holding "value" in "data" Size "dataLen"
              Where ((Index >= "lower") && (Value <= "upper")) {
              "node" <-- Call "malloc"!"malloc"(0)
              [Al rdone, Al r, Al d, Al out,
                PRE[V, MR] array (rdone ++ encodeAll (CollectBelow (V "lower") (V "upper") :: r)) (V "cmd")
                  * array d (V "data") * mallocHeap * sll out (V "output")
                  * [| V "position" = natToW (length rdone + 3) |]
                  * [| V "cmdLen" = (length rdone + 3 + length (encodeAll r))%nat |]
                  * [| V "dataLen" = length d |]
                  * [| goodSize (length rdone + 3 + length (encodeAll r) + 3) |]
                  * MR =?> 2 * [| MR <> 0 |]
                POST[R] array (rdone ++ encodeAll (CollectBelow (V "lower") (V "upper") :: r)) (V "cmd")
                  * mallocHeap * sll (responseAll d r
                    (collectBelow (V "upper") (skipn (wordToNat (V "index")) d) out)) R ];;

              "node" *<- "value";;
              "node" + 4 *<- "output";;
              "output" <- "node"
            }
          end
        } Default {
          Diverge(*Fail*) (* Impossible: the match was exhaustive w.r.t. the spec. *)
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

Lemma valueIsGe_set : forall ls posn V lower,
  sel V "index" = length ls
  -> weqb (sel V "index") posn = true
  -> wleb lower (sel V "value") = true
  -> goodSize (length ls)
  -> $1 = valueIsGe (ls ++ sel V "value" :: nil) posn lower.
  intros; subst;
    match goal with
      | [ H : _ |- _ ] => apply wleb_true_fwd in H
    end;
    match goal with
      | [ H : _ |- _ ] => apply weqb_true_iff in H
    end;
    match goal with
      | [ H : _ = _ |- _ ] => rewrite H in *
    end; replace posn with (natToW (length ls)) by auto; unfold valueIsGe;
    autorewrite with Server; simpl; rewrite wordToNat_natToW_goodSize by auto;
      destruct (le_lt_dec (Datatypes.length ls + 1) (Datatypes.length ls)); try omega;
        rewrite sel_middle by auto; destruct (wlt_dec (sel V "value") lower); auto; nomega.
Qed.

Lemma not_done_yet : forall (pos len : W) (ws : list W) r,
  pos < len
  -> pos = natToW (length ws)
  -> len = length ws + length (encodeAll r)
  -> r <> nil.
  destruct r; intuition (try discriminate); subst; simpl in *;
    rewrite plus_0_r in *; nomega.
Qed.

Ltac finish := fold (@skipn W); subst; eauto;
  try match goal with
        | [ _ : context[?a ++ ?b :: ?c :: ?d :: _] |- sel _ "position" = natToW (length _) ] =>
          instantiate (1 := a ++ b :: c :: d :: nil)
      end;
  repeat match goal with
           | [ H : sel _ _ = _ |- _ ] => rewrite H in *
           | [ H : Regs _ _ = sel _ _ |- _ ] => rewrite H in *
         end; try rewrite wordToNat_natToW_goodSize by (eapply goodSize_weaken; eauto);
  eauto; autorewrite with StreamParse Server; simpl; autorewrite with StreamParse Server; eauto; simpl;
    try solve [ auto
      | eapply goodSize_weaken; eauto
      | step hints
      | match goal with
          | [ _ : ~match encodeAll ?r with nil => _ | _ => _ end |- _ ] =>
            match goal with
              | [ _ : match encodeAll _ with nil => False | _ => _ end |- _ ] => fail 1
              | _ => assert (r <> nil) by (eapply not_done_yet; eauto);
                destruct r as [ | [ ] ]; simpl in *; tauto
            end
        end ].

Hint Extern 1 (natToW 1 = valueIsGe _ _ _) =>
  eapply valueIsGe_set; [ eassumption | eassumption | eassumption
    | match goal with
        | [ _ : context[?a ++ sel ?V "value" :: ?b] |- _ ] =>
          apply goodSize_weaken with (length (a ++ sel V "value" :: b)); [
            eapply containsArray_goodSize; eauto 10
            | finish ]
      end ].

Lemma join3 : forall A x y z ls' (ls : list A),
  ((ls ++ x :: y :: z :: nil) ++ ls') = ls ++ x :: y :: z :: ls'.
  induction ls; simpl; intuition.
Qed.

Hint Rewrite join3 : Server.

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

Hint Extern 1 (@eq W _ _) =>
  match goal with
    | [ |- ?G ] => has_evar G; fail 1
    | _ => words
  end.

Fixpoint maxInRange' (lower upper : W) (data : list W) (acc : W) : W :=
  match data with
    | nil => acc
    | w :: ws =>
      maxInRange' lower upper ws (if wlt_dec w lower
        then acc
        else if wlt_dec upper w
          then acc
          else wmax w acc)
  end.

Ltac ifs := repeat match goal with
                     | [ |- context[if ?E then _ else _] ] => destruct E; auto
                     | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; auto
                   end.

Hint Rewrite roundTrip_0 : N.

Lemma wordToNat_inj : forall sz (w w' : word sz),
  wordToNat w = wordToNat w'
  -> w = w'.
  intros ? ? ? H; apply (f_equal (natToWord sz)) in H;
    repeat rewrite natToWord_wordToNat in *; auto.
Qed.

Lemma maxInRange'_alt : forall lower upper data acc,
  maxInRange' lower upper data acc
  = wmax (maxInRange lower upper data) acc.
  induction data; simpl; unfold wmax in *; intuition; [
    ifs; nomega
    | rewrite IHdata; clear IHdata; ifs; (try nomega; apply wordToNat_inj; nomega) ].
Qed.

Lemma maxInRange_alt : forall lower upper data,
  maxInRange lower upper data = maxInRange' lower upper data 0.
  intros; rewrite maxInRange'_alt; unfold wmax; ifs; apply wordToNat_inj; nomega.
Qed.

Lemma wle_lt : forall u v : W,
  u < v
  -> u <= v.
  intros; nomega.
Qed.

Hint Immediate wle_lt.

Lemma maxInRange'_skip : forall lower upper w ws acc,
  (wleb lower w = true
    -> wleb w upper = true
    -> wleb (maxInRange' lower upper ws acc) w = true
    -> False)
  -> maxInRange' lower upper ws acc = maxInRange' lower upper (ws ++ w :: nil) acc.
  induction ws; simpl; unfold wmax; intros; ifs; elimtype False; eauto.
Qed.

Lemma maxInRange_skip : forall lower upper w ws,
  (wleb lower w = true
    -> wleb w upper = true
    -> wleb (maxInRange lower upper ws) w = true
    -> False)
  -> maxInRange lower upper ws = maxInRange lower upper (ws ++ w :: nil).
  intros; repeat rewrite maxInRange_alt in *; apply maxInRange'_skip; auto.
Qed.

Hint Immediate maxInRange_skip.

Lemma maxInRange'_set : forall lower upper w ws acc,
  wleb lower w = true
  -> wleb w upper = true
  -> wleb (maxInRange' lower upper ws acc) w = true
  -> w = maxInRange' lower upper (ws ++ w :: nil) acc.
  induction ws; simpl; unfold wmax; intuition;
    ifs; repeat match goal with
                  | [ H : wleb _ _ = true |- _ ] => apply wleb_true_fwd in H
                end; try nomega; apply wordToNat_inj; nomega.
Qed.

Lemma maxInRange_set : forall lower upper w ws,
  wleb lower w = true
  -> wleb w upper = true
  -> wleb (maxInRange lower upper ws) w = true
  -> w = maxInRange lower upper (ws ++ w :: nil).
  intros; repeat rewrite maxInRange_alt in *; apply maxInRange'_set; auto.
Qed.

Hint Immediate maxInRange_set.


Theorem ok : moduleOk m.
Proof.
  vcgen; parse0; for0.

  Ltac t := post; evaluate hints; repeat (parse1 finish; use_match); multi_ex; sep hints; finish.

  admit.
  admit.
  admit.
  admit.
  admit.
  admit.

  t.
  t.
  t.
  t.


  Lemma skipn_nil : forall A n,
    skipn n (@nil A) = nil.
    destruct n; reflexivity.
  Qed.

  Hint Rewrite skipn_nil : Server.

  t.


  post.
  evaluate hints.
  multi_ex.
  descend.
  step hints.
  fold (@skipn W).

  Lemma eq0_le : forall w : W,
    wordToNat w = 0
    -> w <= natToW 0.
    intros ? H; apply (f_equal natToW) in H;
      unfold natToW in H; rewrite natToWord_wordToNat in H; subst; nomega.
  Qed.

  Hint Immediate eq0_le.

  (*Lemma le0' : forall w,
    w <= natToW 0
    -> w = natToW 0.
    intros; apply wordToNat_inj; nomega.
  Qed.

  Lemma le0 : forall w b,
    w <= natToW 0
    -> w <= b.
    intros; rewrite (le0' w); nomega.
  Qed.

  Hint Immediate le0.*)

  Lemma le_any : forall (w : W) b,
    wordToNat w = 0
    -> w <= b.
    intros; pre_nomega; rewrite H; omega.
  Qed.

  Hint Immediate le_any.

  Lemma wleb_false_fwd : forall u v,
    wleb u v = false
    -> v < u.
    unfold wleb; intros; ifs; try discriminate;
      assert (wordToNat u <> wordToNat v) by (intro; apply wordToNat_inj in H0; tauto); nomega.
  Qed.

  Hint Immediate wleb_false_fwd.

  Lemma collectBelow_skip1 : forall upper this ws lower base,
    wleb this upper = false
    -> collectBelow upper (skipn lower (ws ++ this :: nil)) base
    = collectBelow upper (skipn lower ws) base.
    induction ws; destruct lower; simpl; intuition idtac; autorewrite with Server; auto;
      solve [ ifs; elimtype False; eauto
        | specialize (IHws 0); simpl in *; ifs ].
  Qed.

  Lemma skipn_app1 : forall A (ls2 : list A) n ls1,
    (length ls1 < n)%nat
    -> skipn n (ls1 ++ ls2) = skipn (n - length ls1) ls2.
    induction n; destruct ls1; simpl; intuition.
  Qed.

  Lemma skipn_all : forall A n (ls1 : list A),
    (length ls1 <= n)%nat
    -> skipn n ls1 = nil.
    induction n; destruct ls1; simpl; intuition.
  Qed.

  Lemma collectBelow_skip2 : forall upper this ws (lower : W) base,
    wleb (wordToNat lower) (length ws) = false
    -> goodSize (S (length ws))
    -> collectBelow upper (skipn (wordToNat lower) (ws ++ this :: nil)) base
    = collectBelow upper (skipn (wordToNat lower) ws) base.
    intros; repeat (rewrite skipn_all; simpl; auto);
      match goal with
        | [ H : _ |- _ ] => apply wleb_false_fwd in H
      end;
      match goal with
        | [ H : _ |- _ ] => apply lt_goodSize' in H; autorewrite with Server; simpl; auto
      end.
  Qed.

  Lemma collectBelow_skip : forall upper (lower : W) this base ws,
    (wleb lower (length ws) = true
      -> wleb this upper = true
      -> False)
    -> goodSize (S (length ws))
    -> collectBelow upper (skipn (wordToNat lower) (ws ++ this :: nil)) base
    = collectBelow upper (skipn (wordToNat lower) ws) base.
    intros; case_eq (wleb this upper); intros; try solve [ apply collectBelow_skip1; auto ];
      intros; case_eq (wleb lower (length ws)); intros; [
        elimtype False; eauto
        | apply collectBelow_skip2; auto; unfold natToW; rewrite natToWord_wordToNat; auto ].
  Qed.

  rewrite collectBelow_skip.
  finish.
  auto.
  auto.
  



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
