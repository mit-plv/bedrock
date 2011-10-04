(* Structured programming *)

Require Import NArith String List.

Require Import Nomega PropX PropXTac Word LabelMap IL XCAP.

Set Implicit Arguments.

Local Open Scope N_scope.


Section imports.
  (* Which external code labels must be available? *)
  Variable imports : LabelMap.t assert.

  Hypothesis imports_global : forall k v, LabelMap.MapsTo k v imports
    -> exists s, snd k = Global s.

  (* Which code module are we defining here? *)
  Variable modName : string.

  (* Full set of code labels that may be mentioned in generated code *)
  Fixpoint imps (bls : list (assert * block)) (base exit : N) (post : assert) : LabelMap.t assert :=
    match bls with
      | nil => LabelMap.add (modName, Local exit) post imports
      | (pre, _) :: bls' => LabelMap.add (modName, Local base) pre (imps bls' (Nsucc base) exit post)
    end.

  (** The data type of structured program pieces *)

  Record codeGen (Precondition : assert) (Base Exit : N) (Postcondition : assert) (VerifCond : Prop) := {
    Entry : N;                      (* Jump here to start *)
    Blocks : list (assert * block); (* Code blocks *)

    EntryOk : Entry < N_of_nat (length Blocks);

    PreconditionOk : exists bl, nth_error Blocks (nat_of_N Entry) = Some (Precondition, bl);
    
    BlocksOk : VerifCond
      -> Exit < Base
      -> List.Forall (fun p => blockOk (imps Blocks Base Exit Postcondition) (fst p) (snd p)) Blocks
  }.

  Record codeOut (Precondition : assert) := {
    Postcondition : assert;     (* Guarantee this on exit. *)
    VerifCond : Prop;           (* User must prove this *)
    Generate : forall Base Exit : N, (* Start generating code labels at this address *)
      codeGen Precondition Base Exit Postcondition VerifCond
  }.

  Definition cmd := forall cin, codeOut cin.


  (** Sequencing *)

  Definition notStuck (pre : assert) (is : list instr) :=
    forall stn st specs, interp specs (pre stn st)
      -> evalInstrs stn st is <> None.

  Ltac lomega := (let H := fresh in intro H; injection H; clear H; intro; try subst; simpl in *; congruence || nomega)
    || (repeat match goal with
                 | [ |- eq (A := ?A) _ _ ] =>
                   match A with
                     | N => fail 1
                     | _ => f_equal
                   end
               end; nomega).

  Hint Extern 1 (_ < _) => nomega.

  Lemma ge_refl : forall n, n >= n.
    intros; nomega.
  Qed.

  Hint Resolve ge_refl.

  Hint Extern 1 (eq (A := label) _ _) => lomega.
  Hint Extern 1 (~(eq (A := label) _ _)) => lomega.
  Hint Extern 1 (eq (A := LabelKey.t) _ _) => lomega.
  Hint Extern 1 (~(eq (A := LabelKey.t) _ _)) => lomega.

  Hint Resolve LabelMap.add_1 LabelMap.add_2.

  Lemma lookup_imps : forall p bl exit post bls n base,
    nth_error bls (nat_of_N n) = Some (p, bl)
    -> LabelMap.MapsTo (modName, Local (base + n)) p
    (imps bls base exit post).
    induction bls; simpl in *; intuition.

    destruct (nat_of_N n); discriminate.

    induction n using Nind; simpl in *.

    injection H; clear H; intros; subst.
    autorewrite with N.
    auto.

    autorewrite with N in *; simpl in *.
    replace (base + Nsucc n) with (Nsucc base + n) by nomega.
    auto.
  Qed.

  Hint Resolve lookup_imps.

  Hint Immediate simplify_fwd.

  Lemma blockOk_impl : forall imps imps' p bl,
    (forall k v, LabelMap.MapsTo k v imps
      -> LabelMap.MapsTo k v imps')
    -> blockOk imps p bl
    -> blockOk imps' p bl.
    unfold blockOk; intuition.
    specialize (H0 stn specs).
    match type of H0 with
      | ?P -> _ => assert P by auto; intuition
    end.
    specialize (H4 _ H2); destruct H4; intuition.
    destruct H5; intuition.
    destruct H6; intuition.
    eauto 8.
  Qed.

  Hint Resolve blockOk_impl.

  Lemma imps_preserve : forall k v exit post n pre bls base,
    LabelMap.MapsTo k v (imps bls base exit post)
    -> n < base
    -> exit < n
    -> LabelMap.MapsTo k v (LabelMap.add (modName, Local n) pre
        (imps bls base exit post)).
    induction bls; simpl; intuition.

    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    auto.

    destruct (imports_global H3).
    auto.

    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    auto.

    specialize (IHbls _ H3).
    assert (n < Nsucc base) by nomega; intuition.
    apply LabelFacts.add_mapsto_iff in H5; intuition; subst.
    auto.
  Qed.

  Hint Resolve imps_preserve.

  Lemma imps_exit : forall exit post bls base,
    exit < base
    -> LabelMap.MapsTo (modName, Local exit) post (imps bls base exit post).
    induction bls; simpl; intuition.
  Qed.

  Hint Resolve imps_exit.

  Lemma specialize_imps : forall {exit post} {P : _ -> _ -> Prop} {bls base},
    (forall k v, LabelMap.MapsTo k v (imps bls base exit post) -> P k v)
    -> (exit < base -> P (modName, Local exit) post)
    /\ (forall base', base = Nsucc base'
      -> forall n p bl, nth_error bls (nat_of_N n) = Some (p, bl)
        -> P (modName, Local (base + n)) p).
    intuition.

    apply H.
    rewrite H0.
    eapply lookup_imps; eauto.
  Qed.

  Lemma lt_succ : forall n, n < Nsucc n.
    intros; nomega.
  Qed.

  Lemma lt_succ' : forall n m, n < m -> n < Nsucc m.
    intros; nomega.
  Qed.

  Hint Immediate lt_succ lt_succ'.

  Hint Extern 1 (List.Forall _ _) => eapply Forall_impl; [ | eassumption ].

  Theorem split_add : forall A k (v : A) m {P : _ -> _ -> Prop},
    (forall k' v', LabelMap.MapsTo k' v' (LabelMap.add k v m) -> P k' v')
    -> P k v
    /\ (forall k' v', LabelMap.MapsTo k' v' m -> k' <> k -> P k' v').
    intuition.
  Qed.

  Hint Extern 1 (interp _ _) => apply simplify_bwd; simpl.

  Hint Rewrite nat_of_N_of_nat : N.

  Lemma nth_error_app2 : forall n A (ls2 ls1 : list A),
    nth_error (ls1 ++ ls2) (length ls1 + n) = nth_error ls2 n.
    induction ls1; simpl; intuition.
  Qed.

  Hint Rewrite nth_error_app2 : N.

  Lemma Forall_app : forall A (P : A -> Prop) ls1 ls2,
    List.Forall P ls1
    -> List.Forall P ls2
    -> List.Forall P (ls1 ++ ls2).
    induction 1; simpl; intuition.
  Qed.

  Hint Resolve Forall_app.

  Lemma imps_imports : forall exit post k v bls base,
    LabelMap.MapsTo k v imports
    -> LabelMap.MapsTo k v (imps bls base exit post).
    induction bls; simpl; intuition.
    destruct (imports_global H).
    auto.
    destruct (imports_global H).
    auto.
  Qed.

  Hint Resolve imps_imports.

  Lemma imps_app1 : forall exit post bls2 k v bls1 base,
    exit < base
    -> LabelMap.MapsTo k v (imps bls1 base exit post)
    -> LabelMap.MapsTo k v (imps (bls1 ++ bls2) base exit post).
    induction bls1; simpl; intuition.

    apply LabelFacts.add_mapsto_iff in H0; intuition; subst; auto.

    apply LabelFacts.add_mapsto_iff in H0; intuition; subst; auto.
  Qed.

  Lemma imps_app2'' : forall k v exit exit' post post' bls base,
    LabelMap.MapsTo k v (imps bls base exit' post')
    -> (k = (modName, Local exit') /\ v = post') \/ LabelMap.MapsTo k v (imps bls base exit post).
    induction bls; simpl; intuition.

    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    right.
    apply LabelMap.add_2.
    apply imports_global in H1.
    destruct H1.
    destruct k; simpl in *; congruence.
    auto.
   
    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    eauto.
    apply IHbls in H1.
    intuition.
  Qed.

  Lemma imps_app2' : forall exit post bls2 k v exit' post' bls1 base,
    LabelMap.MapsTo k v (imps bls2 (base + N_of_nat (length bls1)) exit' post')
    -> exit < base
    -> (k = (modName, Local exit') /\ v = post') \/ LabelMap.MapsTo k v (imps (bls1 ++ bls2) base exit post).
    induction bls1; simpl; intuition.

    replace (base + 0) with base in H by nomega.
    apply imps_app2''; auto.

    replace (base + Npos (P_of_succ_nat (length bls1)))
      with (Nsucc base + N_of_nat (length bls1)) in H by nomega.
    apply IHbls1 in H; clear IHbls1; intuition.
  Qed.

  Lemma nth_error_app1 : forall A x (ls2 ls1 : list A) n,
    nth_error ls1 n = Some x
    -> nth_error (ls1 ++ ls2) n = Some x.
    induction ls1; destruct n; simpl; intuition; discriminate.
  Qed.

  Hint Resolve nth_error_app1.

  Lemma imps_app2 : forall exit post bls2 k v post' bl bls1 base offset,
    LabelMap.MapsTo k v (imps bls2 (base + N_of_nat (length bls1)) (base + offset) post')
    -> nth_error bls1 (nat_of_N offset) = Some (post', bl)
    -> exit < base
    -> LabelMap.MapsTo k v (imps (bls1 ++ bls2) base exit post).
    intros.
    eapply imps_app2' in H.
    intuition; subst; eauto.
    auto.
  Qed.

  Hint Resolve imps_app1 imps_app2.

  Hint Rewrite app_length : N.

  Ltac preSimp := simpl in *; intuition eauto; repeat (apply Forall_nil || apply Forall_cons); simpl.

  Ltac simp := repeat (match goal with
                         | [ x : codeGen _ _ _ _ _ |- _ ] => destruct x; simpl in *
                         | [ H : ex _ |- _ ] => destruct H
                         | [ H1 : notStuck _ _, H2 : _ |- _ ] => specialize (H1 _ _ _ H2)
                         | [ H : forall k v, _ |- _ ] => destruct (split_add H); clear H
                         | [ H : _ |- _ ] => destruct (specialize_imps H); clear H
                         | [ H : forall x, _ -> _ |- _ ] => specialize (H _ (refl_equal _))
                         | [ H : forall x y z, _ -> _ , H' : _ |- _ ] => specialize (H _ _ _ H')
                         | [ |- blockOk _ _ _ ] => red
                         | [ H : ?E = None -> False |- _ ] => case_eq E; intros; tauto || clear H
                         | [ H : _ |- _ ] => rewrite H
                         | [ H : ?P -> _ |- _ ] =>
                           match type of P with
                             | Prop => assert P by (lomega || auto); intuition
                           end
                         | [ x : N |- _ ] => unfold x in *; clear x
                       end; intuition; unfold evalBlock; simpl; autorewrite with N).

  Ltac finisher := repeat esplit; eauto 8.

  Ltac struct := preSimp; simp; finisher.

  Definition Seq (c1 c2 : cmd) : cmd.
    red; refine (fun pre =>
      let cout1 := c1 pre in
      let cout2 := c2 (Postcondition cout1) in
        {|
          Postcondition := Postcondition cout2;
          VerifCond := VerifCond cout1 /\ VerifCond cout2;
          Generate := fun Base Exit =>
            let cg2 := Generate cout2 Base Exit in
              let numBlocks := N_of_nat (length (Blocks cg2)) in
                let cg1 := Generate cout1 (Base + numBlocks) (Base + Entry cg2) in
                  {|
                    Entry := numBlocks + Entry cg1;
                    Blocks := Blocks cg2 ++ Blocks cg1
                  |}
        |}); abstract struct.
  Defined.

End imports.
