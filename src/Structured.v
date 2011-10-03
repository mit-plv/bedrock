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

    PreconditionOk : exists pre, exists bl, nth_error Blocks (nat_of_N Entry) = Some (pre, bl)
      /\ forall specs stn st, interp specs (Precondition stn st)
        -> interp specs (pre stn st);
    
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

  Inductive cmd :=
  | StraightLine : list instr -> cmd
  | Structured : (forall ci, codeOut ci) -> cmd.


  (** Sequencing *)

  Definition notStuck (pre : assert) (is : list instr) :=
    forall stn st specs, interp specs (pre stn st)
      -> evalInstrs stn st is <> None.

  Lemma lookup_imps : forall p bl exit post bls n base,
    nth_error bls (nat_of_N n) = Some (p, bl)
    -> LabelMap.MapsTo (modName, Local (Nsucc base + n)) p
    (imps bls (Nsucc base) exit post).
    induction bls; simpl in *; intuition.

    destruct (nat_of_N n); discriminate.

    induction n using Nind; simpl in *.

    injection H; clear H; intros; subst.
    autorewrite with N.
    apply LabelMap.add_1; reflexivity.

    autorewrite with N in *; simpl in *.
    apply (IHbls n (Nsucc base)) in H.
    apply LabelMap.add_2.
    intro.
    injection H0; clear H0; intros.
    nomega.
    
    replace (Nsucc base + Nsucc n) with (Nsucc (Nsucc base) + n) by nomega.
    assumption.
  Qed.

  Lemma lookup_imps_plus : forall {p bl exit post p' bls n base},
    nth_error bls (nat_of_N n) = Some (p, bl)
    -> LabelMap.MapsTo (modName, Local (Nsucc base + n)) p
    (LabelMap.add (modName, Local base) p'
      (imps bls (Nsucc base) exit post)).
    intros.
    apply LabelMap.add_2.

    intro.
    injection H0; clear H0; intros.
    nomega.

    eapply lookup_imps; eauto.
  Qed.

  Hint Resolve lookup_imps @lookup_imps_plus.
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
    apply LabelMap.add_2.
    intro.
    injection H; clear H; intros.
    nomega.
    apply LabelMap.add_1; reflexivity.

    apply LabelMap.add_2.
    apply imports_global in H3; destruct H3.
    destruct k; simpl in *; congruence.
    apply LabelMap.add_2.
    apply imports_global in H3; destruct H3.
    destruct k; simpl in *; congruence.
    assumption.

    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    apply LabelMap.add_2.
    intro.
    injection H; clear H; intros.
    nomega.
    apply LabelMap.add_1; reflexivity.

    specialize (IHbls _ H3).
    assert (n < Nsucc base) by nomega; intuition.
    apply LabelFacts.add_mapsto_iff in H5; intuition; subst.
    apply LabelMap.add_1; reflexivity.
    apply LabelMap.add_2; auto.
    apply LabelMap.add_2; auto.
  Qed.

  Hint Resolve imps_preserve.

  Lemma lt_succ : forall n, n < Nsucc n.
    intros; nomega.
  Qed.

  Lemma lt_succ' : forall n m, n < m -> n < Nsucc m.
    intros; nomega.
  Qed.

  Hint Immediate lt_succ lt_succ'.

  Hint Extern 1 (List.Forall _ _) => eapply Forall_impl; [ | eassumption ].

  Definition seq (c1 c2 : cmd) : cmd.
    refine (match c1, c2 with
              | StraightLine is1, StraightLine is2 => StraightLine (is1 ++ is2)

              | StraightLine is, Structured cf =>
                Structured (fun pre =>
                  let cout := cf (fun stn st =>
                    Ex st', [evalInstrs stn st' is = Some st] /\ pre stn st')%PropX in
                  {|
                    Postcondition := Postcondition cout;
                    VerifCond := notStuck pre is /\ VerifCond cout;
                    Generate := fun Base Exit =>
                      let cg := Generate cout (Nsucc Base) Exit in
                        {|
                          Entry := 0;
                          Blocks := (pre, (is, Uncond (RvLabel (modName, Local (Nsucc Base + Entry cg))))) :: Blocks cg
                        |}
                  |})

              | Structured cf, StraightLine is =>
                Structured (fun pre =>
                  let cout := cf pre in
                  {|
                    Postcondition := (fun stn st =>
                      Ex st', [evalInstrs stn st' is = Some st] /\ Postcondition cout stn st')%PropX;
                    VerifCond := VerifCond cout /\ notStuck (Postcondition cout) is;
                    Generate := fun Base Exit =>
                      let cg := Generate cout (Nsucc Base) Base in
                        {|
                          Entry := Nsucc (Entry cg);
                          Blocks := (Postcondition cout, (is, Uncond (RvLabel (modName, Local Exit)))) :: Blocks cg
                        |}
                  |})

              | Structured cf1, Structured cf2 =>
                Structured (fun pre =>
                  let cout1 := cf1 pre in
                  let cout2 := cf2 (Postcondition cout1) in
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
                  |})
            end); simpl in *; intuition eauto; repeat (apply Forall_nil || apply Forall_cons); simpl.

    Ltac simp := repeat (match goal with
                           | [ x : codeGen _ _ _ _ _ |- _ ] => destruct x; simpl in *
                           | [ H : ex _ |- _ ] => destruct H
                           | [ H1 : notStuck _ _, H2 : _ |- _ ] => specialize (H1 _ _ _ H2)
                           | [ H : _, H' : _ |- _ ] => specialize (H _ _ (lookup_imps_plus H')); destruct H; intuition
                           | [ |- blockOk _ _ _ ] => red
                           | [ H : ?E = None -> False |- _ ] => case_eq E; intros; tauto || clear H
                           | [ H : _ |- _ ] => rewrite H
                           | [ H : ?P -> _ |- _ ] =>
                             match type of P with
                               | Prop => assert P by auto; intuition
                             end
                         end; intuition; unfold evalBlock; simpl; autorewrite with N).
    Ltac finisher := repeat match goal with
                              | [ |- ex _ ] => esplit
                              | [ |- _ /\ _ ] => split
                              | [ H : _ |- interp _ _ ] => apply H; propxFo
                            end; (instantiate; eauto).

    Ltac t := simp; finisher.

    t.
    
    t.

    t.

    admit.

    admit.

    admit.

    admit.
  Qed.

End imports.
