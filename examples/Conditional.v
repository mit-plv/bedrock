Require Import Bedrock Bool.

Open Scope list_scope.


Inductive bexp :=
| Test : rvalue -> test -> rvalue -> bexp
| Not : bexp -> bexp
| And : bexp -> bexp -> bexp
| Or : bexp -> bexp -> bexp.

Fixpoint bexpD (b : bexp) (stn : settings) (st : state) : option bool :=
  match b with
    | Test rv1 t rv2 =>
      match evalRvalue stn st rv1, evalRvalue stn st rv2 with
        | Some v1, Some v2 => Some (evalTest t v1 v2)
        | _, _ => None
      end
    | Not b => match bexpD b stn st with
                 | Some b => Some (negb b)
                 | None => None
               end
    | And b1 b2 => match bexpD b1 stn st, bexpD b2 stn st with
                     | Some v1, Some v2 => Some (v1 && v2)
                     | _, _ => None
                   end
    | Or b1 b2 => match bexpD b1 stn st, bexpD b2 stn st with
                    | Some v1, Some v2 => Some (v1 || v2)
                    | _, _ => None
                  end
  end.

Fixpoint size (b : bexp) : nat :=
  match b with
    | Test _ _ _ => 1
    | Not b => size b
    | And b1 b2 => size b1 + size b2
    | Or b1 b2 => size b1 + size b2
  end.

Import DefineStructured.

Section Cond.
  Variable imports : LabelMap.t assert.
  Hypothesis imports_global : importsGlobal imports.
  Variable modName : string.

  Fixpoint blocks (Base : N) (pre : assert) (b : bexp) (Tru Fals : N) : list (assert * block) :=
    match b with
      | Test rv1 t rv2 => (pre, (nil, Cond rv1 t rv2
        (modName, Local Tru)
        (modName, Local Fals))) :: nil
      | Not b => blocks Base pre b Fals Tru
      | And b1 b2 =>
        let Base' := (Base + N_of_nat (size b1))%N in
        blocks Base pre b1 Base' Fals
        ++ blocks Base' (fun stn_st =>
          [| bexpD b (fst stn_st) (snd stn_st) = Some true |] /\ pre stn_st)%PropX b2 Tru Fals
      | Or b1 b2 =>
        let Base' := (Base + N_of_nat (size b1))%N in
        blocks Base pre b1 Tru Base'
        ++ blocks Base' (fun stn_st =>
          [| bexpD b (fst stn_st) (snd stn_st) = Some false |] /\ pre stn_st)%PropX b2 Tru Fals
    end.

  Lemma blocks_first : forall b Base pre Tru Fals,
    exists bl, exists rest, blocks Base pre b Tru Fals = (pre, bl) :: rest.
    induction b; simpl; intuition eauto;
      match goal with
        | [ H : context[blocks _ _ ?B _ _] |- context[blocks ?Base ?pre ?B ?Tru ?False] ] =>
          specialize (H Base pre Tru False); destruct H as [ ? [ ? H ] ]; rewrite H
      end; simpl; eauto.
  Qed.

  Lemma length_size : forall b Base pre Tru Fals,
    length (blocks Base pre b Tru Fals) = size b.
    induction b; simpl; intuition; rewrite app_length; struct.
  Qed.

  Ltac choosePost :=
    match goal with
      | [ _ : LabelMap.MapsTo _ _ (imps _ _ _ _ _ ?post) |- LabelMap.MapsTo _ _ (imps _ _ _ _ _ ?post') ] =>
        equate post' post
    end.

  Hint Extern 2 (LabelMap.MapsTo _ _ _) =>
    eapply imps_app_2; [ assumption | | eassumption | nomega | nomega ];
      rewrite length_size; choosePost.

  Transparent evalInstrs.

  Hint Extern 1 (_ < _)%N => nomega.
  Hint Extern 1 (~(eq (A := LabelMap.key) _ _)) => lomega.

  Definition Cond_ (b : bexp) (Then Else : cmd imports modName) : cmd imports modName.
    red; refine (fun pre =>
      let cout1 := Then (fun stn_st => pre stn_st /\ [|bexpD b (fst stn_st) (snd stn_st) = Some true|])%PropX in
      let cout2 := Else (fun stn_st => pre stn_st /\ [|bexpD b (fst stn_st) (snd stn_st) = Some false|])%PropX in
      {|
        Postcondition := (fun stn_st => Postcondition cout1 stn_st \/ Postcondition cout2 stn_st)%PropX;
        VerifCond := (forall stn st specs, interp specs (pre (stn, st)) -> bexpD b stn st <> None)
          :: VerifCond cout1 ++ VerifCond cout2;
        Generate := fun Base Exit =>
          let Base' := (Nsucc (Nsucc Base) + N_of_nat (size b))%N in
          let cg1 := Generate cout1 Base' Base in
          let Base'' := (Base' + N_of_nat (length (Blocks cg1)))%N in
          let cg2 := Generate cout2 Base'' (Nsucc Base) in
          {|
            Entry := 2;
            Blocks := (Postcondition cout1, (nil, Uncond (RvLabel (modName, Local Exit))))
              :: (Postcondition cout2, (nil, Uncond (RvLabel (modName, Local Exit))))
              :: blocks (Nsucc (Nsucc Base)) pre b Base' Base''
              ++ Blocks cg1 ++ Blocks cg2
          |}
      |}).

    struct.

    match goal with
      | [ |- context[blocks ?Base ?pre ?b ?Tru ?Fals] ] =>
        let H := fresh in destruct (blocks_first b Base pre Tru Fals) as [ ? [ ? H ] ];
          rewrite H
    end.
    struct.

    struct;
      try match goal with
            | [ H : context[imps _ ?modName _ _ ?Exit ?post] |- context[Labels _ (?modName, Local ?Exit)] ] =>
              let H' := fresh in destruct (H (modName, Local Exit) post) as [ ? [ H' ] ]; eauto; rewrite H';
                repeat esplit; eauto; propxFo
          end.

    repeat apply Forall_app.

    admit.

    eauto 15.

    eauto 15.
  Defined.

End Cond.
