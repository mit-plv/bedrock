Require Import Ascii AutoSep Wrap Malloc SinglyLinkedList StringMatch XmlLex XmlSearch.

Set Implicit Arguments.


(* Patterns matching against XML trees *)
Inductive pat :=

(* Record CDATA at this position in the specified variable. *)
| Cdata (text : string)

(* Match a specific tag at this level in the XML tree, then continue into its children. *)
| Tag (tag : string) (inner : pat)

(* Match two different patterns at this level of the tree. *)
| Both (p1 p2 : pat).

(* A full program: find all matches of a pattern, outputting the value of a variable for each. *)
Record program := {
  Pattern : pat;
  Output : string
}.


(** * Our versions of the auxiliary functions from XmlSearch *)

Fixpoint freeVar (p : pat) (x : string) : Prop :=
  match p with
    | Cdata text => x = text
    | Tag _ inner => freeVar inner x
    | Both p1 p2 => freeVar p1 x \/ freeVar p2 x
  end.

Fixpoint wf (p : pat) : Prop :=
  match p with
    | Cdata _ => True
    | Tag tag inner => goodSize (String.length tag) /\ wf inner
    | Both p1 p2 => wf p1 /\ wf p2 /\ (forall x, freeVar p1 x -> ~freeVar p2 x)
  end%type.

Fixpoint allCdatas (p : pat) : list string :=
  match p with
    | Cdata text => text :: nil
    | Tag _ inner => allCdatas inner
    | Both p1 p2 => allCdatas p2 ++ allCdatas p1
  end.


(** * Compiling patterns *)

Fixpoint compilePat (p : pat) : XmlSearch.pat :=
  match p with
    | Cdata text => XmlSearch.Cdata (text ++ "_start") (text ++ "_len")
    | Tag tag inner => XmlSearch.Tag tag (compilePat inner)
    | Both p1 p2 => XmlSearch.Both (compilePat p1) (compilePat p2)
  end%string.

Fixpoint allCdatas_both (p : pat) : list string :=
  match p with
    | Cdata text => (text ++ "_start")%string :: (text ++ "_len")%string :: nil
    | Tag _ inner => allCdatas_both inner
    | Both p1 p2 => allCdatas_both p2 ++ allCdatas_both p1
  end.

Fixpoint underscore_free (s : string) : Prop :=
  match s with
    | ""%string => True
    | String ch s' => ch <> "_"%char /\ underscore_free s'
  end.

Lemma no_clash' : forall s' s,
  underscore_free (s ++ String "_"  s')%string
  -> False.
  induction s; simpl; intuition.
Qed.

Lemma no_clash : forall s,
  underscore_free s
  -> forall p, In s (allCdatas_both p)
    -> False.
  induction p; simpl; intuition (subst; eauto using no_clash');
    match goal with
      | [ H : _ |- _ ] => apply in_app_or in H; tauto
    end.
Qed.

Local Hint Extern 1 False => eapply no_clash; [ | eassumption ]; (cbv beta; simpl; intuition congruence).

Lemma append_inj : forall s1 s2 s,
  (s ++ s1 = s ++ s2)%string
  -> s1 = s2.
  induction s; simpl; intuition.
Qed.

Lemma NoDup_app : forall A (ls2 : list A),
  NoDup ls2
  -> forall ls1, NoDup ls1
    -> (forall x, In x ls1 -> In x ls2 -> False)
    -> NoDup (ls1 ++ ls2).
  induction 2; simpl; intuition;
    constructor; simpl; intuition eauto;
      match goal with
        | [ H : _ |- _ ] => apply in_app_or in H; intuition eauto
      end.
Qed.

Lemma NoDup_unapp_noclash : forall A (ls2 ls1 : list A),
  NoDup (ls1 ++ ls2)
  -> (forall x, In x ls1 -> In x ls2 -> False).
  induction ls1; inversion 1; simpl in *; subst; intuition (subst; eauto using in_or_app).
Qed.

Lemma In_allCdatas_both : forall x p,
  In x (allCdatas_both p)
  -> exists y, In y (allCdatas p) /\ (x = y ++ "_start" \/ x = y ++ "_len")%string.
  induction p; simpl; intuition (subst; eauto);
    match goal with
      | [ H : _ |- _ ] =>
        apply in_app_or in H; post; subst; eauto 6 using in_or_app
    end.
Qed.

Lemma length_append : forall s2 s1,
  String.length (s1 ++ s2) = String.length s1 + String.length s2.
  induction s1; simpl; intuition.
Qed.

Lemma append_inj' : forall s s1 s2,
  (s1 ++ s = s2 ++ s)%string
  -> s1 = s2.
  induction s1; destruct s2; simpl; intuition;
    match goal with
      | [ H : _ |- _ ] =>
        apply (f_equal String.length) in H; simpl in H; rewrite length_append in H; omega
      | [ H : String _ _ = String _ _ |- _ ] =>
        injection H; clear H; intros; f_equal; auto
    end.
Qed.

Fixpoint lastChar (s : string) : ascii :=
  match s with
    | ""%string => " "%char
    | String ch ""%string => ch
    | String _ s' => lastChar s'
  end.

Lemma lastChar_app : forall s2,
  (String.length s2 > 0)%nat
  -> forall s1, lastChar (s1 ++ s2) = lastChar s2.
  induction s1; simpl; intuition;
    destruct s1; simpl in *; auto;
      destruct s2; simpl in *; auto; omega.
Qed.

Lemma allCdatas_NoDup : forall p,
  NoDup (allCdatas p)
  -> NoDup (allCdatas_both p).
  induction p; simpl; intuition.
  repeat constructor; simpl; intuition;
    match goal with
      | [ H : _ |- _ ] => apply append_inj in H; discriminate
    end.
  match goal with
    | [ H : NoDup _ |- _ ] =>
      specialize (NoDup_unapp1 _ _ H);
        specialize (NoDup_unapp2 _ _ H);
          specialize (NoDup_unapp_noclash _ _ H);
            clear H; intros
  end; apply NoDup_app; auto; intros.
  repeat match goal with
           | [ H : _ |- _ ] => apply In_allCdatas_both in H
         end; post; subst;
  match goal with
    | [ H : _ |- _ ] => solve [ apply append_inj' in H; subst; eauto ]
    | [ H : _ |- _ ] => apply (f_equal lastChar) in H;
      repeat rewrite lastChar_app in H by (simpl; omega); discriminate
  end.
Qed.

Local Hint Immediate allCdatas_NoDup.


(** * Compiling programs *)

Section compileProgram.
  Variable pr : program.

  Definition numCdatas := length (allCdatas_both (Pattern pr)).
  Definition reserved := numCdatas + 18.

  Definition preLvars := "lex" :: "res"
    :: "tagStart" :: "tagLen" :: "matched" :: "stack" :: "level" :: allCdatas_both (Pattern pr).
  Definition lvars := "buf" :: "len" :: preLvars.

  Definition mainS := SPEC("buf", "len") reserving reserved
    Al bs,
    PRE[V] array8 bs (V "buf") * mallocHeap 0 * [| length bs = wordToNat (V "len") |]
    POST[_] array8 bs (V "buf") * mallocHeap 0.

  Definition m := bimport [["xml_lex"!"next" @ [nextS], "xml_lex"!"position" @ [positionS],
                            "xml_lex"!"setPosition" @ [setPositionS], "xml_lex"!"tokenStart" @ [tokenStartS],
                            "xml_lex"!"tokenLength" @ [tokenLengthS], "malloc"!"malloc" @ [mallocS],
                            "malloc"!"free" @ [freeS], "sys"!"abort" @ [abortS], "sys"!"write" @ [writeS],
                            "xml_lex"!"init" @ [initS], "xml_lex"!"delete" @ [deleteS] ]]
    bmodule "xml_prog" {{
      {|
        FName := "main";
        FVars := lvars;
        FReserved := 11;
        FPrecondition := Precondition mainS None;
        FBody := Seq (Assign' ((fun _ => LvMem (Indir Sp O)):lvalue') Rp)
        (Seq (fun _ _ =>
          Structured nil
          (fun im mn _ =>
            Structured.Assert_ im mn
            (Precondition mainS (Some lvars))))
        ("lex" <-- Call "xml_lex"!"init"("len")
          [Al bs,
            PRE[V, R] array8 bs (V "buf") * mallocHeap 0 * xmlp (V "len") R * [| length bs = wordToNat (V "len") |]
            POST[_] array8 bs (V "buf") * mallocHeap 0];;
         "stack" <- 0;;
         Diverge)%SP)
      |}
    }}.

  Hypothesis distinct : NoDup (allCdatas (Pattern pr)).

  Ltac xomega := unfold preLvars, reserved, numCdatas; simpl; omega.

  Opaque mult.

  Hint Extern 1 (@eq W _ _) => words.

  Ltac reger := fold (@length string) in *;
    repeat match goal with
             | [ H : Regs _ _ = _ |- _ ] => rewrite H
           end; try rewrite wplus_wminus; try rewrite <- mult4_S.

  Ltac prelude :=
    intros;
      match goal with
        | [ H : _ |- _ ] =>
          eapply localsInvariant_inEx; [ | apply H ]; clear H; simpl; intros
      end;
      eapply (@localsInvariant_in preLvars); try eassumption; try reflexivity; try xomega;
        try solve [ repeat constructor; simpl; intuition (try congruence; eauto) ];
          (intros ? ? Hrew; repeat rewrite Hrew by (simpl; tauto); reflexivity).

  Ltac varer n s :=
    change (Sp + n)%loc with (Sp + variablePosition ("rp" :: lvars) s)%loc in *;
      assert (In s ("rp" :: lvars)) by (simpl; tauto).

  Ltac prep :=
    fold (@length string) in *; varer 32 "stack"; varer 8 "len"; varer 12 "lex";
      try match goal with
            | [ H : context[Binop (LvReg Rv) (RvLval (LvReg Sp)) Plus (RvImm (natToW ?X))] |- _ ] =>
              replace X with (S (S (S (S (4 * Datatypes.length lvars)))))%nat in * by xomega
          end;
      try match goal with
            | [ H : context[locals _ _ ?X _] |- _ ] =>
              replace X with 11 in * by xomega
          end;
      match goal with
        | [ H : context[locals ?ns ?vs ?avail ?p]
            |- context[locals ?ns' _ ?avail' _] ] =>
          match avail' with
            | avail => fail 1
            | _ =>
              let offset := constr:(S (S (S (S (4 * List.length lvars))))) in
                change (locals ns vs avail p) with (locals_call ns vs avail p ns' avail' offset) in H;
                  assert (ok_call ns ns' avail avail' offset)%nat
                    by (hnf; intuition; xomega || NoDup)
          end
        | [ _ : evalInstrs _ _ ?E = None, H : context[locals ?ns ?vs ?avail ?p] |- _ ] =>
          let ns' := slotVariables E in
            match ns' with
              | nil => fail 1
              | _ =>
                let ns' := constr:("rp" :: ns') in
                  let offset := constr:(S (S (S (S (4 * List.length lvars))))) in
                    change (locals ns vs avail p) with (locals_call ns vs avail p ns' 0 offset) in H;
                      assert (ok_call ns ns' avail 0 offset)%nat by
                        (hnf; intuition; xomega || NoDup)
            end
        | _ => idtac
      end.

  Ltac my_descend := repeat match goal with
                              | [ H : In _ _ |- _ ] => clear H
                            end; descend; reger.

  Ltac t' := post; prep; evaluate auto_ext; my_descend; repeat (step auto_ext; my_descend).
  Ltac t := prelude || t'.

  Theorem ok : moduleOk m.
    vcgen.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
  Qed.

End compileProgram.
