Require Import Ascii AutoSep Wrap Malloc SinglyLinkedList StringOps XmlLex XmlSearch XmlOutput ArrayOps.

Set Implicit Arguments.


(* Patterns matching against XML trees *)
Inductive pat :=

(* Match CDATA constant. *)
| Cdata (const : string)

(* Record CDATA at this position via a variable. *)
| Var (text : string)

(* Match a specific tag at this level in the XML tree, then continue into its children. *)
| Tag (tag : string) (inner : pat)

(* Match two different patterns at this level of the tree. *)
| Both (p1 p2 : pat)

(* Match one pattern and then another in the part of the XML tree right after the match of the first. *)
| Ordered (p1 p2 : pat).

(* A full program: find all matches of a pattern, outputting the value of a variable for each. *)
Record program := {
  Pattern : pat;
  Output : xml
}.


(** * Our versions of the auxiliary functions from XmlSearch *)

Fixpoint freeVar (p : pat) (x : string) : Prop :=
  match p with
    | Cdata _ => False
    | Var text => x = text
    | Tag _ inner => freeVar inner x
    | Both p1 p2 => freeVar p1 x \/ freeVar p2 x
    | Ordered p1 p2 => freeVar p1 x \/ freeVar p2 x
  end.

Fixpoint wfPat (p : pat) : Prop :=
  match p with
    | Cdata const => goodSize (String.length const)
    | Var _ => True
    | Tag tag inner => goodSize (String.length tag) /\ wfPat inner
    | Both p1 p2 => wfPat p1 /\ wfPat p2 /\ (forall x, freeVar p1 x -> ~freeVar p2 x)
    | Ordered p1 p2 => wfPat p1 /\ wfPat p2 /\ (forall x, freeVar p1 x -> ~freeVar p2 x)
  end%type.

Fixpoint allCdatas (p : pat) : list string :=
  match p with
    | Cdata _ => nil
    | Var text => text :: nil
    | Tag _ inner => allCdatas inner
    | Both p1 p2 => allCdatas p2 ++ allCdatas p1
    | Ordered p1 p2 => allCdatas p2 ++ allCdatas p1
  end.


(** * Compiling patterns *)

Fixpoint compilePat (p : pat) : XmlSearch.pat :=
  match p with
    | Cdata const => XmlSearch.Cdata const
    | Var text => XmlSearch.Var (text ++ "_start") (text ++ "_len")
    | Tag tag inner => XmlSearch.Tag tag (compilePat inner)
    | Both p1 p2 => XmlSearch.Both (compilePat p1) (compilePat p2)
    | Ordered p1 p2 => XmlSearch.Ordered (compilePat p1) (compilePat p2)
  end%string.

Definition wf (pr : program) :=
  wfPat (Pattern pr)
  /\ XmlOutput.wf (Output pr)
  /\ cdatasGood (XmlSearch.allCdatas (compilePat (Pattern pr)))
  /\ forall start len, XmlOutput.freeVar (Output pr) (start, len)
    -> exists x, start = (x ++ "_start")%string /\ len = (x ++ "_len")%string
      /\ freeVar (Pattern pr) x.

Fixpoint allCdatas_both (p : pat) : list string :=
  match p with
    | Cdata _ => nil
    | Var text => (text ++ "_start")%string :: (text ++ "_len")%string :: nil
    | Tag _ inner => allCdatas_both inner
    | Both p1 p2 => allCdatas_both p2 ++ allCdatas_both p1
    | Ordered p1 p2 => allCdatas_both p2 ++ allCdatas_both p1
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

Lemma no_clash'' : forall s,
  underscore_free s
  -> forall p, In s (allCdatas_both p)
    -> False.
  induction p; simpl; intuition (subst; eauto using no_clash');
    match goal with
      | [ H : _ |- _ ] => apply in_app_or in H; tauto
    end.
Qed.

Lemma no_clash : forall s p,
  In s (allCdatas_both p)
  -> underscore_free s
  -> False.
  intros; eapply no_clash''; eauto.
Qed.

Local Hint Resolve no_clash.

Local Hint Extern 1 (underscore_free _) => simpl; intuition congruence.

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

Ltac injy :=
  match goal with
    | [ H : _ |- _ ] => solve [ apply append_inj' in H; subst; eauto ]
    | [ H : _ |- _ ] => apply (f_equal lastChar) in H;
      repeat rewrite lastChar_app in H by (simpl; omega); discriminate
    | [ H : _ |- _ ] =>
      apply (f_equal String.length) in H; simpl in H; rewrite length_append in H; simpl in H; omega
  end.

Lemma allCdatas_NoDup : forall p,
  NoDup (allCdatas p)
  -> NoDup (allCdatas_both p).
  induction p; simpl; intuition;
    repeat constructor; simpl; intuition;
      try match goal with
            | [ H : _ |- _ ] => apply append_inj in H; discriminate
          end;
  match goal with
    | [ H : NoDup _ |- _ ] =>
      specialize (NoDup_unapp1 _ _ H);
        specialize (NoDup_unapp2 _ _ H);
          specialize (NoDup_unapp_noclash _ _ H);
            clear H; intros
  end; apply NoDup_app; auto; intros;
  repeat match goal with
           | [ H : _ |- _ ] => apply In_allCdatas_both in H
         end; post; subst;
  injy.
Qed.

Local Hint Immediate allCdatas_NoDup.

Lemma freeVar_compile : forall x p,
  XmlSearch.freeVar (compilePat p) x
  -> In x (allCdatas_both p).
  induction p; simpl; intuition.
Qed.

Local Hint Immediate freeVar_compile.

Lemma allCdatas_freeVar : forall x p,
  In x (allCdatas p)
  -> freeVar p x.
  induction p; simpl; intuition;
    match goal with
      | [ H : _ |- _ ] =>
        apply in_app_or in H; tauto
    end.
Qed.

Local Hint Resolve allCdatas_freeVar.

Lemma wf_compile : forall p,
  wfPat p
  -> XmlSearch.wf (compilePat p).
  induction p; simpl; intuition;
    repeat match goal with
             | [ H : _ |- _ ] => apply freeVar_compile in H; apply In_allCdatas_both in H
           end; post; subst; injy.
Qed.

Local Hint Immediate wf_compile.

Lemma wf_NoDup : forall p,
  wfPat p
  -> NoDup (allCdatas p).
  induction p; simpl; intuition; try NoDup; eauto using NoDup_app.
Qed.


(** * Compiling programs *)

Section compileProgram.
  (** First, create a [vcgen] version that knows about [Pat], with some shameless copy-and-paste. *)

  Ltac vcgen_simp := cbv beta iota zeta delta [WrapC Wrap Pat Out
    map app imps
    LabelMap.add Entry Blocks Postcondition VerifCond
    Straightline_ Seq_ Diverge_ Fail_ Skip_ Assert_
    Structured.If_ Structured.While_ Goto_ Structured.Call_ IGoto
    setArgs Programming.Reserved Programming.Formals Programming.Precondition
    importsMap fullImports buildLocals blocks union Nplus Nsucc length N_of_nat
    List.fold_left ascii_lt string_lt label'_lt
    LabelKey.compare' LabelKey.compare LabelKey.eq_dec
    LabelMap.find
    toCmd Seq Instr Diverge Fail Skip Assert_
    Programming.If_ Programming.While_ Goto Programming.Call_ RvImm'
    Assign' localsInvariant localsInvariantCont
    regInL lvalIn immInR labelIn variableSlot string_eq ascii_eq
    andb Bool.eqb qspecOut
    ICall_ Structured.ICall_
    Assert_ Structured.Assert_
    LabelMap.Raw.find LabelMap.this LabelMap.Raw.add
    LabelMap.empty LabelMap.Raw.empty string_dec
    Ascii.ascii_dec string_rec string_rect sumbool_rec sumbool_rect Ascii.ascii_rec Ascii.ascii_rect
    Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym
    fst snd labl
    Ascii.N_of_ascii Ascii.N_of_digits N.compare Nmult Pos.compare Pos.compare_cont
    Pos.mul Pos.add LabelMap.Raw.bal
    Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec LabelMap.Raw.create
    ZArith_dec.Z_gt_le_dec Int.Z_as_Int.plus Int.Z_as_Int.max LabelMap.Raw.height
    ZArith_dec.Z_gt_dec Int.Z_as_Int._1 BinInt.Z.add Int.Z_as_Int._0 Int.Z_as_Int._2 BinInt.Z.max
    ZArith_dec.Zcompare_rec ZArith_dec.Z_ge_lt_dec BinInt.Z.compare ZArith_dec.Zcompare_rect
    ZArith_dec.Z_ge_dec label'_eq label'_rec label'_rect
    COperand1 CTest COperand2 Pos.succ
    makeVcs
    Note_ Note__
    IGotoStar_ IGotoStar AssertStar_ AssertStar
    Cond_ Cond
  ].

  Ltac vcgen := structured_auto vcgen_simp.


  (** Now, on to the interesting part.... *)

  Variable pr : program.

  Definition numCdatas := length (allCdatas_both (Pattern pr)).
  Definition reserved := numCdatas + 21.

  Definition preLvars := "lex" :: "res" :: "opos" :: "overflowed"
    :: "tagStart" :: "tagLen" :: "matched" :: "stack" :: "level" :: "tmp" :: allCdatas_both (Pattern pr).
  Definition lvars := "buf" :: "len" :: "obuf" :: "olen" :: preLvars.

  Definition mainS := SPEC("buf", "len", "obuf", "olen") reserving reserved
    Al bsI, Al bsO,
    PRE[V] array8 bsI (V "buf") * array8 bsO (V "obuf") * mallocHeap 0
      * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
    POST[R] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf") * mallocHeap 0
      * [| length bsO' = length bsO |] * [| R <= V "olen" |].

  Definition m := bimport [["xml_lex"!"next" @ [nextS], "xml_lex"!"position" @ [positionS],
                            "xml_lex"!"setPosition" @ [setPositionS], "xml_lex"!"tokenStart" @ [tokenStartS],
                            "xml_lex"!"tokenLength" @ [tokenLengthS], "malloc"!"malloc" @ [mallocS],
                            "malloc"!"free" @ [freeS], "sys"!"abort" @ [abortS], "sys"!"printInt" @ [printIntS],
                            "xml_lex"!"init" @ [initS], "xml_lex"!"delete" @ [deleteS],
                            "array8"!"copy" @ [copyS] ]]

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
         [Al bsI, Al bsO,
           PRE[V, R] array8 bsI (V "buf") * array8 bsO (V "obuf") * mallocHeap 0 * xmlp (V "len") R
             * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
           POST[R'] Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf") * mallocHeap 0
             * [| length bsO' = length bsO |] * [| R' <= V "olen" |]%word ];;
         "stack" <- 0;;
         "opos" <- 0;;
         "overflowed" <- 0;;

         Pat (fun bsO V => array8 bsO (V "obuf") * [| length bsO = wordToNat (V "olen") |]
           * [| V "opos" <= V "olen" |]%word)%Sep
         (fun bsO V R => Ex bsO', array8 bsO' (V "obuf") * [| length bsO' = length bsO |]
           * [| R <= V "olen" |]%word)%Sep
         (compilePat (Pattern pr))
         (Out
           (fun (_ : unit) V => mallocHeap 0 * xmlp (V "len") (V "lex")
             * Ex ls, sll ls (V "stack") * [| stackOk ls (V "len") |])%Sep
           (fun _ V R => [| R <= V "olen" |]%word * mallocHeap 0)%Sep
           (XmlSearch.allCdatas (compilePat (Pattern pr)))
           (Output pr));;

         Call "xml_lex"!"delete"("lex")
         [Al ls,
           PRE[V] [| V "opos" <= V "olen" |]%word * mallocHeap 0 * sll ls (V "stack")
           POST[R] [| R <= V "olen" |]%word * mallocHeap 0];;

         [Al ls,
           PRE[V] [| V "opos" <= V "olen" |]%word * mallocHeap 0 * sll ls (V "stack")
           POST[R] [| R <= V "olen" |]%word * mallocHeap 0]
         While ("stack" <> 0) {
           "lex" <- "stack";;
           "stack" <-* "stack"+4;;

           Call "malloc"!"free"(0, "lex", 2)
           [Al ls,
             PRE[V] [| V "opos" <= V "olen" |]%word * mallocHeap 0 * sll ls (V "stack")
             POST[R] [| R <= V "olen" |]%word * mallocHeap 0]
         };;

         If ("overflowed" = 1) {
           Return 0
         } else {
           Return "opos"
         }))%SP
      |}
    }}.

  Hypothesis wellFormed : wf pr.

  Let distinct : NoDup (allCdatas (Pattern pr)).
    destruct wellFormed; intros; apply wf_NoDup; auto.
  Qed.

  Ltac xomega := unfold preLvars, reserved, numCdatas; simpl; omega.

  Opaque mult.

  Hint Extern 1 (@eq W _ _) => words.

  Ltac reger := fold (@length string) in *;
    repeat match goal with
             | [ H : Regs _ _ = _ |- _ ] => rewrite H
           end; try rewrite wplus_wminus; repeat rewrite <- mult4_S in *.

  Ltac prelude :=
    intros;
      repeat match goal with
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
    post;
    try match goal with
          | [ st : (settings * state)%type |- _ ] => destruct st; simpl in *
        end;
    fold (@length string) in *; varer 48 "stack"; varer 8 "len"; varer 20 "lex"; varer 28 "opos";
      varer 32 "overflowed";
      try match goal with
            | [ _ : context[Assign _ (RvLval (LvMem (Sp + natToW 0)%loc))] |- _ ] => varer 0 "rp"
          end;
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
      end;
      try match goal with
            | [ _ : context[Binop (LvReg Rv) _ Plus (RvImm (natToW ?N))],
              _ : context[locals_call _ _ _ _ _ _ ?M] |- _ ] => replace N with M in * by (simpl; omega)
          end; try rewrite inBounds_sel in *.

  Ltac my_descend :=
    repeat match goal with
             | [ H : In _ _ |- _ ] => clear H
           end;
    try match goal with
          | [ st : (settings * state)%type |- _ ] => destruct st; simpl in *
        end;
    descend; reger; try rewrite inBounds_sel in *.

  Ltac my_evaluate := evaluate SinglyLinkedList.hints.
  Ltac my_step := step SinglyLinkedList.hints.

  Ltac invoke1 :=
    match goal with
      | [ H : interp _ _, H' : _ |- _ ] => apply H' in H; clear H'
    end.

  Ltac t' := post; repeat invoke1; prep; my_evaluate; my_descend; repeat (my_step; my_descend); eauto.

  Ltac easy :=
    try match goal with
          | [ H : XmlOutput.freeVar _ _, H' : forall start len : string, _ |- _ ] =>
            apply H' in H; post; subst
        end;
    solve [ hnf; simpl; intuition (subst; try congruence; eauto) ].

  Ltac pre := try destruct wellFormed;
    repeat match goal with
             | [ |- context[vcs] ] => wrap0
           end.

  Hint Resolve no_clash' Forall_app.

  Lemma xall_underscore : forall p,
    List.Forall (fun p => not (underscore_free (fst p)) /\ not (underscore_free (snd p)))
    (XmlSearch.allCdatas (compilePat p)).
    induction p; simpl; intuition eauto.
  Qed.

  Lemma inBounds_swizzle : forall V V' p,
    (forall x, x <> "overflowed" -> x <> "opos" -> sel V x = sel V' x)
    -> inBounds (XmlSearch.allCdatas (compilePat p)) V
    -> inBounds (XmlSearch.allCdatas (compilePat p)) V'.
    intros.
    rewrite <- inBounds_sel.
    rewrite <- inBounds_sel in H0.
    eapply Forall_impl2; [ apply H0 | apply xall_underscore | ].
    simpl; intuition; match goal with
                        | [ x : (string * string)%type |- _ ] => destruct x; simpl in *
                      end.
    repeat rewrite H in * by (intro; subst; simpl in *; intuition congruence).
    auto.
  Qed.

  Hint Immediate inBounds_swizzle.

  Ltac prove_irrel :=
    repeat match goal with
             | [ V : vals |- _ ] =>
               match goal with
                 | [ |- context[V ?x] ] => change (V x) with (sel V x)
               end
           end;
    match goal with
      | [ H : forall x : string, _ |- _ ] =>
        repeat rewrite H by intuition (congruence || eauto)
    end; reflexivity || cancel auto_ext; solve [ eauto ].

  Ltac t := easy || prelude || prove_irrel || t'.

  Lemma stackOk_nil : forall len, stackOk nil len.
    constructor.
  Qed.

  Hint Immediate stackOk_nil.

  Lemma freeVar_all : forall x p,
    freeVar p x
    -> In x (allCdatas p).
    induction p; simpl; intuition.
  Qed.

  Lemma freeVar_compile' : forall x p,
    freeVar p x
    -> In (x ++ "_start", x ++ "_len")%string (XmlSearch.allCdatas (compilePat p)).
    induction p; simpl; intuition.
  Qed.

  Hint Extern 1 (_ <= _)%nat =>
    match goal with
      | [ H : inBounds _ _ |- _ ] => eapply Forall_forall in H; [ | eauto using freeVar_compile' ]
    end.

  Lemma freeVar_start : forall x p,
    freeVar p x
    -> In (x ++ "_start")%string (allCdatas_both p).
    induction p; simpl; intuition.
  Qed.

  Lemma freeVar_len : forall x p,
    freeVar p x
    -> In (x ++ "_len")%string (allCdatas_both p).
    induction p; simpl; intuition.
  Qed.

  Hint Immediate freeVar_start freeVar_len.

  Hint Extern 1 (NoDup (_ :: _)) => repeat constructor; simpl; intuition injy.


  Opaque mult.

  Hint Constructors unit.
  Hint Immediate freeVar_compile'.

  Theorem ok : moduleOk m.
    destruct wellFormed; vcgen;
      (intros; try match goal with
                     | [ H : importsGlobal _ |- _ ] => clear H
                   end; pre); abstract t.
  Qed.

End compileProgram.
