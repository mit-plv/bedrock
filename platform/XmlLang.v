Require Import Ascii Bool AutoSep Wrap Malloc SinglyLinkedList Bags NumOps Buffers.
Require Import StringOps XmlLex XmlSearch XmlOutput ArrayOps.
Require Import RelDb RelDbCondition RelDbSelect RelDbInsert RelDbDelete.

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

(* Expressions for data queries and updates *)
Inductive exp :=
| Const (s : string)
| Input (text : string).

Definition equality := (string * exp)%type.
Definition condition := list equality.

(* Language for generating XML code *)
Inductive xml :=
| XCdata (const : string)
| XVar (text : string)
| XTag (tag : string) (inner : list xml)
| XColumn (tab col : string)
| XSelect (tab : string) (cond : condition) (inner : xml).

Section xml_ind'.
  Variable P : xml -> Prop.

  Hypothesis H_Cdata : forall const, P (XCdata const).

  Hypothesis H_Var : forall text, P (XVar text).

  Hypothesis H_Tag : forall tag inner, List.Forall P inner -> P (XTag tag inner).

  Hypothesis H_Column : forall tab col, P (XColumn tab col).

  Hypothesis H_Select : forall tab cond inner, P inner -> P (XSelect tab cond inner).

  Fixpoint xml_ind' (xm : xml) : P xm :=
    match xm with
      | XCdata const => H_Cdata const
      | XVar text => H_Var text
      | XTag tag inner => H_Tag tag ((fix xmls_ind (xms : list xml) : List.Forall P xms :=
        match xms with
          | nil => Forall_nil _
          | xm :: xms' => Forall_cons _ (xml_ind' xm) (xmls_ind xms')
        end) inner)
      | XColumn tab col => H_Column tab col
      | XSelect tab cond inner => H_Select tab cond (xml_ind' inner)
    end.
End xml_ind'.

Opaque xml_ind'.

(* Language of actions to take for matched patterns *)
Inductive action :=
| Insert (tab : string) (es : list exp)
| Delete (tab : string) (cond : condition)
| Output (xm : xml)
| Seq (a1 a2 : action).

(* A full program *)
Inductive program :=
| Rule (p : pat) (a : action)
| PSeq (pr1 pr2 : program).


(** * Our versions of the auxiliary functions from XmlSearch *)

Fixpoint freeVar (p : pat) (x : string) : Prop :=
  match p with
    | Cdata _ => False
    | Var text => x = text
    | Tag _ inner => freeVar inner x
    | Both p1 p2 => freeVar p1 x \/ freeVar p2 x
    | Ordered p1 p2 => freeVar p1 x \/ freeVar p2 x
  end.

Fixpoint pwf (p : pat) : Prop :=
  match p with
    | Cdata const => goodSize (String.length const)
    | Var _ => True
    | Tag tag inner => goodSize (String.length tag) /\ pwf inner
    | Both p1 p2 => pwf p1 /\ pwf p2 /\ (forall x, freeVar p1 x -> ~freeVar p2 x)
    | Ordered p1 p2 => pwf p1 /\ pwf p2 /\ (forall x, freeVar p1 x -> ~freeVar p2 x)
  end%type.

Fixpoint allCdatas (p : pat) : list string :=
  match p with
    | Cdata _ => nil
    | Var text => text :: nil
    | Tag _ inner => allCdatas inner
    | Both p1 p2 => allCdatas p2 ++ allCdatas p1
    | Ordered p1 p2 => allCdatas p2 ++ allCdatas p1
  end.


(** * Our versions of the auxiliary functions from XmlOutput *)

Definition ewf (e : exp) : Prop :=
  match e with
    | Const s => goodSize (String.length s)
    | Input _ => True
  end.

Definition ewfs := List.Forall ewf.

Definition eqwf (sch : schema) (e : equality) : Prop :=
  In (fst e) sch /\ ewf (snd e).

Definition cwf sch : condition -> Prop := List.Forall (eqwf sch).

Fixpoint xwf (avs ts : tables) (xm : xml) : Prop :=
  match xm with
    | XCdata const => goodSize (String.length const)
    | XVar _ => True
    | XTag tag inner => goodSize (String.length tag + 3)
      /\ ForallR (xwf avs ts) inner
    | XColumn tab col => exists t, In t avs /\ Name t = tab
      /\ In col (Schema t)
    | XSelect tab cond inner => exists t, In t ts /\ Name t = tab
      /\ cwf (Schema t) cond
      /\ xwf (t :: avs) (removeTable tab ts) inner
  end.

Definition efreeVar (e : exp) (x : string) : Prop :=
  match e with
    | Const _ => False
    | Input text => x = text
  end.

Fixpoint xfreeVar (xm : xml) (x : string) : Prop :=
  match xm with
    | XCdata _ => False
    | XVar text => x = text
    | XTag _ inner => ExistsR (fun xm' => xfreeVar xm' x) inner
    | XColumn _ _ => False
    | XSelect _ cond inner => List.Exists (fun e => efreeVar (snd e) x) cond
      \/ xfreeVar inner x
  end.

Fixpoint xbindsRowVar (xm : xml) (x : string) : Prop :=
  match xm with
    | XCdata _ => False
    | XVar _ => False
    | XTag _ inner => ExistsR (fun xm' => xbindsRowVar xm' x) inner
    | XColumn _ _ => False
    | XSelect tab _ inner => x = tab \/ xbindsRowVar inner x
  end.


(** * Compiling to other [Xml*] modules' languages *)

Fixpoint compilePat (p : pat) : XmlSearch.pat :=
  match p with
    | Cdata const => XmlSearch.Cdata const
    | Var text => XmlSearch.Var (text ++ "_start") (text ++ "_len")
    | Tag tag inner => XmlSearch.Tag tag (compilePat inner)
    | Both p1 p2 => XmlSearch.Both (compilePat p1) (compilePat p2)
    | Ordered p1 p2 => XmlSearch.Ordered (compilePat p1) (compilePat p2)
  end.

Definition compileExp (e : exp) : RelDb.exp :=
  match e with
    | Const s => RelDb.Const s
    | Input text => RelDb.Input (text ++ "_start") (text ++ "_len")
  end.

Definition compileExps := map compileExp.

Definition compileEquality (e : equality) : RelDb.equality :=
  (fst e, compileExp (snd e)).

Definition compileCondition : condition -> RelDb.condition :=
  map compileEquality.

Fixpoint compileXml (p : xml) : XmlOutput.xml :=
  match p with
    | XCdata const => XmlOutput.Cdata const
    | XVar text => XmlOutput.Var (text ++ "_start") (text ++ "_len")
    | XTag tag inner => XmlOutput.Tag tag (map compileXml inner)
    | XColumn tab col => XmlOutput.Column tab col
    | XSelect tab cond inner => XmlOutput.Select tab
      (tab ++ "_row") (tab ++ "_data") (compileCondition cond)
      (compileXml inner)
  end.


(** * Combined well-formedness and related lemmas *)

Fixpoint awf (avs ts : tables) (a : action) : Prop :=
  match a with
    | Insert tab es => exists t, In t ts /\ Name t = tab
      /\ length es = length (Schema t) /\ ewfs es
    | Delete tab cond => exists t, In t ts /\ Name t = tab
      /\ cwf (Schema t) cond
    | Output xm => xwf avs ts xm
    | Seq a1 a2 => awf avs ts a1 /\ awf avs ts a2
  end.

Fixpoint afreeVar (a : action) (x : string) : Prop :=
  match a with
    | Insert _ es => List.Exists (fun e => efreeVar e x) es
    | Delete _ cond => List.Exists (fun e => efreeVar (snd e) x) cond
    | Output xm => xfreeVar xm x
    | Seq a1 a2 => afreeVar a1 x \/ afreeVar a2 x
  end.

Fixpoint wf (ts : tables) (pr : program) : Prop :=
  match pr with
    | Rule p a => pwf p /\ awf nil ts a
      /\ (forall x, afreeVar a x -> freeVar p x)
    | PSeq pr1 pr2 => wf ts pr1 /\ wf ts pr2
  end.

Fixpoint allCdatas_both (p : pat) : list string :=
  match p with
    | Cdata _ => nil
    | Var text => (text ++ "_start")%string :: (text ++ "_len")%string :: nil
    | Tag _ inner => allCdatas_both inner
    | Both p1 p2 => allCdatas_both p2 ++ allCdatas_both p1
    | Ordered p1 p2 => allCdatas_both p2 ++ allCdatas_both p1
  end.

Fixpoint member (s : string) (ss : list string) : bool :=
  match ss with
    | nil => false
    | s0 :: ss => string_eq s s0 || member s ss
  end.

Fixpoint addTo (ss1 ss2 : list string) : list string :=
  match ss1 with
    | nil => ss2
    | s :: ss1 => addTo ss1 (if member s ss2 then ss2 else s :: ss2)
  end.

Fixpoint cdatasOf (pr : program) : list string :=
  match pr with
    | Rule p _ => allCdatas_both p
    | PSeq pr1 pr2 => addTo (cdatasOf pr1) (cdatasOf pr2)
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
  pwf p
  -> XmlSearch.wf (compilePat p).
  induction p; simpl; intuition;
    repeat match goal with
             | [ H : _ |- _ ] => apply freeVar_compile in H; apply In_allCdatas_both in H
           end; post; subst; injy.
Qed.

Local Hint Immediate wf_compile.

Lemma wf_NoDup : forall p,
  pwf p
  -> NoDup (allCdatas p).
  induction p; simpl; intuition; try NoDup; eauto using NoDup_app.
Qed.

Fixpoint allCursors_both' (xm : xml) : list string :=
  match xm with
    | XCdata _ => nil
    | XVar _ => nil
    | XTag _ inners => fold_left (fun ls xm => addTo (allCursors_both' xm) ls) inners nil
    | XColumn _ _ => nil
    | XSelect tab _ inner => (tab ++ "_row")%string :: (tab ++ "_data")%string
      :: allCursors_both' inner
  end.

Fixpoint allCursors_both (a : action) : list string :=
  match a with
    | Insert _ _ => nil
    | Delete tab _ => (tab ++ "_row")%string :: (tab ++ "_data")%string :: nil
    | Output xm => allCursors_both' xm
    | Seq a1 a2 => addTo (allCursors_both a1) (allCursors_both a2)
  end.

Fixpoint cursorsOf (pr : program) : list string :=
  match pr with
    | Rule _ a => allCursors_both a
    | PSeq pr1 pr2 => addTo (cursorsOf pr1) (cursorsOf pr2)
  end.


(** * Compiling programs *)

Section compileProgram.
  Variable pr : program.

  Definition numCdatas := length (cdatasOf pr).
  Definition numCursors := length (cursorsOf pr).
  Definition reserved := numCdatas + numCursors + 25.

  Definition preLvars := "lex" :: "res" :: "opos" :: "overflowed"
    :: "tagStart" :: "tagLen" :: "matched" :: "stack" :: "level" :: "tmp"
    :: "ibuf" :: "row" :: "ilen" :: "ipos"
    :: cdatasOf pr ++ cursorsOf pr.
  Definition lvars := "buf" :: "len" :: "obuf" :: "olen" :: preLvars.

  Definition db := starL (fun t => RelDb.table (Schema t) (Address t)).

  Definition mainS ts := SPEC("buf", "len", "obuf", "olen", "dummy") reserving reserved
    Al bsI, Al bsO,
    PRE[V] db ts
      * array8 bsI (V "buf") * array8 bsO (V "obuf") * mallocHeap 0
      * [| length bsI = wordToNat (V "len") |]
      * [| length bsO = wordToNat (V "olen") |]
    POST[R] db ts
      * Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf") * mallocHeap 0
      * [| length bsO' = length bsO |] * [| R <= V "olen" |].

  Lemma string_eq_true : forall s1 s2,
    string_eq s1 s2 = false -> s1 <> s2.
    intros; intro; subst; rewrite string_eq_true in *; discriminate.
  Qed.

  Lemma member_means : forall x ls,
    if member x ls then In x ls else ~In x ls.
    induction ls; simpl; intuition.
    generalize (@string_eq_false x a), (@string_eq_true x a).
    destruct (string_eq x a); simpl; intuition.
    destruct (member x ls); eauto.
    destruct (string_dec x a); subst; auto.
    apply H in n; discriminate.
    destruct (member x ls); eauto.
    intuition.
  Qed.

  Hint Constructors NoDup.

  Lemma NoDup_addTo : forall ls1 ls2, NoDup ls2
    -> NoDup (addTo ls1 ls2).
    induction ls1; simpl; intuition.
    generalize (member_means a ls2); destruct (member a ls2); intuition.
  Qed.    

  Hint Immediate NoDup_addTo.

  Lemma cdatas_distinct : forall ts, wf ts pr
    -> NoDup (cdatasOf pr).
    induction pr; simpl in *; intuition
      eauto using allCdatas_NoDup, wf_NoDup, NoDup_addTo.
  Qed.

  Lemma In_addTo_or : forall x ls1 ls2,
    In x (addTo ls1 ls2)
    -> In x ls1 \/ In x ls2.
    clear; induction ls1; simpl; intuition.
    generalize (member_means a ls2); destruct (member a ls2); intuition;
      destruct (IHls1 _ H); simpl in *; intuition.
  Qed.

  Lemma append_underscore_free : forall suff suff' tab tab0,
    underscore_free tab
    -> underscore_free tab0
    -> (tab0 ++ String "_" suff)%string = (tab ++ String "_" suff')%string
    -> tab0 = tab.
    induction tab; destruct tab0; simpl; intuition.
    injection H1; clear H1; intros; subst.
    f_equal; eauto.
  Qed.

  Lemma Forall_removeTable : forall P tab ts,
    List.Forall P ts
    -> List.Forall P (removeTable tab ts).
    induction 1; simpl; intuition; ift.
  Qed.

  Hint Immediate Forall_removeTable.

  Hint Immediate NoDup_unapp1 NoDup_unapp2.

  Definition NoDups avs ts := NoDup (Names avs ++ Names ts).

  Lemma NoDups_descend : forall tab t avs ts,
    NoDups avs ts
    -> In t ts
    -> Name t = tab
    -> NoDups (t :: avs) (removeTable tab ts).
    clear; unfold NoDups; simpl; intros; subst.
    constructor.
    intro.
    apply in_app_or in H1; intuition eauto using removeTable_contra.
    eapply NoDups_unapp_cross in H; eauto.
    apply H.
    apply in_map; auto.
    apply NoDups_app; eauto using NoDup_removeTable.
    intros.
    intro.
    eapply NoDups_unapp_cross in H; eauto.
  Qed.

  Hint Immediate NoDups_descend.

  Lemma Forall_removeTable' : forall P tab ts,
    List.Forall P ts
    -> List.Forall (fun t => Name t <> tab /\ P t) (removeTable tab ts).
    clear; induction 1; simpl; intuition; ift.
  Qed.

  Hint Immediate Forall_removeTable'.
  
  Lemma unusedTable : forall tab suff, underscore_free tab
    -> forall xm avs ts,
      xwf avs ts xm
      -> NoDups avs ts
      -> List.Forall (fun t => Name t <> tab /\ underscore_free (Name t))%type ts
      -> In (tab ++ String "_" suff)%string (allCursors_both' xm)
      -> False.
    clear; induction xm using xml_ind'; simpl; intuition.
    assert (~In (tab ++ String "_" suff)%string nil) by (simpl; tauto).
    generalize dependent (@nil string); induction H0; simpl in *; intuition.
    eapply H6.
    eauto.
    intros.
    apply In_addTo_or in H10; intuition eauto.

    eapply append_underscore_free in H4; eauto.
    subst.
    destruct H0; intuition.
    eapply Forall_forall in H2; [ | eassumption ]; tauto.
    destruct H0; intuition.
    eapply Forall_forall in H2; [ | eassumption ]; intuition congruence.

    eapply append_underscore_free in H3; eauto.
    subst.
    destruct H0; intuition.
    eapply Forall_forall in H2; [ | eassumption ]; tauto.
    destruct H0; intuition.
    eapply Forall_forall in H2; [ | eassumption ]; intuition congruence.

    destruct H0; intuition eauto.
  Qed.

  Lemma allCursors'_both_NoDup : forall xm avs ts,
    xwf avs ts xm
    -> NoDups avs ts
    -> List.Forall (fun t => underscore_free (Name t)) ts
    -> NoDup (allCursors_both' xm).
    clear; induction xm using xml_ind'; simpl; intuition.
    generalize (NoDup_nil string); generalize dependent (@nil string);
      induction H; simpl in *; intuition.
    destruct H; intuition.

    constructor.
    simpl; intuition.
    apply append_inj in H6; discriminate.
    eapply unusedTable; eauto.
    eapply Forall_forall in H1; [ | eassumption ]; eauto.

    constructor.
    simpl; intuition.
    eapply unusedTable; eauto.
    eapply Forall_forall in H1; [ | eassumption ]; eauto.

    eauto.
  Qed.

  Hint Immediate allCursors'_both_NoDup.

  Lemma allCursors_both_NoDup : forall a avs ts,
    awf avs ts a
    -> NoDups avs ts
    -> List.Forall (fun t => underscore_free (Name t)) ts
    -> NoDup (allCursors_both a).
    clear; induction a; simpl; intuition eauto using NoDup_addTo.
    repeat constructor; simpl; intuition.
    apply append_inj in H3; discriminate.
  Qed.

  Hint Immediate allCursors_both_NoDup.

  Lemma cursorsOf_NoDup : forall ts p,
    wf ts p
    -> NoDup (Names ts)
    -> List.Forall (fun t => underscore_free (Name t)) ts
    -> NoDup (cursorsOf p).
    induction p; simpl; intuition eauto.
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

  Definition avout := map (fun av => {| Table := av; Row := Name av ++ "_row";
    Data := Name av ++ "_data" |}).

  Definition cursors V avs := cursors V (avout avs).

  Lemma cursors_sel : forall V avs, cursors (sel V) avs = cursors V avs.
    auto.
  Qed.

  Ltac prep :=
    post;
    try match goal with
          | [ st : (settings * state)%type |- _ ] => destruct st; simpl in *
        end;
    repeat match goal with
             | [ H : context[cursors (sel ?V) ?x] |- _ ] => rewrite (cursors_sel V x) in H
             | [ |- context[cursors (sel ?V) ?x] ] => rewrite (cursors_sel V x)
             | [ H : context[XmlOutput.cursors (sel ?V) ?x] |- _ ] => rewrite (XmlOutput.cursors_sel V x) in H
             | [ |- context[XmlOutput.cursors (sel ?V) ?x] ] => rewrite (XmlOutput.cursors_sel V x)
           end;
    fold (@length string) in *; varer 52 "stack"; varer 8 "len"; varer 24 "lex"; varer 32 "opos";
      varer 36 "overflowed";
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
          end; try rewrite inBounds_sel in *; try rewrite inputOk_sel in *;
      unfold lvalIn, regInL, immInR in *; prep_locals.
  
  Ltac my_descend :=
    repeat match goal with
             | [ H : @In string _ _ |- _ ] => clear H
           end;
    try match goal with
          | [ st : (settings * state)%type |- _ ] => destruct st; simpl in *
        end;
    descend; reger; try rewrite inBounds_sel in *; try rewrite inputOk_sel in *;
      repeat match goal with
               | [ H : context[cursors (sel ?V) ?x] |- _ ] => rewrite (cursors_sel V x) in H
               | [ |- context[cursors (sel ?V) ?x] ] => rewrite (cursors_sel V x)
               | [ H : context[XmlOutput.cursors (sel ?V) ?x] |- _ ] => rewrite (XmlOutput.cursors_sel V x) in H
               | [ |- context[XmlOutput.cursors (sel ?V) ?x] ] => rewrite (XmlOutput.cursors_sel V x)
             end.

  Ltac clear_fancier :=
    repeat match goal with
             | [ H : importsGlobal _ |- _ ] => clear dependent H
           end;
    repeat match goal with
             | [ H : LabelMap.find _ _ = _ |- _ ] => clear H
           end.

  Ltac my_evaluate := clear_fancier; evaluate SinglyLinkedList.hints.
  Ltac my_step := step SinglyLinkedList.hints.

  Ltac invoke1 :=
    match goal with
      | [ H : interp _ _, H' : _ |- _ ] => apply H' in H; clear H'
      | [ H : LabelMap.find _ _ = Some _ |- _ ] => rewrite H; post
    end.

  Ltac post := PreAutoSep.post;
    try match goal with
          | [ H : context[findTable] |- _ ] =>
            PreAutoSep.post; erewrite findTable_good in H by eauto; PreAutoSep.post
        end.

  Ltac t' := post; repeat invoke1; prep; my_evaluate; my_descend; repeat (my_step; my_descend); eauto.

  Lemma freeVar_compile' : forall x p,
    freeVar p x
    -> In (x ++ "_start", x ++ "_len")%string (XmlSearch.allCdatas (compilePat p)).
    induction p; simpl; intuition.
  Qed.

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

  Ltac easy :=
    try match goal with
          | [ H : XmlOutput.freeVar _ _, H' : forall start len : string, _ |- _ ] =>
            apply H' in H; post; subst
        end;
    solve [ hnf; simpl in *; intuition (subst; try congruence;
      eauto using freeVar_compile', freeVar_start, freeVar_len) ].

  Ltac pre :=
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
    -> XmlSearch.inBounds (XmlSearch.allCdatas (compilePat p)) V
    -> XmlSearch.inBounds (XmlSearch.allCdatas (compilePat p)) V'.
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

  Lemma underscore_discrim : forall s1 s2,
    s1 = s2
    -> ~underscore_free s1
    -> underscore_free s2
    -> False.
    intros; congruence.
  Qed.

  Lemma underscore_free_app_contra : forall s1 s2,
    underscore_free (s1 ++ String "_" s2)
    -> False.
    clear; induction s1; simpl; intuition eauto.
  Qed.

  Lemma underscore_mid_discrim : forall s2 s2',
    underscore_free s2
    -> underscore_free s2'
    -> forall s1 s1', (s1 ++ String "_" s2)%string = (s1' ++ String "_" s2')%string
      -> s2 = s2'.
    clear; induction s1; destruct s1'; simpl; intuition;
      injection H1; clear H1; intros; subst; simpl in *; eauto;
        exfalso; eauto using underscore_free_app_contra.
  Qed.

  Ltac und := congruence
    || (intro Ho; apply underscore_mid_discrim in Ho; auto; discriminate)
    || (intro; eapply underscore_discrim; try eassumption; solve [ eauto ])
    || (intro; eapply underscore_discrim; try (symmetry; eassumption); eauto).

  Ltac prove_irrel := clear_fancier;
    repeat match goal with
             | [ V : vals |- _ ] =>
               match goal with
                 | [ |- context[V ?x] ] => change (V x) with (sel V x)
               end
           end;
    match goal with
      | [ H : forall x : string, _ |- _ ] =>
        match type of H with
          | context[sel] =>
            repeat rewrite H by und
        end
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

  Hint Extern 1 (_ <= _)%nat =>
    match goal with
      | [ H : inBounds _ _ |- _ ] => eapply Forall_forall in H; [ | eauto using freeVar_compile' ]
    end.

  Hint Extern 1 (NoDup (_ :: _)) => repeat constructor; simpl; intuition injy.


  Opaque mult.

  Hint Constructors unit.
  Hint Immediate freeVar_compile'.

  Lemma Forall_map : forall A B (f : A -> B) (P : B -> Prop) ls,
    List.Forall (fun x => P (f x)) ls
    -> List.Forall P (map f ls).
    induction 1; simpl; auto.
  Qed.

  Fixpoint cdatasOf' (pr : program) : list string :=
    match pr with
      | Rule p _ => allCdatas p
      | PSeq pr1 pr2 => addTo (cdatasOf' pr1) (cdatasOf' pr2)
    end.

  Definition cdataify := map (fun s => (s ++ "_start", s ++ "_len"))%string.

  Lemma dontTouch_cdataify : forall tab cds,
    dontTouch (tab ++ "_row") (tab ++ "_data") (cdataify cds).
    clear; induction cds; simpl; intuition;
      apply underscore_mid_discrim in H; intuition.
  Qed.

  Hint Immediate dontTouch_cdataify.

  Lemma NoDups_dontReuse : forall x ts avs,
    NoDups avs ts
    -> In x ts
    -> dontReuse (Name x ++ "_row") (Name x ++ "_data") (avout avs).
    clear; induction avs; simpl; intuition.

    apply append_inj' in H1.
    hnf in H; simpl in H.
    inversion_clear H.
    apply H2.
    rewrite H1.
    eapply in_or_app; right.
    apply in_map; auto.

    apply underscore_mid_discrim in H1; simpl; intuition.
    apply underscore_mid_discrim in H1; simpl; intuition.

    apply append_inj' in H1.
    hnf in H; simpl in H.
    inversion_clear H.
    apply H2.
    rewrite H1.
    eapply in_or_app; right.
    apply in_map; auto.

    inversion_clear H.
    eauto.
  Qed.

  Hint Immediate NoDups_dontReuse.

  Lemma wfExp_compileExp : forall ns e,
    ewf e
    -> (forall text, efreeVar e text
      -> In (text ++ "_start")%string ns)
    -> (forall text, efreeVar e text
      -> In (text ++ "_len")%string ns)
    -> wfExp ns (compileExp e).
    destruct e; simpl; intuition eauto 4 using underscore_discrim.
  Qed.

  Hint Resolve wfExp_compileExp.

  Lemma allCdatas_start : forall x p,
    In x (allCdatas p)
    -> In (x ++ "_start")%string (allCdatas_both p).
    induction p; simpl; intuition;
      apply in_app_or in H; intuition.
  Qed.

  Hint Immediate allCdatas_start.

  Lemma In_addTo2 : forall x ls1 ls2,
    In x ls2
    -> In x (addTo ls1 ls2).
    induction ls1; simpl; intuition.
    destruct (member a ls2).
    eauto.
    apply IHls1.
    simpl; tauto.
  Qed.

  Lemma In_addTo1 : forall x ls1 ls2,
    In x ls1
    -> In x (addTo ls1 ls2).
    induction ls1; simpl; intuition.
    generalize (member_means a ls2); destruct (member a ls2); intuition.
    subst; eauto using In_addTo2.
    subst; apply In_addTo2; simpl; tauto.
  Qed.

  Hint Immediate In_addTo1 In_addTo2.

  Lemma cdatasOf'_start : forall x p,
    In x (cdatasOf' p)
    -> In (x ++ "_start")%string (cdatasOf p).
    induction p; simpl; eauto.
    intros.
    apply In_addTo_or in H; intuition.
  Qed.

  Hint Resolve cdatasOf'_start in_or_app.

  Lemma allCdatas_len : forall x p,
    In x (allCdatas p)
    -> In (x ++ "_len")%string (allCdatas_both p).
    induction p; simpl; intuition;
      apply in_app_or in H; intuition.
  Qed.

  Hint Immediate allCdatas_len.

  Lemma cdatasOf'_len : forall x p,
    In x (cdatasOf' p)
    -> In (x ++ "_len")%string (cdatasOf p).
    induction p; simpl; eauto.
    intros.
    apply In_addTo_or in H; intuition.
  Qed.

  Hint Resolve cdatasOf'_len.

  Lemma In_cdataify : forall text cds,
    In text cds
    -> In ((text ++ "_start")%string, (text ++ "_len")%string) (cdataify cds).
    clear; induction cds; simpl; intuition.
  Qed.

  Hint Resolve In_cdataify.

  Lemma exp_wf : forall ns cds e,
    ewf e
    -> (forall x, efreeVar e x -> In (x ++ "_start")%string ns)
    -> (forall x, efreeVar e x -> In (x ++ "_len")%string ns)
    -> (forall x, efreeVar e x -> In (x ++ "_start", x ++ "_len")%string cds)
    -> XmlOutput.ewf ns cds (compileExp e).
    clear; destruct e; simpl; intuition (eauto 4 using underscore_discrim; eauto).
  Qed.

  Lemma eq_wf : forall ns sch cds x,
    eqwf sch x
    -> (forall y, efreeVar (snd x) y -> In (y ++ "_start")%string ns)
    -> (forall y, efreeVar (snd x) y -> In (y ++ "_len")%string ns)
    -> (forall y, efreeVar (snd x) y -> In (y ++ "_start", y ++ "_len")%string cds)
    -> XmlOutput.eqwf ns sch cds (compileEquality x).
    intros; hnf in *; intuition; apply exp_wf; auto.
  Qed.

  Hint Resolve eq_wf.

  Lemma cond_wf : forall ns cds sch cond,
    cwf sch cond
    -> (forall x, List.Exists (fun e => efreeVar (snd e) x) cond -> In (x ++ "_start")%string ns)
    -> (forall x, List.Exists (fun e => efreeVar (snd e) x) cond -> In (x ++ "_len")%string ns)
    -> (forall x, List.Exists (fun e => efreeVar (snd e) x) cond
      -> In (x ++ "_start", x ++ "_len")%string cds)
    -> XmlOutput.cwf ns sch cds (compileCondition cond).
    clear; unfold cwf, XmlOutput.cwf; induction 1; simpl; intuition.
  Qed.

  Hint Resolve cond_wf.

  Lemma In_removeTable' : forall x y ts,
    In x (removeTable y ts)
    -> In x ts.
    clear; induction ts; simpl; intuition.
    destruct (string_dec y (Name a)); subst; simpl in *; intuition.
  Qed.

  Hint Immediate In_removeTable'.

  Fixpoint abindsRowVar (a : action) (x : string) : Prop :=
    match a with
      | Insert _ _ => False
      | Delete tab _ => x = tab
      | Output xm => xbindsRowVar xm x
      | Seq a1 a2 => abindsRowVar a1 x \/ abindsRowVar a2 x
    end.

  Fixpoint bindsRowVar (pr : program) (x : string) : Prop :=
    match pr with
      | Rule _ a => abindsRowVar a x
      | PSeq pr1 pr2 => bindsRowVar pr1 x \/ bindsRowVar pr2 x
    end.

  Lemma output_wf : forall ns cds xm avs ts,
    xwf avs ts xm
    -> NoDups avs ts
    -> (forall x, xfreeVar xm x -> In (x ++ "_start")%string ns)
    -> (forall x, xfreeVar xm x -> In (x ++ "_len")%string ns)
    -> (forall t, In t avs -> In (Name t ++ "_data")%string ns)
    -> (forall tab, xbindsRowVar xm tab -> In (tab ++ "_data")%string ns)
    -> (forall x, xfreeVar xm x -> In (x ++ "_start", x ++ "_len")%string (cdataify cds))
    -> XmlOutput.wf ns (cdataify cds) (avout avs) ts (compileXml xm).
    induction xm using xml_ind'; simpl; intuition idtac;
      try match goal with
            | [ H : _ |- _ ] => apply append_inj in H; discriminate
          end; eauto 4 using underscore_discrim.

    induction H; simpl in *; intuition.

    destruct H; intuition subst.
    do 2 esplit.
    eapply in_map in H6; eauto.
    simpl; intuition eauto using in_or_app.

    destruct H; intuition (subst; eauto).

    destruct H; intuition subst.
    descend; eauto 8.
    eapply IHxm in H9; eauto;
      (simpl; intuition (subst; eauto)).
  Qed.

  Hint Immediate output_wf.


  (** ** Action compilation *)

  Variable bufSize : W.

  Hypothesis buf_size_lower : bufSize >= natToW 2.
  Hypothesis buf_size_upper : goodSize (4 * wordToNat bufSize).

  Section compileAction.
    Variable p : pat.

    Infix ";;" := SimpleSeq : SP_scope.

    Fixpoint compileAction' (avs ts ts' : tables) (a : action) : chunk :=
      match a with
        | Insert tab es =>
          match findTable tab ts with
            | None => Fail
            | Some t => RelDbInsert.Insert
              (fun bsO V => cursors V avs * db (removeTable tab ts) * array8 bsO (V "obuf")
                * [| length bsO = wordToNat (V "olen") |]
                * [| V "opos" <= V "olen" |]%word
                * [| XmlOutput.inBounds (XmlSearch.allCdatas (compilePat p)) V |]
                * xmlp (V "len") (V "lex")
                * Ex ls, sll ls (V "stack") * [| stackOk ls (V "len") |])%Sep
              (fun bsO V R => db ts'
                * [| R <= V "olen" |]%word * mallocHeap 0
                * Ex bsO', array8 bsO' (V "obuf")
                * [| length bsO' = length bsO |])%Sep
              (Address t) (Schema t) bufSize (compileExps es)
          end
        | Delete tab cond =>
          match findTable tab ts with
            | None => Fail
            | Some t => RelDbDelete.Delete
              (fun bsO V => cursors V avs * db (removeTable tab ts) * array8 bsO (V "obuf")
                * [| length bsO = wordToNat (V "olen") |]
                * [| V "opos" <= V "olen" |]%word
                * [| XmlOutput.inBounds (XmlSearch.allCdatas (compilePat p)) V |]
                * xmlp (V "len") (V "lex")
                * Ex ls, sll ls (V "stack") * [| stackOk ls (V "len") |])%Sep
              (fun bsO V R => db ts'
                * [| R <= V "olen" |]%word * mallocHeap 0
                * Ex bsO', array8 bsO' (V "obuf")
                * [| length bsO' = length bsO |])%Sep
              (Address t) (Schema t) (tab ++ "_row") (tab ++ "_data") (compileCondition cond)
          end
        | Output xm => 
          Out
          (fun (_ : unit) V => mallocHeap 0 * xmlp (V "len") (V "lex")
            * Ex ls, sll ls (V "stack") * [| stackOk ls (V "len") |])%Sep
          (fun _ V R => db ts'
            * [| R <= V "olen" |]%word * mallocHeap 0)%Sep
          (XmlSearch.allCdatas (compilePat p))
          (avout avs) ts
          (compileXml xm)
        | Seq a1 a2 =>
          compileAction' avs ts ts' a1;;
          compileAction' avs ts ts' a2
      end%SP.

    Definition ainv avs ts ts' :=
      XmlSearch.inv (fun bsO V => cursors V avs * db ts
        * array8 bsO (V "obuf")
        * [| length bsO = wordToNat (V "olen") |]
        * [| V "opos" <= V "olen" |]%word)%Sep
      (fun bsO V R => db ts'
        * Ex bsO', array8 bsO' (V "obuf")
        * [| length bsO' = length bsO |]
        * [| R <= V "olen" |]%word)%Sep
      (XmlSearch.allCdatas (compilePat p)).

    Lemma removeTable_bwd' : forall x ts P,
      NoDup (Names ts)
      -> In x ts
      -> RelDb.table (Schema x) (Address x) * (db (removeTable (Name x) ts) * P)
      ===> P * db ts.
      sepLemma; etransitivity; [ | apply removeTable_bwd ]; eauto; sepLemma.
    Qed.

    Lemma removeTable_fwd' : forall x ts P,
      NoDup (Names ts)
      -> In x ts
      -> db ts * P
      ===> P * (RelDb.table (Schema x) (Address x) * db (removeTable (Name x) ts)).
      sepLemma; etransitivity; [ apply removeTable_fwd | ]; eauto; sepLemma.
    Qed.

    Ltac cap := abstract (t;
      ((apply removeTable_bwd' || apply removeTable_fwd'); eauto)
      || apply himp_star_comm
      || (etransitivity; [ | apply himp_star_frame; [ | apply removeTable_bwd ] ]; assumption || my_step)
      || (etransitivity; [ apply himp_star_frame; [ apply removeTable_fwd | ] | ]; eassumption || my_step)
      || my_step).

    Lemma compileAction_post : forall im mn (H : importsGlobal im) ns res a avs ts ts' pre,
      (forall specs st,
        interp specs (pre st)
        -> interp specs (ainv avs ts ts' true (fun x : W => x) ns res st))
      -> awf avs ts a
      -> NoDups avs ts
      -> forall specs st, interp specs (Postcondition (toCmd
        (compileAction' avs ts ts' a) mn H ns res pre) st)
        -> interp specs (ainv avs ts ts' true (fun x : W => x) ns res st).
    Admitted.
      (*induction a.

      cap.
      cap.
      cap.
      cap.
    Qed.*)

    Lemma Exists_map : forall A B (f : A -> B) (P : B -> Prop) ls,
      List.Exists P (map f ls)
      -> List.Exists (fun x => P (f x)) ls.
      induction ls; inversion 1; subst; auto.
    Qed.

    Lemma Forall_Exists : forall A (P Q : A -> Prop) ls,
      List.Forall P ls
      -> List.Exists Q ls
      -> exists x, P x /\ Q x /\ In x ls.
      induction 1; inversion 1; subst; simpl; intuition eauto;
        match goal with
          | [ H : Logic.ex _ |- _ ] => destruct H; intuition eauto
        end.
    Qed.

    Lemma In_ExistsR : forall A (P : A -> Prop) x ls,
      In x ls
      -> P x
      -> ExistsR P ls.
      induction ls; simpl; intuition.
    Qed.

    Hint Immediate In_ExistsR.

    Lemma compile_efreeVar' : forall e text,
      XmlOutput.efreeVar (compileExp e) (text ++ "_start", text ++ "_len")%string
      -> efreeVar e text.
      clear; destruct e; simpl; intuition.
      injection H; clear H; intros.
      apply append_inj' in H; tauto.
    Qed.

    Lemma compile_efreeVar : forall e start len,
      XmlOutput.efreeVar (compileExp e) (start, len)
      -> exists text, efreeVar e text /\ start = (text ++ "_start")%string
        /\ len = (text ++ "_len")%string.
      clear; destruct e; simpl; intuition.
      injection H; eauto.
    Qed.

    Lemma Exists_impl : forall A (P P' : A -> Prop) ls,
      List.Exists P ls
      -> (forall x, P x -> P' x)
      -> List.Exists P' ls.
      induction 1; simpl; intuition.
    Qed.

    Lemma Exists_exists : forall A B (P : A -> B -> Prop) ls,
      List.Exists (fun x => exists y, P x y) ls
      -> exists y, List.Exists (fun x => P x y) ls.
      clear; induction 1; simp; eauto.
    Qed.

    Lemma Exists_conj2 : forall A (P : A -> Prop) Q R ls,
      List.Exists (fun x => P x /\ Q /\ R) ls
      -> List.Exists P ls /\ Q /\ R.
      clear; induction 1; simp; eauto.
    Qed.

    Lemma compileXml_freeVar : forall start len xm,
      XmlOutput.freeVar (compileXml xm) (start, len)
      -> exists text, xfreeVar xm text
        /\ start = (text ++ "_start")%string
        /\ len = (text ++ "_len")%string.
      induction xm using xml_ind'; simpl; intuition;
        try match goal with
              | [ H : (_, _) = (_, _) |- _ ] => injection H; clear H; intros; subst
            end; eauto.

      apply ExistsR_Exists in H0; apply Exists_map in H0.
      eapply Forall_Exists in H; eauto.
      destruct H; intuition; match goal with
                               | [ H : Logic.ex _ |- _ ] => destruct H; intuition eauto
                             end.

      unfold compileCondition in H0.
      eapply Exists_map in H0.
      eapply (@Exists_impl _ _ (fun x => exists text, efreeVar (snd x) text
        /\ start = (text ++ "_start")%string /\ len = (text ++ "_len")%string)) in H0; [
          | auto using compile_efreeVar ].
      apply Exists_exists in H0; destruct H0.
      apply Exists_conj2 in H; intuition eauto.

      post; eauto.
    Qed.

    Lemma compilePat_cdatas : forall p0,
      cdatasGood (XmlSearch.allCdatas (compilePat p0)).
      unfold cdatasGood; induction p0; simpl; intuition.
      constructor; auto; simpl; intuition (eapply underscore_discrim; eauto).
    Qed.

    Hint Immediate compilePat_cdatas.

    Lemma inputOk_compileExps : forall V cdatas es,
      XmlOutput.inBounds cdatas V
      -> (forall text, List.Exists (fun e => efreeVar e text) es
        -> In (text ++ "_start", text ++ "_len")%string cdatas)
      -> inputOk V (compileExps es).
      unfold inputOk, XmlOutput.inBounds; induction es; simpl; intuition.
      constructor; auto.
      destruct a; simpl; auto.
      specialize (H0 text); match type of H0 with
                              | ?P -> _ => assert P by (constructor; reflexivity)
                            end; intuition.
      eapply Forall_forall in H; try eassumption; assumption.
    Qed.

    Hint Immediate inputOk_compileExps.

    Lemma inBounds_swizzle' : forall V V' p,
      (forall x, x <> "ibuf" -> x <> "row"
        -> x <> "ilen" -> x <> "tmp" -> x <> "ipos" -> x <> "overflowed" -> sel V x = sel V' x)
      -> XmlOutput.inBounds (XmlSearch.allCdatas (compilePat p)) V
      -> XmlOutput.inBounds (XmlSearch.allCdatas (compilePat p)) V'.
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

    Hint Immediate inBounds_swizzle'.

    Lemma goodSize_more : forall t ts,
      twfs ts
      -> In t ts
      -> goodSize (S (S (length (Schema t) + length (Schema t)))).
      intros; eapply Forall_forall in H; eauto; eassumption.
    Qed.

    Hint Immediate goodSize_more.

    Lemma underscore_discrim' : forall s1 s2,
      s1 = s2
      -> underscore_free s1
      -> ~underscore_free s2
      -> False.
      intros; congruence.
    Qed.

    Lemma wfExps_compileExps : forall ns es,
      ewfs es
      -> (forall text, List.Exists (fun e => efreeVar e text) es
        -> In (text ++ "_start")%string ns)
      -> (forall text, List.Exists (fun e => efreeVar e text) es
        -> In (text ++ "_len")%string ns)
      -> wfExps ns (compileExps es).
      unfold wfExps; induction 1; simpl; intuition.
    Qed.

    Hint Immediate wfExps_compileExps.

    Lemma length_compileExps : forall es, length (compileExps es) = length es.
      intros; apply map_length.
    Qed.

    Hint Rewrite length_compileExps : sepFormula.

    Lemma goodSize_base : forall ts t,
      twfs ts
      -> In t ts
      -> goodSize (length (Schema t)).
      intros; eapply goodSize_weaken; [ eapply goodSize_more | ]; eauto.
    Qed.

    Hint Immediate goodSize_base.

    Notation baseVars := ("buf" :: "len" :: "lex" :: "res"
      :: "tagStart" :: "tagLen" :: "matched" :: "stack" :: "level" :: nil).

    Notation "l ~~ im ~~> s" := (LabelMap.find l%SP im = Some (Precondition s None)) (at level 0).

    Lemma inputOk_compileCondition : forall V cdatas cond,
      XmlOutput.inBounds cdatas V
      -> (forall text, List.Exists (fun e => efreeVar (snd e) text) cond
        -> In (text ++ "_start", text ++ "_len")%string cdatas)
      -> inputOk V (exps (compileCondition cond)).
      unfold inputOk, XmlOutput.inBounds; induction cond; simpl; intuition.
      constructor; auto.
      destruct a; simpl in *.
      destruct e; simpl; auto.
      specialize (H0 text); match type of H0 with
                              | ?P -> _ => assert P by (constructor; reflexivity)
                            end; intuition.
      eapply Forall_forall in H; try eassumption; assumption.
    Qed.

    Hint Resolve inputOk_compileCondition.

    Lemma inBounds_swizzle'' : forall V V' p,
      (forall x, x <> "row"
        -> x <> "ibuf" -> x <> "ilen" -> x <> "tmp"
        -> x <> "ipos" -> x <> "overflowed" -> x <> "matched"
        -> sel V x = sel V' x)
      -> XmlOutput.inBounds (XmlSearch.allCdatas (compilePat p)) V
      -> XmlOutput.inBounds (XmlSearch.allCdatas (compilePat p)) V'.
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

    Hint Immediate inBounds_swizzle''.

    Lemma wfEqualities_compileCondition : forall ns sch cond,
      cwf sch cond
      -> (forall text,
        List.Exists (fun e => efreeVar (snd e) text) cond ->
        In (text ++ "_start")%string ns)
      -> (forall text,
        List.Exists (fun e => efreeVar (snd e) text) cond ->
        In (text ++ "_len")%string ns)
      -> wfEqualities ns sch (compileCondition cond).
      unfold wfEqualities; induction 1; simpl; auto.
      constructor; auto.
      hnf; simpl.
      hnf in H.
      intuition eauto 6.
    Qed.

    Hint Resolve wfEqualities_compileCondition.

    Ltac step1 := wrap0;
      try match goal with
            | [ |- context[findTable] ] => post; post; erewrite findTable_good by eauto; wrap0
          end;
      try match goal with
            | [ |- vcs (_ :: _) ] => wrap0
          end.

    Ltac discrim :=
      match goal with
        | _ => eapply underscore_discrim; solve [ eauto ]
        | _ => eapply underscore_discrim; try symmetry; solve [ eauto ]
        | [ H : _ |- _ ] => apply append_inj in H; discriminate
        | [ H : _ |- _ ] => apply underscore_mid_discrim in H; try discriminate; solve [ eauto ]
      end.

    Lemma compileXml_bindsRowVar : forall rw data xm,
      XmlOutput.bindsRowVar (compileXml xm) (rw, data)
      -> exists tab, xbindsRowVar xm tab
        /\ rw = (tab ++ "_row")%string
        /\ data = (tab ++ "_data")%string.
      induction xm using xml_ind'; simpl; intuition;
        try match goal with
              | [ H : (_, _) = (_, _) |- _ ] => injection H; clear H; intros; subst
            end; eauto.

      apply ExistsR_Exists in H0; apply Exists_map in H0.
      eapply Forall_Exists in H; eauto.
      destruct H; intuition; match goal with
                               | [ H : Logic.ex _ |- _ ] => destruct H; intuition eauto
                             end.

      post; eauto.
    Qed.

    Ltac step2 :=
      match goal with
        | [ |- False ] => discrim
        | _ => solve [ subst; eauto ]
        | [ H : _ |- _ ] =>
          apply compileXml_freeVar in H; post; subst; solve [
            eauto | eapply proj1; eauto | eapply proj2; eauto ]
        | [ H : _ |- _ ] =>
          apply compileXml_freeVar in H; post; subst; solve [ eauto ]
        | [ H : _ |- _ ] =>
          apply compileXml_bindsRowVar in H; post; subst; solve [ eauto ]
        | _ => cap
        | _ => repeat (post; intuition idtac;
          match goal with
            | [ H : _ |- _ ] => apply H; auto
          end; try (apply compileAction_post; auto))
      end.

    Ltac cav := abstract (step1; step2).

    Lemma inBounds_swizzle''' : forall V V' p,
      (forall x, x <> "ibuf" -> x <> "ilen" -> x <> "tmp"
        -> x <> "ipos" -> x <> "overflowed" -> x <> "matched"
        -> x <> "res" -> sel V x = sel V' x)
      -> XmlOutput.inBounds (XmlSearch.allCdatas (compilePat p)) V
      -> XmlOutput.inBounds (XmlSearch.allCdatas (compilePat p)) V'.
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

    Hint Immediate inBounds_swizzle'''.

    Lemma Weaken_cursors : forall V V',
      (forall x, x <> "ibuf" -> x <> "row" -> x <> "ilen"
        -> x <> "tmp" -> x <> "ipos" -> x <> "overflowed"
        -> x <> "opos" -> x <> "matched" -> x <> "res"
        -> sel V x = sel V' x)
      -> forall avs, cursors V avs ===> cursors V' avs.
      unfold cursors; clear; induction avs; simpl; intuition.
      sepLemma.
      apply Himp_star_frame; auto.
      unfold cvars in *; simpl in *; intuition idtac;
        unfold cursor; apply Himp_star_frame;
          repeat match goal with
                   | [ V : vals |- _ ] =>
                     progress repeat match goal with
                                       | [ |- context[V ?x] ] => change (V x) with (sel V x)
                                     end
                 end;
          try match goal with
                | [ H : forall x : string, _ |- _ ] => repeat rewrite H
                  by eauto 4 using underscore_discrim
              end; apply Himp_refl.
    Qed.

    Hint Extern 1 (himp _ (cursors _ _) (cursors _ _)) => apply Weaken_cursors.

    Lemma xall_underscore' : forall p,
      List.Forall (fun p => exists tab, p = (tab ++ "_start", tab ++ "_len")%string)
      (XmlSearch.allCdatas (compilePat p)).
      clear; induction p; simpl; intuition eauto.
    Qed.

    Lemma inBounds_swizzle'''' : forall V V' p tab,
      (forall x, x <> (tab ++ "_row")%string -> x <> (tab ++ "_data")%string
        -> x <> "ibuf" -> x <> "ilen" -> x <> "tmp" -> x <> "ipos" -> x <> "overflowed"
        -> x <> "matched" -> x <> "res"
        -> sel V x = sel V' x)
      -> XmlOutput.inBounds (XmlSearch.allCdatas (compilePat p)) V
      -> XmlOutput.inBounds (XmlSearch.allCdatas (compilePat p)) V'.
      intros.
      rewrite <- inBounds_sel.
      rewrite <- inBounds_sel in H0.
      eapply Forall_impl2; [ apply H0 | apply xall_underscore' | ].
      post; subst; simpl in *.
      repeat rewrite H in * by und.
      auto.
    Qed.

    Hint Immediate inBounds_swizzle''''.
    
    Lemma Weaken_cursors_eauto : forall V V' t,
      (forall x, x <> (Name t ++ "_row")%string
        -> x <> (Name t ++ "_data")%string
        -> x <> "ibuf" -> x <> "ilen"
        -> x <> "tmp" -> x <> "ipos" -> x <> "overflowed"
        -> x <> "matched" -> x <> "res"
        -> sel V x = sel V' x)
      -> forall ts avs, NoDups avs ts
        -> In t ts
        -> cursors V avs ===> cursors V' avs.
      unfold cursors; clear; induction avs; simpl; intuition.
      sepLemma.

      inversion_clear H0.
      assert ((Name a ++ "_data")%string <> (Name t ++ "_data")%string).
      intro.
      apply append_inj' in H0.
      apply H2.
      rewrite H0.
      apply in_or_app; right.
      apply in_map; auto.

      assert ((Name a ++ "_row")%string <> (Name t ++ "_row")%string).
      intro.
      apply append_inj' in H4.
      apply H2.
      rewrite H4.
      apply in_or_app; right.
      apply in_map; auto.

      apply Himp_star_frame; auto.
      unfold cvars in *; simpl in *; intuition idtac;
        unfold cursor; apply Himp_star_frame; simpl;
          repeat match goal with
                   | [ V : vals |- _ ] =>
                     progress repeat match goal with
                                       | [ |- context[V ?x] ] => change (V x) with (sel V x)
                                     end
                 end;
          try match goal with
                | [ H : forall x : string, _ |- _ ] => repeat rewrite H by und
              end; apply Himp_refl.
    Qed.

    Hint Extern 1 (himp _ (cursors _ _) (cursors _ _)) => eapply Weaken_cursors_eauto.

    Hint Extern 1 (incl (_ :: _) _) => hnf; simpl; intuition subst;
      match goal with
        | [ H : _ |- _ ] => apply H
      end.

    Lemma noOverlapExps_compileCondition : forall tab cond,
      noOverlapExps (tab ++ "_row") (tab ++ "_data")
      (exps (compileCondition cond)).
      unfold noOverlapExps, noOverlapExp; induction cond; simpl; intuition.
      constructor; auto.
      destruct (snd a); simpl; auto.
      intuition discrim.
    Qed.

    Hint Immediate noOverlapExps_compileCondition.

    Lemma cdataify_app : forall ls1 ls2,
      cdataify (ls1 ++ ls2) = cdataify ls1 ++ cdataify ls2.
      induction ls1; simpl; intuition.
    Qed.

    Lemma cdataify_pat : forall p,
      XmlSearch.allCdatas (compilePat p) = cdataify (allCdatas p).
      clear; induction p; simpl; intuition;
        rewrite cdataify_app; congruence.
    Qed.        

    Lemma allCdatas_cdataify : forall x p,
      In x (XmlSearch.allCdatas (compilePat p))
      -> In x (cdataify (allCdatas p)).
      clear; induction p; simpl; intuition; rewrite cdataify_app;
        apply in_app_or in H; intuition.
    Qed.

    Hint Resolve allCdatas_cdataify.

    Lemma output_wf' : forall ns p xm avs ts,
      xwf avs ts xm
      -> NoDups avs ts
      -> (forall x, xfreeVar xm x -> In (x ++ "_start")%string ns)
      -> (forall x, xfreeVar xm x -> In (x ++ "_len")%string ns)
      -> (forall t, In t avs -> In (Name t ++ "_data")%string ns)
      -> (forall tab, xbindsRowVar xm tab -> In (tab ++ "_data")%string ns)
      -> (forall x, xfreeVar xm x -> In (x ++ "_start", x ++ "_len")%string
        (XmlSearch.allCdatas (compilePat p)))
      -> XmlOutput.wf ns (XmlSearch.allCdatas (compilePat p)) (avout avs) ts (compileXml xm).
      intros; rewrite cdataify_pat; eauto using output_wf.
    Qed.

    Hint Resolve output_wf'.

    Lemma goodCursors_avout : forall avs,
      twfs avs
      -> goodCursors (avout avs).
      unfold goodCursors; clear; induction 1; simpl; intuition.
      constructor; simpl; auto.
      intuition (try discrim; eauto).
    Qed.

    Hint Immediate goodCursors_avout.

    Lemma map_avout : forall avs,
      map (fun av => Name (Table av)) (avout avs) = Names avs.
      induction avs; simpl; intuition.
    Qed.

    Lemma NoDups_avout : forall avs ts,
      NoDups avs ts
      -> XmlOutput.NoDups (avout avs) ts.
      intros; hnf in *.
      eapply NoDup_app; try rewrite map_avout; eauto.
      eapply NoDups_unapp_cross; auto.
    Qed.

    Hint Immediate NoDups_avout.

    Lemma compileAction_vcs : forall im mn (H : importsGlobal im) ns res,
      ~In "rp" ns
      -> In "obuf" ns
      -> In "olen" ns
      -> In "opos" ns
      -> In "overflowed" ns
      -> In "tmp" ns
      -> In "buf" ns
      -> In "ibuf" ns
      -> In "row" ns
      -> In "ilen" ns
      -> In "ipos" ns
      -> In "len" ns
      -> In "matched" ns
      -> In "res" ns
      -> incl baseVars ns
      -> (res >= 11)%nat
      -> "array8"!"copy" ~~ im ~~> copyS
      -> "array8"!"equal" ~~ im ~~> equalS
      -> "buffers"!"bmalloc" ~~ im ~~> Buffers.bmallocS
      -> "malloc"!"malloc" ~~ im ~~> mallocS
      -> "numops"!"div4" ~~ im ~~> div4S
      -> "malloc"!"free" ~~ im ~~> freeS
      -> "buffers"!"bfree" ~~ im ~~> bfreeS
      -> forall a avs ts ts' pre,
        (forall specs st,
          interp specs (pre st)
          -> interp specs (ainv avs ts ts' true (fun x : W => x) ns res st))
        -> awf avs ts a
        -> NoDups avs ts
        -> twfs avs
        -> twfs ts
        -> (forall text, afreeVar a text -> In (text ++ "_start", text ++ "_len")%string
          (XmlSearch.allCdatas (compilePat p)))
        -> (forall text, afreeVar a text -> In (text ++ "_start") ns)%string
        -> (forall text, afreeVar a text -> In (text ++ "_len") ns)%string
        -> (forall tab, abindsRowVar a tab -> In (tab ++ "_row") ns)%string
        -> (forall tab, abindsRowVar a tab -> In (tab ++ "_data") ns)%string
        -> (forall t, In t avs -> In (Name t ++ "_row")%string ns)
        -> (forall t, In t avs -> In (Name t ++ "_data")%string ns)
        -> vcs (VerifCond (toCmd (compileAction' avs ts ts' a) mn H ns res pre)).
      induction a.

      step1.

      step2.
      step2.
      step2.
      step2.
      step2.
      step2.

      step1.

      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.
      step2.

      step1.

      step2.
      admit.
      admit.
      step2.
      step2.
      step2.
      step2.
      step2.

      step1.

      step2.
      step2.
    Qed.

    Hint Resolve compileAction_post compileAction_vcs.

    Notation CompileVcs a := (fun im ns res =>
      (~In "rp" ns) :: In "obuf" ns :: In "olen" ns :: In "opos" ns :: In "overflowed" ns
      :: In "tmp" ns :: In "buf" ns :: In "ibuf" ns :: In "row" ns :: In "ilen" ns
      :: In "ipos" ns :: In "len" ns :: In "data" ns :: In "dummy" ns
      :: In "matched" ns :: In "res" ns
      :: incl baseVars ns
      :: (res >= 11)%nat
      :: "array8"!"copy" ~~ im ~~> copyS
      :: "array8"!"equal" ~~ im ~~> equalS
      :: "buffers"!"bmalloc" ~~ im ~~> Buffers.bmallocS
      :: "malloc"!"malloc" ~~ im ~~> mallocS
      :: "numops"!"div4" ~~ im ~~> div4S
      :: "malloc"!"free" ~~ im ~~> freeS
      :: "buffers"!"bfree" ~~ im ~~> bfreeS
      :: awf ts a
      :: (forall text, afreeVar a text -> In (text ++ "_start", text ++ "_len")%string
        (XmlSearch.allCdatas (compilePat p)))
      :: (forall text, afreeVar a text -> (In (text ++ "_start") ns /\ In (text ++ "_len") ns)%string)
      :: nil).

    Definition compileAction (a : action) : chunk.
      refine (WrapC (compileAction' a)
        ainv
        ainv
        (CompileVcs a) _ _); abstract (
          intros; repeat match goal with
                           | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; intros; subst
                         end; eauto).
    Defined.
  End compileAction.

  Section compileProgram.
    Definition cpinv :=
      Al bsI, Al bsO, Al ls,
      PRE[V] db ts * array8 bsI (V "buf") * array8 bsO (V "obuf")
        * [| length bsI = wordToNat (V "len") |]
        * [| length bsO = wordToNat (V "olen") |]
        * row nil (V "dummy") * sll ls (V "stack") * mallocHeap 0
        * xmlp (V "len") (V "lex")
        * [| V "opos" <= V "olen" |] * [| stackOk ls (V "len") |]
      POST[R] db ts * array8 bsI (V "buf") * Ex bsO', array8 bsO' (V "obuf")
        * [| length bsO' = length bsO |]
        * row nil (V "dummy")
        * [| R <= V "olen" |] * mallocHeap 0.

    Infix ";;" := SimpleSeq : SP_scope.    

    Fixpoint compileProgram' (pr : program) : chunk :=
      match pr with
        | Rule p a =>
          Call "xml_lex"!"setPosition"("lex", 0)
          [Al bsI, Al bsO, Al ls,
            PRE[V] db ts * array8 bsI (V "buf") * array8 bsO (V "obuf")
              * [| length bsI = wordToNat (V "len") |]
              * [| length bsO = wordToNat (V "olen") |]
              * row nil (V "dummy") * sll ls (V "stack") * mallocHeap 0
              * xmlp (V "len") (V "lex")
              * [| V "opos" <= V "olen" |]%word * [| stackOk ls (V "len") |]
            POST[R] db ts * array8 bsI (V "buf") * Ex bsO', array8 bsO' (V "obuf")
              * [| length bsO' = length bsO |]
              * row nil (V "dummy")
              * [| R <= V "olen" |]%word * mallocHeap 0];;

          Pat (fun bsO V => db ts * array8 bsO (V "obuf")
            * [| length bsO = wordToNat (V "olen") |]
            * row nil (V "dummy")
            * [| V "opos" <= V "olen" |]%word)%Sep
          (fun bsO V R => db ts * Ex bsO', array8 bsO' (V "obuf")
            * [| length bsO' = length bsO |]
            * row nil (V "dummy")
            * [| R <= V "olen" |]%word)%Sep
          (compilePat p)
          (compileAction p a)
        | PSeq pr1 pr2 =>
          compileProgram' pr1;;
          compileProgram' pr2
      end%SP.

    Lemma compileProgram_post : forall im mn (H : importsGlobal im)
      ns res pr0 pre,
      (forall specs st,
        interp specs (pre st)
        -> interp specs (cpinv true (fun x : W => x) ns res st))
      -> wf ts pr0
      -> forall specs st, interp specs (Postcondition
        (toCmd (compileProgram' pr0) mn H ns res pre) st)
      -> interp specs (cpinv true (fun x : W => x) ns res st).
      induction pr0; simpl; intros; repeat (invoke1; post); t.
    Qed.

    Lemma compileProgram_vcs : forall im mn (H : importsGlobal im) ns res,
      ~In "rp" ns
      -> In "obuf" ns
      -> In "olen" ns
      -> In "opos" ns
      -> In "overflowed" ns
      -> In "tmp" ns
      -> In "buf" ns
      -> In "ibuf" ns
      -> In "row" ns
      -> In "ilen" ns
      -> In "ipos" ns
      -> In "len" ns
      -> In "data" ns
      -> In "dummy" ns
      -> In "matched" ns
      -> In "res" ns
      -> In "lex" ns
      -> incl ("buf" :: "len" :: "lex" :: "res"
        :: "tagStart" :: "tagLen" :: "matched" :: "stack" :: "level" :: nil)
      ns
      -> (res >= 11)%nat
      -> "array8"!"copy" ~~ im ~~> copyS
      -> "array8"!"equal" ~~ im ~~> equalS
      -> "buffers"!"bmalloc" ~~ im ~~> Buffers.bmallocS
      -> "malloc"!"malloc" ~~ im ~~> mallocS
      -> "xml_lex"!"next" ~~ im ~~> nextS
      -> "xml_lex"!"position" ~~ im ~~> positionS
      -> "xml_lex"!"setPosition" ~~ im ~~> setPositionS
      -> "xml_lex"!"tokenStart" ~~ im ~~> tokenStartS
      -> "xml_lex"!"tokenLength" ~~ im ~~> tokenLengthS
      -> "malloc"!"free" ~~ im ~~> freeS
      -> "sys"!"abort" ~~ im ~~> abortS
      -> "numops"!"div4" ~~ im ~~> div4S
      -> "buffers"!"bfree" ~~ im ~~> bfreeS
      -> forall pr0 pre,
        (forall specs st,
          interp specs (pre st)
          -> interp specs (cpinv true (fun x : W => x) ns res st))
        -> wf ts pr0
        -> incl (cdatasOf pr0) ns
        -> vcs (VerifCond (toCmd (compileProgram' pr0) mn H ns res pre)).
      induction pr0; wrap0;
        repeat match goal with
                 | [ |- vcs (_ :: _) ] => wrap0
                 | [ H : _ |- vcs _ ] => apply H;
                   try apply compileProgram_post
               end; try abstract t.
      t.
      unfold localsInvariant.
      descend.
      my_step.
      my_step.
      descend.
      rewrite H1.
      rewrite mult4_S in *.
      rewrite wplus_wminus.
      my_step.
      my_step.
      my_descend; my_step.
      my_descend; my_step.
      my_descend; my_step.
      my_descend; my_step.
    Qed.

    Hint Resolve compileProgram_post compileProgram_vcs.

    Notation CompileVcs pr := (fun im ns res =>
      (~In "rp" ns) :: In "obuf" ns :: In "olen" ns :: In "opos" ns :: In "overflowed" ns
      :: In "tmp" ns :: In "buf" ns :: In "ibuf" ns :: In "row" ns :: In "ilen" ns
      :: In "ipos" ns :: In "len" ns :: In "data" ns :: In "dummy" ns
      :: In "matched" ns :: In "res" ns :: In "lex" ns
      :: incl ("buf" :: "len" :: "lex" :: "res"
        :: "tagStart" :: "tagLen" :: "matched" :: "stack" :: "level" :: nil)
      ns
      :: (res >= 11)%nat
      :: "array8"!"copy" ~~ im ~~> copyS
      :: "array8"!"equal" ~~ im ~~> equalS
      :: "buffers"!"bmalloc" ~~ im ~~> Buffers.bmallocS
      :: "malloc"!"malloc" ~~ im ~~> mallocS
      :: "xml_lex"!"next" ~~ im ~~> nextS
      :: "xml_lex"!"position" ~~ im ~~> positionS
      :: "xml_lex"!"setPosition" ~~ im ~~> setPositionS
      :: "xml_lex"!"tokenStart" ~~ im ~~> tokenStartS
      :: "xml_lex"!"tokenLength" ~~ im ~~> tokenLengthS
      :: "malloc"!"free" ~~ im ~~> freeS
      :: "sys"!"abort" ~~ im ~~> abortS
      :: "numops"!"div4" ~~ im ~~> div4S
      :: "buffers"!"bfree" ~~ im ~~> bfreeS
      :: wf ts pr
      :: incl (cdatasOf pr) ns
      :: NoDup (Names ts)
      :: twfs ts
      :: nil).

    Definition compileProgram : chunk.
      refine (WrapC (compileProgram' pr)
        cpinv
        cpinv
        (CompileVcs pr) _ _); abstract (
          intros; repeat match goal with
                           | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; intros; subst
                         end; eauto).
    Defined.
  End compileProgram.


  (** Now, create a [vcgen] version that knows about [Pat] and others, with some shameless copy-and-paste. *)

  Ltac vcgen_simp := cbv beta iota zeta delta [WrapC Wrap
    compileProgram map app imps
    LabelMap.add Entry Blocks Postcondition VerifCond
    Straightline_ Seq_ Diverge_ Fail_ Skip_ Assert_
    Structured.If_ Structured.While_ Goto_ Structured.Call_ IGoto
    setArgs Programming.Reserved Programming.Formals Programming.Precondition
    importsMap fullImports buildLocals blocks union Nplus Nsucc length N_of_nat
    List.fold_left ascii_lt string_lt label'_lt
    LabelKey.compare' LabelKey.compare LabelKey.eq_dec
    LabelMap.find
    toCmd Programming.Seq Instr Diverge Fail Skip Assert_
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

  Definition m := bimport [["xml_lex"!"next" @ [nextS], "xml_lex"!"position" @ [positionS],
                            "xml_lex"!"setPosition" @ [setPositionS], "xml_lex"!"tokenStart" @ [tokenStartS],
                            "xml_lex"!"tokenLength" @ [tokenLengthS], "malloc"!"malloc" @ [mallocS],
                            "malloc"!"free" @ [freeS], "sys"!"abort" @ [abortS], "sys"!"printInt" @ [printIntS],
                            "xml_lex"!"init" @ [initS], "xml_lex"!"delete" @ [deleteS],
                            "array8"!"copy" @ [copyS], "array8"!"equal" @ [equalS],
                            "buffers"!"bmalloc" @ [Buffers.bmallocS], "buffers"!"bfree" @ [Buffers.bfreeS],
                            "numops"!"div4" @ [div4S] ]]

    bmodule "xml_prog" {{
      {|
        FName := "main";
        FVars := lvars;
        FReserved := 11;
        FPrecondition := Precondition mainS None;
        FBody := Programming.Seq (Assign' ((fun _ => LvMem (Indir Sp O)):lvalue') Rp)
        (Programming.Seq (fun _ _ =>
          Structured nil
          (fun im mn _ =>
            Structured.Assert_ im mn
            (Precondition mainS (Some lvars))))
        ("lex" <-- Call "xml_lex"!"init"("len")
         [Al bsI, Al bsO,
           PRE[V, R] db ts * array8 bsI (V "buf") * array8 bsO (V "obuf") * mallocHeap 0 * xmlp (V "len") R * row nil (V "dummy")
             * [| length bsI = wordToNat (V "len") |] * [| length bsO = wordToNat (V "olen") |]
           POST[R'] db ts * Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf") * mallocHeap 0 * row nil (V "dummy")
             * [| length bsO' = length bsO |] * [| R' <= V "olen" |]%word ];;
         "stack" <- 0;;
         "opos" <- 0;;
         "overflowed" <- 0;;

         compileProgram;;

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

  Lemma rp_cdatasOf : forall pr0,
    In "rp" (cdatasOf pr0)
    -> False.
    clear; induction pr0; simpl; intuition eauto.
    apply In_addTo_or in H; destruct H; eauto.
  Qed.

  Hint Immediate rp_cdatasOf.

  Lemma no_clash_cdatas : forall s pr0,
    In s (cdatasOf pr0)
    -> underscore_free s
    -> False.
    clear; induction pr0; simpl; intuition eauto.
    apply In_addTo_or in H; destruct H; auto.
  Qed.

  Hint Resolve no_clash_cdatas.

  Theorem ok : moduleOk m.
    vcgen;
      (intros; try match goal with
                     | [ H : importsGlobal _ |- _ ] => clear H
                   end; pre).

    Ltac u := abstract t.

    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
    u.
  Qed.

End compileProgram.
