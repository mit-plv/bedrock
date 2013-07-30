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

(* Language for generating XML code *)
Inductive xml :=
| XCdata (const : string)
| XVar (text : string)
| XTag (tag : string) (inner : list xml)
| XColumn (col : string).

Section xml_ind'.
  Variable P : xml -> Prop.

  Hypothesis H_Cdata : forall const, P (XCdata const).

  Hypothesis H_Var : forall text, P (XVar text).

  Hypothesis H_Tag : forall tag inner, List.Forall P inner -> P (XTag tag inner).

  Hypothesis H_Column : forall col, P (XColumn col).

  Fixpoint xml_ind' (xm : xml) : P xm :=
    match xm with
      | XCdata const => H_Cdata const
      | XVar text => H_Var text
      | XTag tag inner => H_Tag tag ((fix xmls_ind (xms : list xml) : List.Forall P xms :=
        match xms with
          | nil => Forall_nil _
          | xm :: xms' => Forall_cons _ (xml_ind' xm) (xmls_ind xms')
        end) inner)
      | XColumn col => H_Column col
    end.
End xml_ind'.

Opaque xml_ind'.


(* Expressions for data queries and updates *)
Inductive exp :=
| Const (s : string)
| Input (text : string).

Definition equality := (string * exp)%type.
Definition condition := list equality.

(* Language of actions to take for matched patterns *)
Inductive action :=
| Insert (tab : string) (es : list exp)
| Delete (tab : string) (cond : condition)
| Output (xm : xml)
| SelectOutput (tab : string) (cond : condition) (xm : xml)
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

Fixpoint xwf (sch : schema) (xm : xml) : Prop :=
  match xm with
    | XCdata const => goodSize (String.length const)
    | XVar _ => True
    | XTag tag inner => goodSize (String.length tag + 3)
      /\ ForallR (xwf sch) inner
    | XColumn col => In col sch
  end.

Fixpoint xfreeVar (xm : xml) (x : string) : Prop :=
  match xm with
    | XCdata _ => False
    | XVar text => x = text
    | XTag _ inner => ExistsR (fun xm' => xfreeVar xm' x) inner
    | XColumn _ => False
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

Fixpoint compileXml (sch : schema) (p : xml) : XmlOutput.xml :=
  match p with
    | XCdata const => XmlOutput.Cdata const
    | XVar text => XmlOutput.Var (text ++ "_start") (text ++ "_len")
    | XTag tag inner => XmlOutput.Tag tag (map (compileXml sch) inner)
    | XColumn col => XmlOutput.Column "data" sch col
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


(** * Combined well-formedness and related lemmas *)

Record table := {
  Name : string;
  Address : W;
  Schema : schema
}.

Definition twf (t : table) := goodSize (2 + length (Schema t) + length (Schema t)).

Definition tables := list table.
Definition twfs : tables -> Prop := List.Forall twf.

Definition ewf (e : exp) : Prop :=
  match e with
    | Const s => goodSize (String.length s)
    | Input _ => True
  end.

Definition ewfs := List.Forall ewf.

Definition eqwf (sch : schema) (e : equality) : Prop :=
  In (fst e) sch /\ ewf (snd e).

Definition cwf sch : condition -> Prop := List.Forall (eqwf sch).

Fixpoint awf (ts : tables) (a : action) : Prop :=
  match a with
    | Insert tab es => exists t, In t ts /\ Name t = tab
      /\ length es = length (Schema t) /\ ewfs es
    | Delete tab cond => exists t, In t ts /\ Name t = tab
      /\ cwf (Schema t) cond
    | Output xm => xwf nil xm
    | SelectOutput tab cond xm => exists t, In t ts /\ Name t = tab
      /\ cwf (Schema t) cond /\ xwf (Schema t) xm
    | Seq a1 a2 => awf ts a1 /\ awf ts a2
  end.

Definition efreeVar (e : exp) (x : string) : Prop :=
  match e with
    | Const _ => False
    | Input text => x = text
  end.

Fixpoint afreeVar (a : action) (x : string) : Prop :=
  match a with
    | Insert _ es => List.Exists (fun e => efreeVar e x) es
    | Delete _ cond => List.Exists (fun e => efreeVar (snd e) x) cond
    | Output xm => xfreeVar xm x
    | SelectOutput _ cond xm => List.Exists (fun e => efreeVar (snd e) x) cond
      \/ xfreeVar xm x
    | Seq a1 a2 => afreeVar a1 x \/ afreeVar a2 x
  end.

Fixpoint wf (ts : tables) (pr : program) : Prop :=
  match pr with
    | Rule p a => pwf p /\ awf ts a
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


(** * Compiling programs *)

Section compileProgram.
  Variable ts : tables.
  Variable pr : program.

  Definition numCdatas := length (cdatasOf pr).
  Definition reserved := numCdatas + 26.

  Definition preLvars := "lex" :: "res" :: "opos" :: "overflowed"
    :: "tagStart" :: "tagLen" :: "matched" :: "stack" :: "level" :: "tmp"
    :: "ibuf" :: "row" :: "ilen" :: "ipos" :: "data"
    :: cdatasOf pr.
  Definition lvars := "buf" :: "len" :: "obuf" :: "olen" :: "dummy" :: preLvars.

  Definition db := starL (fun t => RelDb.table (Schema t) (Address t)).

  Definition mainS := SPEC("buf", "len", "obuf", "olen", "dummy") reserving reserved
    Al bsI, Al bsO,
    PRE[V] db ts * row nil (V "dummy")
      * array8 bsI (V "buf") * array8 bsO (V "obuf") * mallocHeap 0
      * [| length bsI = wordToNat (V "len") |]
      * [| length bsO = wordToNat (V "olen") |]
    POST[R] db ts * row nil (V "dummy")
      * Ex bsO', array8 bsI (V "buf") * array8 bsO' (V "obuf") * mallocHeap 0
      * [| length bsO' = length bsO |] * [| R <= V "olen" |].

  Hypothesis wellFormed : wf ts pr.

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

  Let distinct : NoDup (cdatasOf pr).
    induction pr; simpl in *; intuition
      auto using allCdatas_NoDup, wf_NoDup, NoDup_addTo.
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
    descend; reger; try rewrite inBounds_sel in *; try rewrite inputOk_sel in *.

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

  Fixpoint findTable (tab : string) (ts : tables) : option table :=
    match ts with
      | nil => None
      | t :: ts => if string_dec tab (Name t) then Some t else findTable tab ts
    end.

  Definition Names := map Name.

  Ltac ift := match goal with
                | [ |- context[if ?E then _ else _] ] => destruct E; intuition
              end.

  Lemma findTable_good : forall tab t ts0,
    NoDup (Names ts0)
    -> In t ts0
    -> Name t = tab
    -> findTable tab ts0 = Some t.
    induction ts0; simpl; inversion 1; intuition subst; ift.
    exfalso; eapply H2.
    rewrite <- e.
    apply in_map; auto.
  Qed.

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
            repeat rewrite H by intuition (congruence || eauto)
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

  Lemma output_wf : forall sch xm,
    xwf sch xm
    -> goodSize (length sch)
    -> XmlOutput.wf (compileXml sch xm).
    induction xm using xml_ind'; simpl; intuition.
    apply Forall_ForallR; apply Forall_map; eapply Forall_impl2; [
      eassumption
      | apply ForallR_Forall; eassumption
      | auto ].
  Qed.

  Hint Immediate output_wf.


  (** ** Action compilation *)

  Fixpoint removeTable (tab : string) (ts : tables) : tables :=
    match ts with
      | nil => nil
      | t :: ts => if string_dec tab (Name t) then removeTable tab ts else t :: removeTable tab ts
    end.

  Variable bufSize : W.

  Hypothesis ND : NoDup (Names ts).
  Hypothesis goodSchema : twfs ts.
  Hypothesis buf_size_lower : bufSize >= natToW 2.
  Hypothesis buf_size_upper : goodSize (4 * wordToNat bufSize).

  Section compileAction.
    Variable p : pat.

    Infix ";;" := SimpleSeq : SP_scope.

    Print RelDbDelete.Delete.

    Fixpoint compileAction' (a : action) : chunk :=
      match a with
        | Insert tab es =>
          match findTable tab ts with
            | None => Fail
            | Some t => RelDbInsert.Insert
              (fun bsO V => db (removeTable tab ts) * array8 bsO (V "obuf")
                * [| length bsO = wordToNat (V "olen") |]
                * [| V "opos" <= V "olen" |]%word
                * [| XmlOutput.inBounds (XmlSearch.allCdatas (compilePat p)) V |]
                * xmlp (V "len") (V "lex") * row nil (V "dummy")
                * Ex ls, sll ls (V "stack") * [| stackOk ls (V "len") |])%Sep
              (fun bsO V R => row nil (V "dummy") * db ts
                * [| R <= V "olen" |]%word * mallocHeap 0
                * Ex bsO', array8 bsO' (V "obuf")
                * [| length bsO' = length bsO |])%Sep
              (Address t) (Schema t) bufSize (compileExps es)
          end
        | Delete tab cond =>
          match findTable tab ts with
            | None => Fail
            | Some t => RelDbDelete.Delete
              (fun bsO V => db (removeTable tab ts) * array8 bsO (V "obuf")
                * [| length bsO = wordToNat (V "olen") |]
                * [| V "opos" <= V "olen" |]%word
                * [| XmlOutput.inBounds (XmlSearch.allCdatas (compilePat p)) V |]
                * xmlp (V "len") (V "lex") * row nil (V "dummy")
                * Ex ls, sll ls (V "stack") * [| stackOk ls (V "len") |])%Sep
              (fun bsO V R => row nil (V "dummy") * db ts
                * [| R <= V "olen" |]%word * mallocHeap 0
                * Ex bsO', array8 bsO' (V "obuf")
                * [| length bsO' = length bsO |])%Sep
              (Address t) (Schema t) "row" "data" (compileCondition cond)
          end
        | Output xm => 
          Out
          (fun (_ : unit) V => db ts * mallocHeap 0 * xmlp (V "len") (V "lex")
            * Ex ls, sll ls (V "stack") * [| stackOk ls (V "len") |])%Sep
          (fun _ V R => row nil (V "dummy") * db ts
            * [| R <= V "olen" |]%word * mallocHeap 0)%Sep
          "dummy" nil
          (XmlSearch.allCdatas (compilePat p))
          (compileXml nil xm)
        | SelectOutput tab cond xm =>
          match findTable tab ts with
            | None => Fail
            | Some t => Select
              (fun bsO V => db (removeTable tab ts) * array8 bsO (V "obuf")
                * [| length bsO = wordToNat (V "olen") |]
                * [| V "opos" <= V "olen" |]%word
                * [| XmlOutput.inBounds (XmlSearch.allCdatas (compilePat p)) V |]
                * xmlp (V "len") (V "lex") * row nil (V "dummy")
                * mallocHeap 0
                * Ex ls, sll ls (V "stack") * [| stackOk ls (V "len") |])%Sep
              (fun bsO V R => row nil (V "dummy") * db ts
                * [| R <= V "olen" |]%word * mallocHeap 0
                * Ex bsO', array8 bsO' (V "obuf")
                * [| length bsO' = length bsO |])%Sep
              (Address t) (Schema t) "row" "data" (compileCondition cond)
              (Out
                (fun (_ : unit) V =>
                  RelDbSelect.inv (Address t) (Schema t) (V "row") (V "data")
                  * db (removeTable (Name t) ts) * mallocHeap 0
                  * xmlp (V "len") (V "lex") * row nil (V "dummy")
                  * Ex ls, sll ls (V "stack") * [| stackOk ls (V "len") |])%Sep
                (fun _ V R => row nil (V "dummy") * db ts
                  * [| R <= V "olen" |]%word
                  * mallocHeap 0)%Sep
                "data" (Schema t)
                (XmlSearch.allCdatas (compilePat p))
                (compileXml (Schema t) xm))
          end
        | Seq a1 a2 =>
          compileAction' a1;;
          compileAction' a2
      end%SP.

    Definition ainv :=
      XmlSearch.inv (fun bsO V => row nil (V "dummy") * db ts
        * array8 bsO (V "obuf")
        * [| length bsO = wordToNat (V "olen") |]
        * [| V "opos" <= V "olen" |]%word)%Sep
      (fun bsO V R => row nil (V "dummy") * db ts
        * Ex bsO', array8 bsO' (V "obuf")
        * [| length bsO' = length bsO |]
        * [| R <= V "olen" |]%word)%Sep
      (XmlSearch.allCdatas (compilePat p)).

    Lemma removeTable_irrel_fwd : forall x ts0,
      ~In x (Names ts0)
      -> db ts0 ===> db (removeTable x ts0).
      induction ts0; simpl; intuition subst; try ift; sepLemma.
    Qed.

    Lemma removeTable_irrel_bwd : forall x ts0,
      ~In x (Names ts0)
      -> db (removeTable x ts0) ===> db ts0.
      induction ts0; simpl; intuition subst; try ift; sepLemma.
    Qed.

    Hint Immediate removeTable_irrel_fwd removeTable_irrel_bwd.

    Lemma removeTable_bwd : forall x ts0,
      NoDup (Names ts0)
      -> In x ts0
      -> RelDb.table (Schema x) (Address x) * db (removeTable (Name x) ts0)
      ===> db ts0.
      induction ts0; inversion 1; simpl; intuition subst;
        match goal with
          | [ |- context[if ?E then _ else _] ] => destruct E; intuition
        end.
      apply Himp_star_frame; try apply Himp_refl; auto.
      exfalso; apply H2; rewrite <- e; eapply in_map; auto.
      simpl.

      sepLemma.
      etransitivity; [ | apply H6 ]; sepLemma.
    Qed.

    Lemma removeTable_fwd : forall x ts0,
      NoDup (Names ts0)
      -> In x ts0
      -> db ts0 ===> RelDb.table (Schema x) (Address x) * db (removeTable (Name x) ts0).
      induction ts0; inversion 1; simpl; intuition subst;
        match goal with
          | [ |- context[if ?E then _ else _] ] => destruct E; intuition
        end.
      apply Himp_star_frame; try apply Himp_refl; auto.
      exfalso; apply H2; rewrite <- e; eapply in_map; auto.
      simpl.

      sepLemma.
      etransitivity; [ apply H6 | ]; sepLemma.
    Qed.

    Ltac cap := abstract (t;
      (etransitivity; [ | apply himp_star_frame; [ | apply removeTable_bwd ] ]; assumption || my_step)
      || (etransitivity; [ apply himp_star_frame; [ apply removeTable_fwd | ] | ]; eassumption || my_step)
      || my_step).

    Lemma compileAction_post : forall im mn (H : importsGlobal im) ns res a pre,
      (forall specs st,
        interp specs (pre st)
        -> interp specs (ainv true (fun x : W => x) ns res st))
      -> awf ts a
      -> forall specs st, interp specs (Postcondition (toCmd (compileAction' a) mn H ns res pre) st)
        -> interp specs (ainv true (fun x : W => x) ns res st).
      induction a; cap.
    Qed.

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

    Lemma compileXml_freeVar : forall sch start len xm,
      XmlOutput.freeVar (compileXml sch xm) (start, len)
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
    Qed.

    Lemma underscore_discrim : forall s1 s2,
      s1 = s2
      -> ~underscore_free s1
      -> underscore_free s2
      -> False.
      intros; congruence.
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

    Lemma goodSize_more : forall t,
      In t ts
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

    Lemma wfExp_compileExp : forall ns e,
      ewf e
      -> (forall text, efreeVar e text
        -> In (text ++ "_start")%string ns /\ In (text ++ "_len")%string ns)
      -> wfExp ns (compileExp e).
      destruct e; simpl; intuition (solve [ eapply proj1; eauto
        | eapply proj2; eauto
        | eapply underscore_discrim'; eauto ]).
    Qed.

    Hint Resolve wfExp_compileExp.

    Lemma wfExps_compileExps : forall ns es,
      ewfs es
      -> (forall text, List.Exists (fun e => efreeVar e text) es
        -> In (text ++ "_start")%string ns /\ In (text ++ "_len")%string ns)
      -> wfExps ns (compileExps es).
      unfold wfExps; induction 1; simpl; intuition.
    Qed.

    Hint Immediate wfExps_compileExps.

    Lemma length_compileExps : forall es, length (compileExps es) = length es.
      intros; apply map_length.
    Qed.

    Hint Rewrite length_compileExps : sepFormula.

    Lemma goodSize_base : forall t,
      In t ts
      -> goodSize (length (Schema t)).
      intros; eapply goodSize_weaken; [ apply goodSize_more | ]; eauto.
    Qed.

    Hint Immediate goodSize_base.

    Notation baseVars := ("buf" :: "len" :: "lex" :: "res"
      :: "tagStart" :: "tagLen" :: "matched" :: "stack" :: "level" :: nil).

    Notation "l ~~ im ~~> s" := (LabelMap.find l%SP im = Some (Precondition s None)) (at level 0).

    Lemma output_wf0 : forall xm,
      xwf nil xm
      -> XmlOutput.wf (compileXml nil xm).
      intros; apply output_wf; auto.
    Qed.

    Hint Immediate output_wf0.

    Lemma good0 : forall data' sch' xm,
      xwf nil xm
      -> freeRowVar (compileXml nil xm) (data', sch')
      -> False.
      induction xm using xml_ind'; simpl; intuition.
      apply ExistsR_Exists in H1; apply Exists_exists in H1.
      destruct H1; intuition idtac.
      eapply in_map_iff in H1; destruct H1; intuition subst.
      eapply Forall_forall in H; eauto.
      apply ForallR_Forall in H3; eapply Forall_forall in H3; eauto.
    Qed.

    Lemma good_data0 : forall data' sch' xm,
      xwf nil xm
      -> freeRowVar (compileXml nil xm) (data', sch')
      -> data' = "dummy".
      intros; exfalso; eauto using good0.
    Qed.

    Lemma good_schema0 : forall data' sch' xm,
      xwf nil xm
      -> freeRowVar (compileXml nil xm) (data', sch')
      -> sch' = nil.
      intros; exfalso; eauto using good0.
    Qed.

    Hint Immediate good_data0 good_schema0.

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
      (forall x, x <> "row" -> x <> "data"
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

    Lemma output_wf' : forall t xm,
      xwf (Schema t) xm
      -> In t ts
      -> twfs ts
      -> XmlOutput.wf (compileXml (Schema t) xm).
      intros.
      eapply Forall_forall in H1; eauto.
      eapply output_wf; eauto.
    Qed.

    Hint Immediate output_wf'.

    Lemma good_data : forall sch data' sch' xm,
      xwf sch xm
      -> freeRowVar (compileXml sch xm) (data', sch')
      -> data' = "data".
      induction xm using xml_ind'; simpl; intuition.
      apply ExistsR_Exists in H1; apply Exists_exists in H1.
      destruct H1; intuition idtac.
      eapply in_map_iff in H1; destruct H1; intuition subst.
      eapply Forall_forall in H; eauto.
      apply ForallR_Forall in H3; eapply Forall_forall in H3; eauto.
    Qed.

    Lemma good_schema : forall sch data' sch' xm,
      xwf sch xm
      -> freeRowVar (compileXml sch xm) (data', sch')
      -> sch' = sch.
      induction xm using xml_ind'; simpl; intuition.
      apply ExistsR_Exists in H1; apply Exists_exists in H1.
      destruct H1; intuition idtac.
      eapply in_map_iff in H1; destruct H1; intuition subst.
      eapply Forall_forall in H; eauto.
      apply ForallR_Forall in H3; eapply Forall_forall in H3; eauto.
    Qed.

    Hint Resolve good_data good_schema.

    Lemma wfEqualities_compileCondition : forall ns sch cond,
      cwf sch cond
      -> (forall text,
        List.Exists (fun e => efreeVar (snd e) text) cond ->
        In (text ++ "_start")%string ns
        /\ In (text ++ "_len")%string ns)
      -> wfEqualities ns sch (compileCondition cond).
      unfold wfEqualities; induction 1; simpl; auto.
      constructor; auto.
      hnf; simpl.
      hnf in H.
      intuition eauto.
    Qed.

    Hint Resolve wfEqualities_compileCondition.

    Lemma noOverlapExpS_compileExp : forall e,
      RelDbSelect.noOverlapExp "row" "data" (compileExp e).
      clear; induction e; simpl; intuition (eauto using underscore_discrim').
    Qed.

    Hint Immediate noOverlapExpS_compileExp.

    Lemma noOverlapExpsS_compileCondition : forall cond,
      RelDbSelect.noOverlapExps "row" "data" (exps (compileCondition cond)).
      unfold RelDbSelect.noOverlapExps; induction cond; simpl; intuition.
    Qed.

    Hint Immediate noOverlapExpsS_compileCondition.

    Lemma noOverlapExp_compileExp : forall e,
      noOverlapExp "row" "data" (compileExp e).
      clear; induction e; simpl; intuition (eauto using underscore_discrim').
    Qed.

    Hint Immediate noOverlapExp_compileExp.

    Lemma noOverlapExps_compileCondition : forall cond,
      noOverlapExps "row" "data" (exps (compileCondition cond)).
      unfold noOverlapExps; induction cond; simpl; intuition.
    Qed.

    Hint Immediate noOverlapExps_compileCondition.

    Ltac cav := abstract (wrap0;
      try match goal with
            | [ |- context[findTable] ] => post; post; erewrite findTable_good by eauto; wrap0
          end;
      try match goal with
            | [ |- vcs (_ :: _) ] => wrap0
          end;
      match goal with
        | [ H : _ |- _ ] =>
          apply compileXml_freeVar in H; post; subst; solve [
            eauto | eapply proj1; eauto | eapply proj2; eauto ]
        | _ => cap
        | _ => repeat (post; intuition idtac;
          match goal with
            | [ H : _ |- _ ] => apply H; auto
          end; try (apply compileAction_post; auto))
      end).

    Lemma inBounds_swizzle''' : forall V V' p,
      (forall x, x <> "row" -> x <> "data"
        -> x <> "ibuf" -> x <> "ilen" -> x <> "tmp"
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
      -> In "data" ns
      -> In "dummy" ns
      -> In "matched" ns
      -> In "res" ns
      -> incl baseVars ns
      -> (res >= 10)%nat
      -> "array8"!"copy" ~~ im ~~> copyS
      -> "array8"!"equal" ~~ im ~~> equalS
      -> "buffers"!"bmalloc" ~~ im ~~> Buffers.bmallocS
      -> "malloc"!"malloc" ~~ im ~~> mallocS
      -> "numops"!"div4" ~~ im ~~> div4S
      -> "malloc"!"free" ~~ im ~~> freeS
      -> "buffers"!"bfree" ~~ im ~~> bfreeS
      -> forall a pre,
        (forall specs st,
          interp specs (pre st)
          -> interp specs (ainv true (fun x : W => x) ns res st))
        -> awf ts a
        -> (forall text, afreeVar a text -> In (text ++ "_start", text ++ "_len")%string
          (XmlSearch.allCdatas (compilePat p)))
        -> (forall text, afreeVar a text -> In (text ++ "_start") ns /\ In (text ++ "_len") ns)%string
        -> vcs (VerifCond (toCmd (compileAction' a) mn H ns res pre)).
      induction a; cav.
    Qed.

    Hint Resolve compileAction_post compileAction_vcs.

    Notation CompileVcs a := (fun im ns res =>
      (~In "rp" ns) :: In "obuf" ns :: In "olen" ns :: In "opos" ns :: In "overflowed" ns
      :: In "tmp" ns :: In "buf" ns :: In "ibuf" ns :: In "row" ns :: In "ilen" ns
      :: In "ipos" ns :: In "len" ns :: In "data" ns :: In "dummy" ns
      :: In "matched" ns :: In "res" ns
      :: incl baseVars ns
      :: (res >= 10)%nat
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

  Lemma In_addTo_or : forall x ls1 ls2,
    In x (addTo ls1 ls2)
    -> In x ls1 \/ In x ls2.
    clear; induction ls1; simpl; intuition.
    generalize (member_means a ls2); destruct (member a ls2); intuition;
      destruct (IHls1 _ H); simpl in *; intuition.
  Qed.

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
