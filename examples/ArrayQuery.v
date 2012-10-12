Require Import PreAutoSep Wrap Conditional.

Import DefineStructured.

Set Implicit Arguments.


(** Test expressions over arrays *)

Inductive exp :=
| Const (w : W)
(* Literal word value *)
| Index
(* Position in the array *)
| Value
(* Content of array cell *)
| Var (x : string)
(* Injected value of Bedrock local variable *).

Inductive condition :=
| Test (e1 : exp) (t : test) (e2 : exp)
(* Basic comparison *)
| Not (c1 : condition)
| And (c1 c2 : condition)
| Or (c1 c2 : condition)
(* Boolean operators *).

Coercion Const : W >-> exp.
Coercion Var : string >-> exp.

Notation "x = y" := (Test x IL.Eq y) : ArrayQuery_scope.
Notation "x <> y" := (Test x IL.Ne y) : ArrayQuery_scope.
Notation "x < y" := (Test x IL.Lt y) : ArrayQuery_scope.
Notation "x <= y" := (Test x IL.Le y) : ArrayQuery_scope.
Notation "x > y" := (Test y IL.Lt x) : ArrayQuery_scope.
Notation "x >= y" := (Test y IL.Le x) : ArrayQuery_scope.

Notation "!" := Not : ArrayQuery_scope.
Infix "&&" := And : ArrayQuery_scope.
Infix "||" := Or : ArrayQuery_scope.

Delimit Scope ArrayQuery_scope with ArrayQuery.

Definition eval (vs : vals) (index value : W) (e : exp) : W :=
  match e with
    | Const w => w
    | Index => index
    | Value => value
    | Var x => sel vs x
  end.

Fixpoint satisfies (vs : vals) (index value : W) (c : condition) : Prop :=
  match c with
    | Test e1 t e2 => (evalTest t) (eval vs index value e1) (eval vs index value e2) = true
    | Not c1 => ~satisfies vs index value c1
    | And c1 c2 => satisfies vs index value c1 /\ satisfies vs index value c2
    | Or c1 c2 => satisfies vs index value c1 \/ satisfies vs index value c2
  end.

Section Query.
  Variable arr : string.
  (* Name of local variable containing an array to query *)
  Variable size : string.
  (* Name of local variable containing the array length in words *)
  Variable index : string.
  (* Name of local variable that, inside the loop, is assigned the current array index *)
  Variable value : string.
  (* Name of local variable that, inside the loop, is assigned the current array cell value *)

  Variable c : condition.
  (* We will loop over only those indices satisfying this condition. *)

  Variable imports : LabelMap.t assert.
  Hypothesis H : importsGlobal imports.
  Variable modName : string.

  Variable invPre : list W -> vals -> qspec.
  Variable invPost : vals -> W -> qspec.
  (* Loop invariant (precondition and postcondition), parameterized over list of cells already considered
   * (parameter starts as [nil] and grows monotonically to full array) *)

  Variables Body : cmd imports modName.
  (* Code to run on each matching array index *)

  Variable ns : list string.
  (* Local variable names *)
  Variable res : nat.
  (* Reserved stack slots *)

  Definition loopInvariant : assert :=
    st ~> ExX, Ex wsPre, Ex vs, qspecOut (invPre wsPre (sel vs)) (fun PR =>
      Ex ws, ![ ^[locals ("rp" :: ns) vs res st#Sp * array ws (sel vs arr) * PR] * #0 ] st
      /\ [| sel vs size = length ws /\ sel vs index = length wsPre |]
      /\ Ex wsPost, [| ws = wsPre ++ wsPost |]
      /\ sel vs "rp" @@ (st' ~>
        [| st'#Sp = st#Sp |]
        /\ Ex vs', qspecOut (invPost (sel vs) st'#Rv) (fun PO =>
          ![ ^[locals ("rp" :: ns) vs' res st#Sp * array ws (sel vs arr) * PO] * #1 ] st'))).

  Definition expBound (e : exp) : Prop :=
    match e with
      | Const _ => True
      | Index => True
      | Value => True
      | Var x => In x ns
    end.

  Fixpoint conditionBound (c : condition) : Prop :=
    match c with
      | Test e1 _ e2 => expBound e1 /\ expBound e2
      | Not c1 => conditionBound c1
      | And c1 c2 => conditionBound c1 /\ conditionBound c2
      | Or c1 c2 => conditionBound c1 \/ conditionBound c2
    end.

  Definition expOut (e : exp) : rvalue :=
    match e with
      | Const w => w
      | Index => variableSlot index ns
      | Value => variableSlot value ns
      | Var x => variableSlot x ns
    end.

  Fixpoint conditionOut (c : condition) : bexp :=
    match c with
      | Test e1 t e2 => Conditional.Test (expOut e1) t (expOut e2)
      | Not c1 => Conditional.Not (conditionOut c1)
      | And c1 c2 => Conditional.And (conditionOut c1) (conditionOut c2)
      | Or c1 c2 => Conditional.Or (conditionOut c1) (conditionOut c2)
    end.

  (* Here's the raw command, which we will later wrap with nicer VCs. *)
  Definition Query_ : cmd imports modName :=
    Seq_ H
    (Straightline_ _ _ (Assign (variableSlot index ns) 0 :: nil))
    (Structured.While_ H loopInvariant (variableSlot index ns) IL.Lt (variableSlot size ns)
      (Seq_ H
        (Cond_ _ H _ (conditionOut c)
          (Seq_ H
            (Straightline_ _ _ (
              Binop Rv (variableSlot index ns) Times 4
              :: Binop Rv (variableSlot arr ns) Plus Rv
              :: Assign (variableSlot value ns) (LvMem (Reg Rv))
              :: nil))
            Body)
          (Skip_ _ _))
        (Straightline_ _ _ (Binop (variableSlot index ns) (variableSlot index ns) Plus 1 :: nil)))).

  Ltac wrap := wrap0; post; wrap1.

  Hint Resolve simplify_fwd.

  Lemma subst_qspecOut_fwd : forall pc state (specs : codeSpec pc state) A v qs (k : _ -> propX _ _ (A :: nil)),
    interp specs (subst (qspecOut qs k) v)
    -> interp specs (qspecOut qs (fun x => subst (k x) v)).
    induction qs; propxFo; eauto.
  Qed.

  Lemma subst_qspecOut_bwd : forall pc state (specs : codeSpec pc state) A v qs (k : _ -> propX _ _ (A :: nil)),
    interp specs (qspecOut qs (fun x => subst (k x) v))
    -> interp specs (subst (qspecOut qs k) v).
    induction qs; propxFo; eauto.
  Qed.

  Fixpoint domain (qs : qspec) : Type :=
    match qs with
      | Programming.Body _ => unit
      | Quant _ f => sigT (fun x => domain (f x))
    end.

  Fixpoint qspecOut' (qs : qspec) : domain qs -> HProp :=
    match qs with
      | Programming.Body P => fun _ => P
      | Quant _ f => fun d => qspecOut' (f (projT1 d)) (projT2 d)
    end.

  Lemma qspecOut_fwd : forall (specs : codeSpec W (settings * state)) qs k,
    interp specs (qspecOut qs k)
    -> exists v : domain qs, interp specs (k (qspecOut' qs v)).
    induction qs; simpl; propxFo.
    exists tt; auto.
    apply H0 in H1; destruct H1.
    exists (existT _ x x0); eauto.
  Qed.

  Lemma qspecOut_bwd : forall (specs : codeSpec W (settings * state)) qs k v,
    interp specs (k (qspecOut' qs v))
    -> interp specs (qspecOut qs k).
    induction qs; simpl; propxFo; eauto.
  Qed.

  Definition Query : cmd imports modName.
    refine (Wrap _ H _ Query_
      (fun _ st => Ex ws, ExX, Ex vs, qspecOut (invPre ws (sel vs)) (fun PR =>
        ![ ^[locals ("rp" :: ns) vs res st#Sp * array ws (sel vs arr) * PR] * #0 ] st
        /\ [| sel vs size = length ws |]
        /\ sel vs "rp" @@ (st' ~>
          [| st'#Sp = st#Sp |]
          /\ Ex vs', qspecOut (invPost (sel vs) st'#Rv) (fun PO =>
            ![ ^[locals ("rp" :: ns) vs' res st#Sp * array ws (sel vs arr) * PO] * #1 ] st'))))%PropX
      (fun _ =>
        In arr ns
        :: In size ns
        :: In index ns
        :: In value ns
        :: (~In "rp" ns)
        :: conditionBound c
        :: VerifCond (Body (st ~> Ex wsPre, ExX, Ex vs, qspecOut (invPre wsPre (sel vs)) (fun PR =>
          Ex ws, ![ ^[locals ("rp" :: ns) vs res st#Sp * array ws (sel vs arr) * PR] * #0 ] st
          /\ [| sel vs size = length ws /\ sel vs index = length wsPre |]
          /\ Ex wsPost, [| ws = wsPre ++ sel vs value :: wsPost |]
          /\ sel vs "rp" @@ (st' ~>
            [| st'#Sp = st#Sp |]
            /\ Ex vs', qspecOut (invPost (sel vs) st'#Rv) (fun PO =>
              ![ ^[locals ("rp" :: ns) vs' res st#Sp * array ws (sel vs arr) * PO] * #1 ] st'))))))
      _ _).

    wrap.
    Opaque In variableSlot.
    apply subst_qspecOut_fwd in H0; simpl in H0.
    apply qspecOut_fwd in H0; simpl in H0; autorewrite with sepFormula in H0; simpl in H0; destruct H0.
    apply simplify_fwd in H.
    simpl in H.
    destruct H; clear H.
    repeat match goal with
             | [ H : Logic.ex _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
           end.
    subst.
    apply simplify_bwd in H.
    autorewrite with sepFormula in H; simpl in H.
    destruct x; unfold fst, snd in *.
    evaluate auto_ext.
    propxFo.
    assert (goodSize (length (x1 ++ x5))) by eauto.
    rewrite H15 in H18.
    rewrite H0 in H18.
    rewrite app_length in *.
    eapply wle_goodSize in H18; [ | eauto | eauto ].
    assert (x5 = nil) by (destruct x5; simpl in H18; auto; omega).
    subst.
    descend.
    apply subst_qspecOut_bwd; eapply qspecOut_bwd.
    post.
    rewrite app_nil_r in *.
    step auto_ext.
    step auto_ext.
    rewrite H0; f_equal; omega.
    descend.
    step auto_ext.
    descend.
    step auto_ext.
    descend.
    step auto_ext.
    descend.
    step auto_ext.
    rewrite app_nil_r.
    apply Imply_refl.

    (* VS *)
    admit.
  Defined.

End Query.
