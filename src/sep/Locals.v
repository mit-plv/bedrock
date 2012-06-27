Require Import Ascii Bool String List.
Require Import Word Memory Expr SepExpr SymEval SepIL Env Prover SymEval IL SymIL.
Require Import sep.Array.

Set Implicit Arguments.

Definition vals := string -> W.

Definition toArray (ns : list string) (vs : vals) : list W := map vs ns.

Definition locals (ns : list string) (vs : vals) (p : W) : HProp := array (toArray ns vs) p.

Definition ascii_eq (a1 a2 : ascii) : bool :=
  let (b1, c1, d1, e1, f1, g1, h1, i1) := a1 in
  let (b2, c2, d2, e2, f2, g2, h2, i2) := a2 in
    eqb b1 b2 && eqb c1 c2 && eqb d1 d2 && eqb e1 e2
    && eqb f1 f2 && eqb g1 g2 && eqb h1 h2 && eqb i1 i2.

Lemma ascii_eq_true : forall a,
  ascii_eq a a = true.
  destruct a; simpl; intuition.
  repeat rewrite eqb_reflx; reflexivity.
Qed.

Lemma ascii_eq_false : forall a b,
  a <> b -> ascii_eq a b = false.
  destruct b, a; simpl; intuition.
  match goal with
    | [ |- ?E = _ ] => case_eq E
  end; intuition.
    repeat match goal with
             | [ H : _ |- _ ] => apply andb_prop in H; destruct H
             | [ H : _ |- _ ] => apply eqb_prop in H
           end; congruence.
Qed.

Fixpoint string_eq (s1 s2 : string) : bool :=
  match s1, s2 with
    | EmptyString, EmptyString => true
    | String a1 s1', String a2 s2' => ascii_eq a1 a2 && string_eq s1' s2'
    | _, _ => false
  end.

Theorem string_eq_true : forall s,
  string_eq s s = true.
  induction s; simpl; intuition; rewrite ascii_eq_true; assumption.
Qed.

Theorem string_eq_false : forall s1 s2,
  s1 <> s2 -> string_eq s1 s2 = false.
  induction s1; destruct s2; simpl; intuition.
  match goal with
    | [ |- ?E = _ ] => case_eq E
  end; intuition.
  repeat match goal with
           | [ H : _ |- _ ] => apply andb_prop in H; destruct H
           | [ H : _ |- _ ] => apply eqb_prop in H
         end.
  destruct (ascii_dec a a0); subst.
  destruct (string_dec s1 s2); subst.
  tauto.
  apply IHs1 in n; congruence.
  apply ascii_eq_false in n; congruence.
Qed.

Theorem string_eq_correct : forall s1 s2,
  string_eq s1 s2 = true -> s1 = s2.
  intros; destruct (string_dec s1 s2); subst; auto.
  apply string_eq_false in n; congruence.
Qed.

Definition sel (vs : vals) (nm : string) : W := vs nm.
Definition upd (vs : vals) (nm : string) (v : W) : vals := fun nm' =>
  if string_eq nm' nm then v else vs nm'.

Definition bedrock_type_string : type :=
  {| Expr.Impl := string
   ; Expr.Eqb := string_eq
   ; Expr.Eqb_correct := string_eq_correct |}.

Definition bedrock_type_listString : type :=
  {| Expr.Impl := list string
   ; Expr.Eqb := (fun _ _ => false)
   ; Expr.Eqb_correct := @ILEnv.all_false_compare _ |}.

Definition bedrock_type_vals : type :=
  {| Expr.Impl := vals
   ; Expr.Eqb := (fun _ _ => false)
   ; Expr.Eqb_correct := @ILEnv.all_false_compare _ |}.

Definition types_r : Env.Repr Expr.type :=
  Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in 
    let lst := 
      Some ILEnv.bedrock_type_W ::
      Some ILEnv.bedrock_type_setting_X_state ::
      None ::
      None ::
      None ::
      Some ILEnv.bedrock_type_nat ::
      None ::
      Some bedrock_type_string ::
      Some bedrock_type_listString ::
      Some bedrock_type_vals ::
      nil
    in Env.listOptToRepr lst EmptySet_type.

Local Notation "'pcT'" := (tvType 0).
Local Notation "'stT'" := (tvType 1).
Local Notation "'wordT'" := (tvType 0).
Local Notation "'natT'" := (tvType 5).
Local Notation "'stringT'" := (tvType 7).
Local Notation "'listStringT'" := (tvType 8).
Local Notation "'valsT'" := (tvType 9).

Local Notation "'wplusF'" := 0.
Local Notation "'wmultF'" := 2.
Local Notation "'natToWF'" := 6.
Local Notation "'nilF'" := 10.
Local Notation "'consF'" := 11.
Local Notation "'selF'" := 12.
Local Notation "'updF'" := 13.

Section parametric.
  Variable types' : list type.
  Definition types := repr types_r types'.
  Variable Prover : ProverT types.

  Definition nil_r : signature types.
    refine {| Domain := nil; Range := listStringT |}.
    exact (@nil _).
  Defined.

  Definition cons_r : signature types.
    refine {| Domain := stringT :: listStringT :: nil; Range := listStringT |}.
    exact (@cons _).
  Defined.

  Definition sel_r : signature types.
    refine {| Domain := valsT :: stringT :: nil; Range := wordT |}.
    exact sel.
  Defined.

  Definition upd_r : signature types.
    refine {| Domain := valsT :: stringT :: wordT :: nil; Range := valsT |}.
    exact upd.
  Defined.

  Definition funcs_r : Env.Repr (signature types) :=
    Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in 
      let lst := 
        Some (ILEnv.wplus_r types) ::
        None ::
        Some (ILEnv.wmult_r types) ::
        None ::
        None ::
        None ::
        Some (ILEnv.natToW_r types) ::
        None ::
        None ::
        None ::
        Some nil_r ::
        Some cons_r ::
        Some sel_r ::
        Some upd_r ::
        nil
      in Env.listOptToRepr lst (Default_signature _).

  Definition deref (e : expr types) : option (expr types * nat) :=
    match e with
      | Func wplusF (base :: offset :: nil) =>
        match offset with
          | Func natToWF (Const t k :: nil) =>
            match t return tvarD types t -> _ with
              | natT => fun k => match div4 k with
                                   | None => None
                                   | Some k' => Some (base, k')
                                 end
              | _ => fun _ => None
            end k
          | _ => None
        end
      | _ => None
    end.

  Fixpoint listIn (e : expr types) : option (list string) :=
    match e with
      | Func nilF nil => Some nil
      | Func consF (Const tp s :: t :: nil) =>
        match tp return tvarD types tp -> option (list string) with
          | stringT => fun s => match listIn t with
                                  | None => None
                                  | Some t => Some (s :: t)
                                end
          | _ => fun _ => None
        end s
      | _ => None
    end.

  Fixpoint sym_sel (vs : expr types) (nm : string) : expr types :=
    match vs with
      | Func updF (vs' :: Const tp nm' :: v :: nil) =>
        match tp return tvarD types tp -> expr types with
          | stringT => fun nm' =>
            if string_eq nm' nm
              then v
              else sym_sel vs' nm
          | _ => fun _ => Func selF (vs :: Const (types := types) (t := stringT) nm :: nil)
        end nm'
      | _ => Func selF (vs :: Const (types := types) (t := stringT) nm :: nil)
    end.

  Definition sym_read (summ : Prover.(Facts)) (args : list (expr types)) (p : expr types)
    : option (expr types) :=
    match args with
      | ns :: vs :: p' :: nil =>
        match deref p, listIn ns with
          | Some (base, offset), Some ns =>
            if Prover.(Prove) summ (Equal wordT p' base)
              then match nth_error ns offset with
                     | None => None
                     | Some nm => Some (sym_sel vs nm)
                   end
              else None
          | _, _ => None
        end
      | _ => None
    end.

  Definition sym_write (summ : Prover.(Facts)) (args : list (expr types)) (p v : expr types)
    : option (list (expr types)) :=
    match args with
      | ns :: vs :: p' :: nil =>
        match deref p, listIn ns with
          | Some (base, offset), Some ns' =>
            if Prover.(Prove) summ (Equal wordT p' base)
              then match nth_error ns' offset with
                     | None => None
                     | Some nm => Some (ns
                       :: Func updF (vs :: Const (types := types) (t := stringT) nm :: v :: nil)
                       :: p' :: nil)
                   end
              else None
          | _, _ => None
        end
      | _ => None
    end.
End parametric.

Definition MemEval types' : @MEVAL.PredEval.MemEvalPred (types types').
  eapply MEVAL.PredEval.Build_MemEvalPred.
  eapply sym_read.
  eapply sym_write.
Defined.

Section correctness.
  Variable types' : list type.
  Definition types0 := types types'.

  Definition ssig : SEP.predicate types0 pcT stT.
    refine (SEP.PSig _ _ _ (listStringT :: valsT :: wordT :: nil) _).
    exact locals.
  Defined.

  Definition ssig_r : Env.Repr (SEP.predicate types0 pcT stT) :=
    Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in 
      let lst := 
        None :: Some ssig :: nil
      in Env.listOptToRepr lst (SEP.Default_predicate _ _ _).

  Variable funcs' : functions types0.
  Definition funcs := Env.repr (funcs_r _) funcs'.

  Variable Prover : ProverT types0.
  Variable Prover_correct : ProverT_correct Prover funcs.

  Ltac deconstruct := repeat deconstruct' idtac.

  Lemma deref_correct : forall uvars vars e w base offset,
    exprD funcs uvars vars e wordT = Some w
    -> deref e = Some (base, offset)
    -> exists wb,
      exprD funcs uvars vars base wordT = Some wb
      /\ w = wb ^+ $(offset * 4).
    destruct e; simpl deref; intuition; try discriminate.
    deconstruct.
    simpl exprD in *.
    match goal with
      | [ _ : context[div4 ?N] |- _ ] => specialize (div4_correct N); destruct (div4 N)
    end; try discriminate.
    deconstruct.
    specialize (H2 _ (refl_equal _)); subst.
    repeat (esplit || eassumption).
    repeat f_equal.
    unfold natToW.
    f_equal.
    omega.
  Qed.

  Lemma listIn_correct : forall uvars vars e ns, listIn e = Some ns
    -> exprD funcs uvars vars e listStringT = Some ns.
    induction e; simpl; intuition; try discriminate.
    repeat match type of H with
             | Forall _ (_ :: _ :: nil) => inversion H; clear H; subst
             | _ => deconstruct' idtac
           end.
    inversion H4; clear H4; subst.
    clear H5.
    deconstruct.
    simpl in *.
    erewrite H2; reflexivity.
  Qed.

  Lemma sym_sel_correct : forall uvars vars nm (vs : expr types0) vsv,
    exprD funcs uvars vars vs valsT = Some vsv
    -> exprD funcs uvars vars (sym_sel vs nm) wordT = Some (sel vsv nm).
    induction vs; simpl; intros; try discriminate.

    destruct (equiv_dec t valsT); congruence.

    rewrite H; reflexivity.

    rewrite H; reflexivity.

    Ltac t := simpl in *; try discriminate; try (deconstruct;
      match goal with
        | [ _ : Range (match ?E with nil => _ | _ => _ end) === _ |- _ ] =>
          destruct E; simpl in *; try discriminate;
            match goal with
              | [ H : Range ?X === _ |- _ ] => destruct X; simpl in *; hnf in H; subst
            end;
            match goal with
              | [ H : _ = _ |- _ ] => rewrite H; reflexivity
            end
      end).
    simpl in *.
    do 14 (destruct f; t).

    Focus 2.
    deconstruct.
    destruct s; simpl in *.
    hnf in e; subst.
    rewrite H0; reflexivity.

    destruct l; simpl in *; try discriminate.
    destruct l; simpl in *; try discriminate.
    rewrite H0; reflexivity.
    destruct e0; simpl in *; try (rewrite H0; reflexivity).
    do 2 (destruct l; simpl in *; try (rewrite H0; reflexivity)).
    destruct t; simpl in *; try (rewrite H0; reflexivity).
    do 8 (destruct n; simpl in *; try (rewrite H0; reflexivity)).
    inversion H; clear H; subst.
    inversion H4; clear H4; subst.
    inversion H5; clear H5; subst.
    clear H6.
    destruct (string_dec t0 nm); subst.
    rewrite string_eq_true.
    deconstruct.
    unfold sel, upd.
    rewrite string_eq_true; reflexivity.

    rewrite string_eq_false by assumption.
    deconstruct.
    erewrite H3 by reflexivity.
    f_equal; unfold sel, upd.
    rewrite string_eq_false; auto.
  Qed.

End correctness.
