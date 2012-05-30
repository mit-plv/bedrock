Require Import List DepList.
Require Import EqdepClass.
Require Import IL Word.
Require Import Bool Folds.
Require Import Reflection. 

Set Implicit Arguments.

(** The reification mechanism use instances of this type-class to
decide how to reify the types *)
Module ReificationHint.
  Class Pkg (T : Type) := mk_Pkg
    {
      Eqb : forall (x y : T), bool;
      Eqb_correct : forall x y, Eqb x y = true -> x = y
    }. 
End ReificationHint. 

Section env.
  (** Syntax **)
  Record type := Typ {
    Impl : Type;
    Eqb : forall x y : Impl, bool;
    Eqb_correct : forall x y, Eqb x y = true -> x = y
  }.
  
  Definition Impl_ (o : option type) : Type :=
    match o return Type with
      | None => Empty_set
      | Some t => Impl t
    end.

  Variable types : list type.

  (** this type requires decidable equality **)
  Inductive tvar : Type :=
  | tvProp 
  | tvType : nat -> tvar.

  Definition tvarD (x : tvar) := 
    match x return Type with
      | tvProp => Prop
      | tvType x =>
        Impl_ (nth_error types x)
    end.

  Definition EmptySet_type : type :=
  {| Impl := Empty_set 
   ; Eqb := fun x _ => match x with end
   ; Eqb_correct := fun x _ _ => match x with end                     
   |}.
  
  Definition Prop_type : type. 
  refine ({| Impl := Prop
       ; Eqb := fun _ _ => false
       ; Eqb_correct := _
   |}). abstract (discriminate). 
  Defined. 

  Definition typeFor (t : tvar) : type :=
    match t with
      | tvProp => Prop_type
      | tvType t => 
        match nth_error types t with
          | None => EmptySet_type
          | Some v => v 
        end
    end.

  Definition tvar_val_seqb (t : tvar) : forall (x y : tvarD t), bool :=
    match t with 
      | tvProp => fun _ _ => false
      | tvType t => 
        match nth_error types t as k return forall x y : match k with 
                                                           | None => Empty_set
                                                           | Some t => Impl t
                                                         end, bool with
          | None => fun x _ => match x with end
          | Some t => fun x y =>  Eqb t x y 
        end
    end.

  Lemma tvar_val_seqb_correct t x y : tvar_val_seqb t x y = true -> x = y.
  Proof. 
    revert x y. destruct t; simpl.   
    discriminate. 
    destruct (nth_error types n); simpl. 
    refine (fun x y H => Eqb_correct _ x y H). 
    intros []. 
  Defined. 

  Fixpoint functionTypeD (domain : list Type) (range : Type) : Type :=
    match domain with
      | nil => range
      | d :: domain' => d -> functionTypeD domain' range
    end.

  Record signature := Sig {
    Domain : list tvar;
    Range : tvar;
    Denotation : functionTypeD (map tvarD Domain) (tvarD Range)
  }.

  Definition Default_signature : signature :=
  {| Domain := nil
   ; Range := tvProp
   ; Denotation := True
   |}.

  Definition functions := list signature.
  Definition variables := list tvar.

  Variable funcs : functions.
  Variable uvars : variables.
  Variable vars : variables.

  Definition func := nat.
  Definition var := nat.
  Definition uvar := nat.

  Unset Elimination Schemes.

  Inductive expr : Type :=
  | Const : forall t : tvar, tvarD t -> expr
  | Var : var -> expr
  | Func : forall f : func, list expr -> expr
  | Equal : tvar -> expr -> expr -> expr
  | Not : expr -> expr
  | UVar : uvar -> expr.

  Definition exprs : Type := list expr.

  Set Elimination Schemes.

  Section expr_ind.
    Variable P : expr -> Prop.

    Hypotheses
      (Hc : forall (t : tvar) (t0 : tvarD t), P (Const t t0))
      (Hv : forall x : var, P (Var x))
      (Hu : forall x : uvar, P (UVar x))
      (Hf : forall (f : func) (l : list expr), Forall P l -> P (Func f l))
      (He : forall t e1 e2, P e1 -> P e2 -> P (Equal t e1 e2))
      (Hn : forall e, P e -> P (Not e)).

    Theorem expr_ind : forall e : expr, P e.
    Proof.
      refine (fix recur e : P e :=
        match e as e return P e with
          | Const t v => @Hc t v 
          | Var x => Hv x
          | UVar x => Hu x
          | Func f xs => @Hf f xs ((fix prove ls : Forall P ls :=
            match ls as ls return Forall P ls with
              | nil => Forall_nil _
              | l :: ls => Forall_cons _ (recur l) (prove ls)
            end) xs)
          | Equal tv e1 e2 => He tv (recur e1) (recur e2)
          | Not e => Hn (recur e)
        end).
    Defined.
  End expr_ind.

 
  Global Instance EqDec_tvar : EqDec _ (@eq tvar).
   red. change (forall x y : tvar, {x = y} + {x <> y}).
    decide equality. eapply Peano_dec.eq_nat_dec.
  Defined.
  
  Definition tvar_seqb (x y : tvar) : bool :=
    match x, y with
        | tvProp , tvProp => true
        | tvType x , tvType y => if Peano_dec.eq_nat_dec x y then true else false
        | _,_ => false
    end.

  Lemma tvar_seqb_correct (x y : tvar) : tvar_seqb x y = true -> x = y.
  Proof. 
    revert x y. intros [|x] [|y]; simpl; try (reflexivity|| discriminate).
    destruct (Peano_dec.eq_nat_dec); simpl; try (subst; reflexivity|| discriminate). 
  Defined. 
  
  Definition env : Type := list (sigT tvarD).

  Definition env_empty : env := nil.

  Definition lookupAs (ls : env) (t : tvar) (i : nat)
    : option (tvarD t) :=
    match nth_error ls i with 
      | None => None
      | Some tv => 
        match equiv_dec (projT1 tv) t with
          | left pf =>
            Some match pf in _ = t return tvarD t with
                   | refl_equal => projT2 tv
                 end
          | right _ => None
        end
    end.

  Lemma lookupAs_det : forall v x t1 t2,
    lookupAs v t1 x <> None
    -> lookupAs v t2 x <> None
    -> t1 = t2.
    unfold lookupAs. clear.
    induction v; destruct x; simpl; intros; try congruence.
      destruct a; simpl in *.
      destruct (equiv_dec x t1); destruct (equiv_dec x t2); try congruence.
      eauto.
  Qed.

  Variable meta_env : env.
  Variable var_env : env.


  Section applyD.
    Variable exprD : expr -> forall t, option (tvarD t).

    Fixpoint applyD domain (xs : list expr) {struct xs}
      : forall range, functionTypeD (map tvarD domain) range -> option range :=
        match domain as domain , xs 
          return forall range, functionTypeD (map tvarD domain) range -> option range
          with
          | nil , nil => fun _ v => Some v
          | t :: ts , e :: es =>
            match exprD e t with
              | None => fun _ _ => None
              | Some v => fun r f => applyD ts es r (f v)
            end
          | _ , _ => fun _ _ => None
        end.
  End applyD.

  Fixpoint exprD (e : expr) (t : tvar) : option (tvarD t) :=
    match e with
      | Const t' c =>
        match equiv_dec t' t with
          | left pf => 
            Some match pf in _ = t return tvarD t with 
                   | refl_equal => c
                 end
          | right _ => None 
        end
      | Var x => lookupAs var_env t x
      | UVar x => lookupAs meta_env t x 
      | Func f xs =>
        match nth_error funcs f with
          | None => None
          | Some f =>
            match equiv_dec (Range f) t with
              | right _ => None
              | left pf => 
                match pf in _ = t return option (tvarD t) with
                  | refl_equal =>
                    applyD (exprD) _ xs _ (Denotation f)
                end
            end
        end
      | Equal t' e1 e2 =>
        match t with
          | tvProp => match exprD e1 t', exprD e2 t' with
                        | Some v1, Some v2 => Some (v1 = v2)
                        | _, _ => None
                      end
          | _ => None
        end
      | Not e1 => match t with
                    | tvProp =>
                      match exprD e1 tvProp with
                        | None => None
                        | Some p => Some (not p)
                      end
                    | _ => None
                  end
    end.

  Theorem exprD_det : forall e t1 t2, exprD e t1 <> None
    -> exprD e t2 <> None
    -> t1 = t2.
  Proof.
    induction e; simpl; intros; try solve [ eapply lookupAs_det; eauto ];
      repeat match goal with
               | [ H : context [ match ?Y with 
                                   | left _ => _ | right _ => _ 
                                 end ] |- _ ] => destruct Y; try congruence
               | [ H : context [ match nth_error ?A ?B with 
                                   | Some _ => _ | None => _ 
                                 end ] |- _ ] => destruct (nth_error A B); try congruence
             end;
    destruct t1; destruct t2; auto.
  Qed.

  Section type_system.
    Definition tenv : Type := list tvar.
    Record tsignature : Type := SigT {
      TDomain : list tvar ;
      TRange  : tvar
    }.
    
    Definition tfunctions : Type := list tsignature.

    Variable tfuncs : tfunctions.
    Variable tmeta_env : tenv.
    Variable tvar_env : tenv.

    Definition WellTyped_env (t : tenv) (g : env) : Prop :=
      t = map (@projT1 _ _) g.
    Definition WellTyped_sig (t : tsignature) (g : signature) : Prop :=
      TDomain t = Domain g /\ TRange t = Range g.
    
    Definition WellTyped_funcs (t : tfunctions) (g : functions) : Prop :=
      Forall2 WellTyped_sig t g.

    Fixpoint typeof (e : expr) : option tvar :=
      match e with
        | Const t _ => Some t
        | Var x => nth_error tvar_env x
        | UVar x => nth_error tmeta_env x
        | Func f _ => match nth_error tfuncs f with
                        | None => None
                        | Some r => Some (TRange r)
                      end
        | Equal _ _ _
        | Not _ => Some tvProp
      end.

    Definition typeof_env : env -> tenv :=
      map (@projT1 _ _).
    Definition typeof_sig (s : signature) : tsignature :=
      {| TDomain := Domain s
       ; TRange  := Range s
       |}.
    Definition typeof_funcs : functions -> tfunctions :=
      map typeof_sig.

    Theorem typeof_env_WellTyped_env : forall g,
      WellTyped_env (typeof_env g) g.
    Proof.
      clear. intros. reflexivity.
    Qed.
    Theorem typeof_sig_WellTyped_sig : forall f,
      WellTyped_sig (typeof_sig f) f.
    Proof.
      clear. unfold WellTyped_sig; intuition.
    Qed.
    Theorem typeof_funcs_WellTyped_funcs : forall f,
      WellTyped_funcs (typeof_funcs f) f.
    Proof.
      clear; induction f; simpl; intros; econstructor; auto using typeof_sig_WellTyped_sig.
    Qed.


    Fixpoint is_well_typed (e : expr) (t : tvar) {struct e} : bool :=
      match e with 
        | Const t' _ => 
          if equiv_dec t' t then true else false
        | Var x => match nth_error tvar_env x with
                     | None => false
                     | Some t' => if equiv_dec t t' then true else false
                   end
        | UVar x => match nth_error tmeta_env x with
                      | None => false
                      | Some t' => if equiv_dec t t' then true else false
                    end
        | Func f xs => 
          match nth_error tfuncs f with
            | None => false
            | Some f =>
              if equiv_dec t (TRange f) then 
                all2 is_well_typed xs (TDomain f)
                else false
          end
        | Equal t' e1 e2 => 
          match t with
            | tvProp => is_well_typed e1 t' && is_well_typed e2 t'
            | _ => false
          end
        | Not e1 => match t with
                      | tvProp => is_well_typed e1 tvProp
                      | _ => false
                    end
      end.
(*
    Definition well_typed (e : expr) : option tvar :=
      match e with 
        | Const t' _ => Some t'
        | Var x => nth_error tvar_env x
        | UVar x => 
          match nth_error meta_env x with
            | None => None
            | Some z => Some (projT1 z)
          end
        | Func f xs => 
          match nth_error funcs f with
            | None => None
            | Some f =>
              if (all2 is_well_typed xs (Domain f))
                then Some (Range f) else None
          end
        | Equal t' e1 e2 => 
          if is_well_typed e1 t' && is_well_typed e2 t'
            then Some tvProp else None
        | Not e1 => if is_well_typed e1 tvProp then Some tvProp else None
      end.
*)

    Hypothesis WT_meta : WellTyped_env tmeta_env meta_env.
    Hypothesis WT_vars : WellTyped_env tvar_env var_env.
    Hypothesis WT_funcs : WellTyped_funcs tfuncs funcs.

      Lemma WellTyped_env_nth_error_Some : forall g t n T,
        WellTyped_env t g ->
        nth_error t n = Some T ->
        exists v, nth_error g n = Some (@existT _ _ T v).
      Proof.
        clear. induction g; destruct t; destruct n; simpl; unfold WellTyped_env, error, value in *; simpl; intros; try congruence.
        inversion H0; clear H0; subst. inversion H; subst.
        exists (projT2 a). destruct a; auto.
        inversion H. eapply IHg; eauto.
      Qed.

      Lemma WellTyped_env_nth_error_None : forall g t n,
        WellTyped_env t g ->
        nth_error t n = None ->
        nth_error g n = None.
      Proof.
        clear. induction g; destruct t; destruct n; simpl; unfold WellTyped_env, error, value in *; simpl; intros; try congruence.
        inversion H. eapply IHg; eauto.
      Qed.

    
    Theorem exprD_principal : forall e t, exprD e t <> None
      -> match typeof e with
           | None => False
           | Some t' => exprD e t' <> None
         end.
    Proof.
      induction e; simpl; unfold lookupAs; intros;
        try solve [ repeat (simpl in *; try congruence; 
          match goal with
            | [ |- context[nth_error ?E ?F] ] => case_eq (nth_error E F); intros
            | [ H : nth_error _ _ = _ |- _ ] =>
              (eapply WellTyped_env_nth_error_Some in H; [ | eassumption ]) ||
              (eapply WellTyped_env_nth_error_None in H; [ | eassumption ])
            | [ |- context[ equiv_dec ?A ?A ] ] => rewrite (EquivDec_refl_left A)
            | [ H : match ?X with
                      | Some _ => _ | None => _ 
                    end <> None |- _ ] => destruct X; [ | solve [ exfalso; auto ] ]
            | [ H : context [ match ?X with
                                | left _ => _ | right _ => _ 
                              end ] |- _ ] => destruct X; [ | solve [ exfalso; auto ] ]
            | [ H : context [ match ?X with
                                | tvProp => _ | tvType _ => _ 
                              end ] |- _ ] => destruct X; [ | solve [ exfalso; auto ] ]
            | [ H : match ?pf with refl_equal => _ end = _ |- _ ] => rewrite (UIP_refl pf) in H
            | [ H : exists x, _ |- _ ] => destruct H
            | [ H : _ = _ |- _ ] => rewrite H in *
            | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
          end) ].
repeat (simpl in *; try congruence; 
          match goal with
            | [ |- context[nth_error ?E ?F] ] => case_eq (nth_error E F); intros
            | [ H : nth_error _ _ = _ |- _ ] =>
              (eapply WellTyped_env_nth_error_Some in H; [ | eassumption ]) ||
              (eapply WellTyped_env_nth_error_None in H; [ | eassumption ])
            | [ |- context[ equiv_dec ?A ?A ] ] => rewrite (EquivDec_refl_left A)
            | [ H : match ?X with
                      | Some _ => _ | None => _ 
                    end <> None |- _ ] => destruct X; [ | solve [ exfalso; auto ] ]
            | [ H : context [ match ?X with
                                | left _ => _ | right _ => _ 
                              end ] |- _ ] => destruct X; [ | solve [ exfalso; auto ] ]
            | [ H : context [ match ?X with
                                | tvProp => _ | tvType _ => _ 
                              end ] |- _ ] => destruct X; [ | solve [ exfalso; auto ] ]
            | [ H : match ?pf with refl_equal => _ end = _ |- _ ] => rewrite (UIP_refl pf) in H
            | [ H : exists x, _ |- _ ] => destruct H
            | [ H : _ = _ |- _ ] => rewrite H in *
            | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
          end).
Lemma Forall2_nth_error_both_Some : forall T U (P : T -> U -> Prop) l r,
  Forall2 P l r ->
  forall n L R,
  nth_error l n = Some L ->
  nth_error r n = Some R ->
  P L R.
Proof.
  clear; induction 1; destruct n; simpl; unfold value, error; intros; try congruence; eauto.
Qed.
eapply Forall2_nth_error_both_Some in WT_funcs; eauto. destruct WT_funcs. destruct (equiv_dec (Range s) (TRange t0)); try congruence.
unfold equiv in *. subst. destruct s; simpl in *. subst. revert H. rewrite (UIP_refl e0). 
induction 1; simpl; destruct TDomain; auto; try congruence.

Lemma Forall2_nth_error_L_None : forall T U (P : T -> U -> Prop) l r,
  Forall2 P l r ->
  forall n,
  nth_error l n = None ->
  nth_error r n = None.
Proof.
  clear; induction 1; destruct n; simpl; unfold value, error; intros; try congruence; eauto.
Qed.

Lemma Forall2_nth_error_L : forall T U (P : T -> U -> Prop) l r,
  Forall2 P l r ->
  forall n L,
  nth_error l n = Some L ->
  exists R,
    nth_error r n = Some R /\ P L R.
Proof.
  clear; induction 1; destruct n; simpl; unfold value, error; intros; try congruence; eauto.
  inversion H1; subst; eauto.
Qed.
eapply Forall2_nth_error_L_None in WT_funcs; try eassumption.
rewrite WT_funcs in *. congruence.
Qed.

  

  Lemma exprD_typeof : forall a1 t D,
    exprD a1 t = Some D ->
    typeof a1 = Some t.
  Proof.
    intros.
    assert (exprD a1 t <> None); try congruence.
    apply exprD_principal in H0.
    destruct (typeof a1); try contradiction.
    f_equal.
    eapply exprD_det in H0. symmetry; eassumption. congruence.
  Qed.


(*
  Theorem well_typed_is_well_typed : forall e t, 
    well_typed e = Some t <-> is_well_typed e t = true.
  Proof.
    clear. induction e; simpl; intros; 
    try solve [ split; intros; unfold lookupAs in * ;
      repeat match goal with
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
               | [ H : context [ equiv_dec ?A ?A ] |- _ ] => rewrite (@EquivDec_refl_left _ _ A) in H
               | [ |- context [ equiv_dec ?A ?A ] ] => rewrite (@EquivDec_refl_left _ _ A)
               | [ H : context [ equiv_dec ?A ?B ] |- _ ] => destruct (equiv_dec A B)
               | [ H : context [ nth_error ?A ?B ] |- _ ] => destruct (nth_error A B)
             end; try congruence; auto ].
    
    Focus.
    split; intros; unfold lookupAs in * ;
      repeat match goal with
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
               | [ H : context [ equiv_dec ?A ?A ] |- _ ] => rewrite (@EquivDec_refl_left _ _ A) in H
               | [ |- context [ equiv_dec ?A ?A ] ] => rewrite (@EquivDec_refl_left _ _ A)
               | [ H : context [ equiv_dec ?A ?B ] |- _ ] => destruct (equiv_dec A B)
               | [ H : context [ nth_error ?A ?B ] |- _ ] => destruct (nth_error A B)
             end; try congruence; auto.
    destruct (all2 is_well_typed l (Domain s)). inversion H0; subst.
      rewrite EquivDec_refl_left; auto.
      congruence.
      rewrite H0.
      congruence.

    split; intros; unfold lookupAs in * ;
      repeat match goal with
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
               | [ H : context [ equiv_dec ?A ?A ] |- _ ] => rewrite (@EquivDec_refl_left _ _ A) in H
               | [ |- context [ equiv_dec ?A ?A ] ] => rewrite (@EquivDec_refl_left _ _ A)
               | [ H : context [ equiv_dec ?A ?B ] |- _ ] => destruct (equiv_dec A B)
               | [ H : context [ nth_error ?A ?B ] |- _ ] => destruct (nth_error A B)
             end; try congruence; auto.
    revert H. case_eq (is_well_typed e1 t); simpl.
    case_eq (is_well_typed e2 t); simpl; intros. inversion H1; auto. congruence.
    intros; congruence.
    destruct t0; try congruence.
    apply andb_true_iff in H. intuition.
    rewrite H0. rewrite H1. auto.

    specialize (IHe tvProp).
    destruct (is_well_typed e tvProp); intuition; try discriminate.
    injection H; intro; subst; reflexivity.
    destruct t; congruence.
    destruct t; congruence.
  Qed.
*)

  Definition ValidProp (e : expr) := 
    exists v, exprD e tvProp = Some v.
  Definition ValidExp (e : expr) := 
    exists t, exists v, exprD e t = Some v.

  Theorem is_well_typed_correct : forall e t, 
    is_well_typed e t = true ->
    exists v, exprD e t = Some v.
  Proof.
    induction e; simpl; intros; 
    repeat match goal with
             | [ H : context [ equiv_dec ?X ?Y ] |- _ ] => 
               destruct (equiv_dec X Y)
             | [ |- context [ equiv_dec ?X ?Y ] ] => 
               destruct (equiv_dec X Y)
             | [ H : context [ match nth_error ?X ?Y with | _ => _ end ] |- _ ] => 
               revert H; case_eq (nth_error X Y); intros
             | [ H : nth_error _ _ = _ , H' : WellTyped_env _ _ |- _ ] =>
               rewrite (@WellTyped_env_nth_error_Some H' H)
             | [ H : nth_error _ _ = _ |- _ ] =>
              (eapply WellTyped_env_nth_error_Some in H; [ destruct H | eassumption ]) ||
              (eapply WellTyped_env_nth_error_None in H; [ | eassumption ])
             | [ H : _ = _ |- _ ] => rewrite H
             | [ H : match ?X with 
                       | _ => _ 
                     end = true |- _ ] => destruct X; try congruence
             | [ |- _ ] => unfold lookupAs in *; simpl in *
        end; eauto; try congruence.
    { unfold equiv in *; subst.
      eapply Forall2_nth_error_L in WT_funcs; eauto. destruct WT_funcs. intuition. rewrite H3.
      destruct H4. rewrite H4 in *; rewrite H2 in *. rewrite EquivDec_refl_left. 
      revert H1. destruct x; simpl in *. generalize Denotation0. generalize Domain0. revert H. clear.
      induction 1; simpl; intros.
      destruct Domain0; eauto. congruence.
      destruct Domain0; try congruence.
      revert H1. case_eq (is_well_typed x t); intros; try congruence.
      apply H in H1. destruct H1. rewrite H1. eapply IHForall; auto. }
    { apply andb_true_iff in H. intuition. apply IHe1 in H0. apply IHe2 in H1.
      destruct H0. destruct H1. rewrite H. rewrite H0. eauto. }
    { apply IHe in H. destruct H; rewrite H; eauto. }
  Qed.    

  Theorem is_well_typed_typeof : forall e t, 
    is_well_typed e t = true -> typeof e = Some t.
  Proof.
    induction e; simpl; intros;
      repeat (progress (unfold equiv in *; subst) ||
        match goal with
          | [ H : context [ equiv_dec ?X ?Y ] |- _ ] => destruct (equiv_dec X Y); try congruence
          | [ H : context [ match nth_error ?X ?Y with | _ => _ end ] |- _ ] => 
            revert H; case_eq (nth_error X Y); intros; try congruence
          | [ H : match ?X with
                    | _ => _
                  end = true |- _ ] => destruct X; try congruence
        end); auto.
  Qed.
  End type_system.
 
  Lemma expr_seq_dec_Equal : forall t1 t2 e1 f1 e2 f2,
    t1 = t2
    -> e1 = e2
    -> f1 = f2
    -> Equal t1 e1 f1 = Equal t2 e2 f2.
    congruence.
  Qed.

  Lemma expr_seq_dec_Not : forall e1 e2,
    e1 = e2
    -> Not e1 = Not e2.
    congruence.
  Qed.

  Definition get_Eq (t : tvar) : forall x y : tvarD t, bool :=
    match t as t return forall x y : tvarD t, bool with
      | tvProp => fun _ _ => false
      | tvType t => 
        match nth_error types t as k 
          return forall x y : match k with
                                | Some t => Impl t
                                | None => Empty_set
                              end, bool
          with
          | None => fun x _ => match x with end
          | Some t => Eqb t
        end 
    end.

  Definition const_seqb  t t' (c : tvarD t) (c' : tvarD t'): bool. 
  case_eq (tvar_seqb t t'). 
  intros. 
  apply tvar_seqb_correct in H. subst. 
  apply (tvar_val_seqb _ c c'). 
  intros _; apply false. 
  Defined. 

  Fixpoint expr_seq_dec (a b : expr) : bool :=
          match a,b  with 
      | Const t c , Const t' c' =>      
          const_seqb t t' c c'
      | Var x , Var y => 
          EqNat.beq_nat x y 
      | UVar x , UVar y => 
          EqNat.beq_nat x y 
      | Func x xs , Func y ys =>
        match Peano_dec.eq_nat_dec x y with
          | left pf =>
              (fix seq_dec' a b : bool :=
                     match a, b with  
                       | nil , nil => true
                       | x :: xs , y :: ys => 
                           if  expr_seq_dec x y then 
                             seq_dec' xs ys                             
                           else false
                       | _ , _ => false
              end) xs ys     
          | right _ => false
        end
      | Equal t1 e1 f1 , Equal t2 e2 f2 =>
          (tvar_seqb t1 t2) && expr_seq_dec e1 e2 && expr_seq_dec f1 f2
      | Not e1 , Not e2 =>
        expr_seq_dec e1 e2 
      | _ , _ => false
    end.
  
  Lemma expr_seq_dec_correct (a b : expr) :  expr_seq_dec a b = true -> a = b. 
  Proof. 
  Admitted. 

  (* This is used by the tactic build_default_type *)
  (* Global Instance SemiDec_expr : SemiDec expr.
  constructor. intros a b. case_eq (expr_seq_dec a b).
  intros H; refine (Some (expr_seq_dec_correct _ _ H)). 
  intros _; apply None. 
  Defined. *)

  (** lift the "real" variables in the range [a,...)
   ** to the range [a+b,...)
   **)
  Fixpoint liftExpr (a b : nat) (e : expr) : expr :=
    match e with
      | Const t' c => Const t' c
      | Var x => 
        if NPeano.ltb x a
        then Var x
        else Var (x + b)
      | UVar x => UVar x
      | Func f xs => 
        Func f (map (liftExpr a b) xs)
      | Equal t e1 e2 => Equal t (liftExpr a b e1) (liftExpr a b e2)
      | Not e1 => Not (liftExpr a b e1)
    end.


  Fixpoint liftExprU (a b : nat) (e : expr (*(uvars' ++ uvars) vars*)) 
    : expr (*(uvars' ++ ext ++ uvars) vars*) :=
    match e with
      | UVar x => 
        if NPeano.ltb a x
        then UVar x
        else UVar (x + b)
      | Var v => Var v
      | Const t x => Const t x 
      | Func f xs => 
        Func f (map (liftExprU a b) xs)
      | Equal t e1 e2 => Equal t (liftExprU a b e1) (liftExprU a b e2)
      | Not e1 => Not (liftExprU a b e1)
    end.

  (** This function replaces "real" variables [a, b) with existential variables (c,...)
   ** TODO: the "b" parameter isn't really used!
   **)
  Fixpoint exprSubstU (a b c : nat) (s : expr (*a (b ++ c ++ d)*)) {struct s}
      : expr (* (c ++ a) (b ++ d) *) :=
      match s with
        | Const _ t => Const _ t
        | Var x =>
          if NPeano.ltb x a 
          then Var x
          else if NPeano.ltb x b
               then UVar (c + x - a)
               else Var (x + a - b)
        | UVar x => UVar x
        | Func f args => Func f (map (exprSubstU a b c) args)
        | Equal t e1 e2 => Equal t (exprSubstU a b c e1) (exprSubstU a b c e2)
        | Not e1 => Not (exprSubstU a b c e1)
      end.

  Lemma nth_error_length : forall T (ls ls' : list T) n,
    nth_error (ls ++ ls') (n + length ls) = nth_error ls' n.
  Proof.
    induction ls; simpl; intros.
    rewrite Plus.plus_0_r. auto.
    cutrewrite (n + S (length ls) = S n + length ls); [ | omega ]. simpl. auto.
  Qed.

  Lemma liftExpr_0 : forall a (b : expr), liftExpr a 0 b = b.
  Proof.
    induction b; simpl; intros; auto.
    destruct (NPeano.ltb x a); f_equal; omega.
    f_equal. generalize dependent H. clear. induction 1. auto.
    simpl; f_equal; auto.
    rewrite IHb1; rewrite IHb2. reflexivity.
    f_equal. auto.
  Qed.

  Lemma liftExpr_combine : forall (e : expr) a b c,
    liftExpr a b (liftExpr a c e) = liftExpr a (c + b) e.
  Proof.
    induction e; intros; simpl; repeat match goal with
                                         | [ H : _ |- _ ] => rewrite H
                                       end; try reflexivity. 
    consider (NPeano.ltb x a); simpl.
    consider (NPeano.ltb x a); auto. intros; exfalso; auto.
    consider (NPeano.ltb (x + c) a). intros; exfalso; omega. intros; f_equal; omega.
    
    f_equal. rewrite map_map. induction H; simpl; auto.
    rewrite H. f_equal; auto.
  Qed.            

  (** first variable in the list is the first one quantified
   **)
  Fixpoint forallEach (ls : variables) : (env -> Prop) -> Prop :=
    match ls with
      | nil => fun cc => cc nil
      | a :: b => fun cc =>
        forall x : tvarD a, forallEach b (fun r => cc (existT _ a x :: r))
    end.

  Theorem forallEach_sem : forall ls P,
    forallEach ls P <-> (forall env, map (@projT1 _ _) env = ls -> P env).
  Proof.
    induction ls; simpl; split; intros.
      destruct env0; auto. simpl in *; congruence.
      eapply H; reflexivity.

      destruct env0; simpl in *; try congruence.
      inversion H0; clear H0; subst. specialize (H (projT2 s)).
      eapply IHls in H; eauto. destruct s; simpl in *; auto.

      eapply IHls. intros. subst. eapply H. auto.
  Qed.

  (** first variable in the list is the first one quantified
   **)
  Fixpoint existsEach (ls : variables) : (env.env -> Prop) -> Prop :=
    match ls with
      | nil => fun cc => cc nil
      | a :: b => fun cc =>
        exists x : tvarD a, existsEach b (fun r => cc (existT _ a x :: r))
    end.

  Theorem existsEach_sem : forall ls P,
    existsEach ls P <-> (exists env, map (@projT1 _ _) env = ls /\ P env).
  Proof.
    induction ls; simpl; split; intros.
      exists nil; auto.
      destruct H. destruct x; intuition (simpl in *; eauto; congruence).

      destruct H. eapply IHls in H. destruct H.
      intuition; subst. eexists; eauto. split; eauto. reflexivity.

      destruct H. intuition; subst. destruct x; simpl in *; try congruence.
      destruct s. simpl in *. inversion H0; clear H0; subst.
      exists t. eapply IHls. eauto.
  Qed.

  Lemma existsEach_ext : forall vs (F G : env.env -> Prop), 
    (forall ls, F ls -> G ls) ->
    existsEach vs F -> existsEach vs G.
  Proof.
    clear. induction vs; simpl; intros; auto.
    destruct H0. exists x. eapply IHvs. 2: eassumption.
    intros. simpl in *. auto.
  Qed.

  Lemma existsEach_projT1_env' : forall (F : env.env -> Prop) vars r, 
    F (r ++ vars) ->
    existsEach (map (@projT1 _ _) vars) (fun x => F (r ++ x)).
  Proof.
    clear. induction vars; simpl; intros; auto.
    exists (projT2 a). specialize (IHl (r ++ a :: nil)). destruct a; simpl in *.
    repeat rewrite app_ass in *. simpl in *.
    apply IHl in H.
    eapply existsEach_ext. 2: eapply H. intros; simpl in *.      
    rewrite app_ass in *; simpl in *; auto.
  Qed.

  Lemma existsEach_projT1_env : forall (F : env.env -> Prop) vars,
    F vars ->
    existsEach (map (@projT1 _ _) vars) F.
  Proof.
    clear. intros. generalize (existsEach_projT1_env' F vars nil H). intros.
    eapply existsEach_ext; try eassumption. simpl. auto.
  Qed.

  Lemma existsEach_app : forall (P : env.env -> Prop) ls' ls,
    existsEach (ls ++ ls') P <->
    existsEach ls (fun e => existsEach ls' (fun e' => P (e ++ e'))).
  Proof.
    clear. split; generalize dependent P; generalize dependent ls; induction ls; simpl; intros;
      try solve [ eapply existsEach_ext; eauto ].

      destruct H.
      exists x. eapply IHls in H. eauto.
      destruct H; exists x. eapply IHls. eauto.
  Qed.

  Section Provable.
    Definition Provable (e : expr) : Prop :=
      match exprD e tvProp with
        | None => False
        | Some p => p
      end.

    Section all_provable.
      Variable ctor : Prop -> Prop -> Prop.
      Variable base : Prop.

      Fixpoint AllProvable_gen (es : list expr) : Prop :=
        match es with
          | nil => base
          | e :: es => ctor (Provable e) (AllProvable_gen es)
        end.
    End all_provable.

    Definition AllProvable := AllProvable_gen and True.
    Definition AllProvable_impl := AllProvable_gen Basics.impl.
    Definition AllProvable_and := AllProvable_gen and.

    Lemma AllProvable_app : forall a b, 
      AllProvable a -> 
      AllProvable b ->
      AllProvable (a ++ b).
    Proof.
      induction a; simpl; intuition auto.
    Qed.

    Lemma AllProvable_app' : forall b a, 
      AllProvable (a ++ b) ->
      AllProvable a /\ AllProvable b.
    Proof.
      induction a; simpl; try solve [ intuition auto ]; intros.
    Qed.
    
    Lemma Provable_ValidProp : forall goal, Provable goal -> ValidProp goal.
      unfold Provable, ValidProp in *; intros;
        repeat match goal with
                 | [ _ : match ?E with None => _ | Some _ => _ end |- _ ] =>
                   destruct E
               end; intuition eauto.
    Qed.

  End Provable.

End env.

Lemma nth_error_app_success : forall T ls' (ls : list T) n v,
  nth_error ls n = Some v ->
  nth_error (ls ++ ls') n = Some v.
Proof.
  clear. induction ls; destruct n; simpl; intros; unfold value, error in *; try congruence; auto.
Qed.

Lemma exprD_weaken : forall types (fs : functions types) uvars vars vars' e t v,
  exprD fs uvars vars e t = Some v ->
  exprD fs uvars (vars ++ vars') e t = Some v.
Proof.
  clear. induction e; simpl; intros; auto;
  repeat match goal with
           | [ H : match ?X with
                     | _ => _
                   end = _ |- _ ] => revert H; case_eq X; intros; try congruence
           | [ H : _ |- _ ] => rewrite H
         end; auto.
  Focus 2.
  unfold Equivalence.equiv in *. subst.
  destruct s; simpl in *.
  clear H0. generalize dependent Denotation. generalize dependent Domain0.
  generalize dependent l. clear. induction l; simpl; intros; destruct Domain0; auto.
  inversion H; clear H; subst.
  revert H2. case_eq (exprD fs uvars vars a t); intros.
  erewrite H3 by eassumption. eauto. congruence.

  Focus 2.
  generalize dependent t0. destruct t0; intros; try congruence.
  repeat match goal with
           | [ H : match ?X with
                     | _ => _
                   end = _ |- _ ] => revert H; case_eq X; intros; try congruence
           | [ H : _ |- _ ] => rewrite H
         end; auto.
  erewrite IHe1; try eauto.
  erewrite IHe2; try eauto. 

  unfold lookupAs in *.
  cutrewrite (nth_error (vars ++ vars') x = nth_error vars x); auto.
  
  revert H; case_eq (nth_error vars x); intros.
  eapply nth_error_app_success; auto.
  congruence.
  destruct t; try congruence. 
  revert H; case_eq (exprD fs uvars vars e tvProp); intros; try congruence.
  erewrite IHe; eauto.
Qed.


Lemma liftExpr_ext : forall types (funcs : functions types) EG G G' G'' e t,
  exprD funcs EG (G'' ++ G) e t = exprD funcs EG (G'' ++ G' ++ G) (liftExpr (length G'') (length G') e) t.
Proof.
  clear. induction e; simpl; intros; try reflexivity.
  consider (NPeano.ltb x (length G'')); intros Hx. 
  simpl. unfold lookupAs. 
  revert G; revert G'. generalize dependent x. generalize dependent G''.
  induction G''; simpl; intros.
  exfalso; omega.
  destruct x. reflexivity. simpl. erewrite <- IHG''. reflexivity. omega.
  simpl. unfold lookupAs. 

  cutrewrite (x = (x - length G'') + length G''). 
  cutrewrite ((x - length G'') + length G'' + length G' = (x - length G'') + length G' + length G''). 2: omega.
  repeat rewrite nth_error_length. reflexivity.
  rewrite Plus.plus_comm. rewrite <- Minus.le_plus_minus; auto. omega.

  destruct (nth_error funcs f); auto. destruct (equiv_dec (Range s) t); auto.
  unfold Equivalence.equiv in e. subst. destruct s; simpl in *.
  generalize dependent Domain0. induction H; intros; auto.
  simpl. destruct Domain0; auto. rewrite H.
  match goal with
    | [ |- match ?X with
             | Some _ => _ | None => _ 
           end _ _ = _ ] => destruct X
  end. eauto.

  auto.

  destruct t0; auto. rewrite IHe1. rewrite IHe2. auto.

  destruct t; auto. rewrite IHe. reflexivity.
Qed.

Section exists_subst.
  Variable types : list type.
  Variable funcs : functions types.
  Variable U1 : env types.
  
  (* Unification variables corresponding to genuine Coq existentials *)
  Fixpoint exists_subst (CU : env types)
    (U : list (tvar * option (expr types)))
    : (env types -> Prop) -> Prop :=
    match U , CU with
      | nil , nil => fun cc => cc nil
      | (t,v) :: U' , existT t' v' :: CU'  => fun cc =>
        match v with
          | None => 
            exists v : tvarD types t, exists_subst (match CU with
                                                      | nil => nil
                                                      | _ :: CU' => CU'
                                                    end) U' (fun z => cc (existT _ t v :: z))
          | Some v => 
            match exprD funcs CU U1 v t' with
              | None => False
              | Some v1 => v' = v1 /\ exists_subst CU' U' (fun z => cc (existT _ t' v1 :: z))
            end
        end
      | _ , _ => fun _ => False
    end.

Lemma exists_subst_exists : forall (B : list (tvar * option (expr types))) CU P,
  exists_subst CU B P ->
  exists C, P C.
Proof.
  clear. induction B; simpl; intros.
    destruct CU. eauto.
    contradiction.
   
    destruct a; destruct CU; simpl in *; try contradiction.
    destruct s; destruct o. 
    match goal with
      | [ H : match ?X with | None => _ | Some _ => _ end |- _ ] => destruct X
    end; intuition; subst; auto.
    apply IHB in H1. destruct H1. eauto.
    destruct H. eapply IHB in H. destruct H; eauto.
Qed.

End exists_subst.

(** Use this function to get an environment extension
 ** - n is the length of the old environment
 **)
Definition env_ext (T : Type) n (ls : list T) : list T :=
  firstn (length ls - n) ls.

(** TODO: There probably need to be some facts about this... **)
  

Implicit Arguments Const [ types t ].
Implicit Arguments Var [ types ].
Implicit Arguments UVar [ types ].
Implicit Arguments Func [ types ].


Module ReifyExpr.
(** Tactics **)
Require Import Reflect.

Ltac lift_signature s nt :=
  let d := eval simpl Domain in (Domain s) in
  let r := eval simpl Range in (Range s) in
  let den := eval simpl Denotation in (Denotation s) in
  constr:(@Sig nt d r den).

Ltac lift_signatures fs nt :=
  let f sig := 
    lift_signature sig nt 
  in
  map_tac (signature nt) f fs.
(*
Goal True.
  refine (
    let ts := {| Impl := nat ; Eq := fun _ _ => None |} :: nil in
    let ts' := {| Impl := nat ; Eq := fun _ _ => None |} ::
      {| Impl := bool ; Eq := fun _ _ => None |} :: nil in
    let fs :=
      {| Domain := tvType 0 :: tvType 0 :: nil
       ; Range  := tvType 0
       ; Denotation := plus : functionTypeD (map (tvarD ts) (tvType 0 :: tvType 0 :: nil))
     (tvarD ts (tvType 0))
      |} :: (@nil (signature ts)) in
    _).
  match goal with
    | [ |- _ ] => 
      let fs := eval unfold fs in fs in
      let r := lift_signatures fs ts' in
      pose (fs' := r)
  end.
Abort.      
*) 

Definition default_type (T : Type) : type. 
Proof. 
  refine ({| Impl := T
             ; Eqb := fun _ _ => false
             ; Eqb_correct := _
          |}). abstract (discriminate). 
Defined. 

(* TODO: remove this type-class... *)
Global Instance SemiDec_nat : SemiDec nat. 
constructor. intros.
destruct (Peano_dec.eq_nat_dec a b). refine (Some e). refine (None). 
Defined. 
      
Definition type_of_ReificationHint T : ReificationHint.Pkg T -> type. 
intros [Eqb EqbH]; apply (@Typ T Eqb EqbH). 
Defined. 

Global Instance ReificationHintNat : ReificationHint.Pkg nat :=
           ReificationHint.mk_Pkg EqNat.beq_nat EqNat.beq_nat_true. 

Ltac build_default_type T := 
  match goal with
    | [ |- _ ] => let C := constr:(_ : ReificationHint.Pkg T) in 
                 let t := constr:(type_of_ReificationHint C) in 
                   t
    | [ |- _ ] => constr:(default_type T)
  end.

Ltac extend_type T types :=
  match T with
    | Prop => types
    | _ => 
      let rec find types :=
        match types with
          | nil => constr:(false)
          | ?a :: ?b =>
            match unifies (Impl a) T with
              | true => constr:(true)
              | false => find b
            end
        end
      in
      match find types with
        | true => types
        | _ =>
          let D := build_default_type T in
          eval simpl app in (types ++ (D :: @nil type))
      end
  end.

(* extend a reflected type list with new raw types
 * - Ts is a list of raw types
 * - types is a list of reflected types
 *)
Ltac extend_all_types Ts types :=
  match Ts with
    | nil => types
    | ?a :: ?b =>
      let types := extend_type a types in
        extend_all_types b types
  end.

Record VarType (t : Type) : Type :=
  { open : t }.
Definition openUp T U (f : T -> U) (vt : VarType T) : U :=
  f (open vt).

(** collect the raw types from the given expression.
 ** - e is the expression to collect types from
 ** - types is a value of type [list Type]
 **   (make sure it is NOT [list Set])
 **)
Ltac collectTypes_expr isConst e Ts :=
  match e with
    | fun x => (@openUp _ ?T _ _) =>
      let v := constr:(T:Type) in
        cons_uniq v Ts
    | fun x => ?e =>
      collectTypes_expr isConst e Ts
    | _ =>
      let rec bt_args args Ts :=
        match args with
          | tt => Ts
          | (?a, ?b) =>
            let Ts := collectTypes_expr isConst a Ts in
              bt_args b Ts
        end
      in
      let cc _ Ts' args := 
        let T := 
          match e with 
            | fun x : VarType _ => _ => 
              match type of e with
                | _ -> ?T => T
              end
            | _ => type of e
          end
        in
        let Ts' :=
          let v := constr:(T : Type) in
          cons_uniq v Ts'
        in
        let Ts := append_uniq Ts' Ts in
        bt_args args Ts
      in
      refl_app cc e
  end.

Ltac collectAllTypes_expr isConst Ts goals :=
  match goals with
    | tt => Ts
    | (?a, ?b) =>
      let ts := collectTypes_expr isConst a Ts in
        collectAllTypes_expr isConst ts b
  end.

Ltac collectAllTypes_func Ts T :=
  match T with
    | ?t -> ?T =>
      let t := constr:(t : Type) in
      let Ts := cons_uniq t Ts in
      collectAllTypes_func Ts T
    | forall x , _ => 
        (** Can't reflect types for dependent function **)
      fail 100 "can't reflect types for dependent function!"
    | ?t =>
      let t := constr:(t : Type) in
      cons_uniq t Ts
  end.

Ltac collectAllTypes_funcs Ts Fs :=
  match Fs with
    | tt => Ts
    | (?Fl, ?Fr) =>
      let Ts := collectAllTypes_funcs Ts Fl in
      collectAllTypes_funcs Ts Fr
    | ?F =>
      let T := type of F in
      collectAllTypes_func Ts T
  end.

Ltac collect_props shouldReflect :=
  let rec collect skip :=
    match goal with
      | [ H : ?X |- _ ] => 
        match shouldReflect X with
          | true =>
            match hcontains H skip with
              | false =>
                let skip := constr:((H, skip)) in
                collect skip
            end
        end
      | _ => skip
    end
  in collect tt.

Ltac props_types ls :=
  match ls with
    | tt => constr:(@nil Prop)
    | (?H, ?ls) =>
      let P := type of H in
      let rr := props_types ls in
      constr:(P :: rr)
  end.

Ltac props_proof ls :=
  match ls with
    | tt => I
    | (?H, ?ls) => 
      let rr := props_proof ls in
      constr:(conj H rr)
  end.
    
(*
Ltac collectAllTypes_props shouldReflect isConst Ts :=
  let rec collect Ts skip :=
    match goal with
      | [ H : ?X |- _ ] => 
        match reflectable shouldReflect X with
          | true =>
            match hcontains H skip with
              | false => 
                let Ts := collectTypes_expr isConst X Ts in
                let skip := constr:((H, skip)) in
                collect Ts skip
            end
        end
      | _ => Ts
    end
  in collect Ts tt.
*)

(** find x inside (map proj xs) and return its position as a natural number.
 ** This tactic fails if x does not occur in the list
 ** - proj is a gallina function.
 **)
Ltac indexOf_nat proj x xs :=
  let rec search xs :=
    match eval hnf in xs with
      | ?X :: ?XS =>
        match unifies (proj X) x with
          | true => constr:(0)
          | false => 
            let r := search XS in
              constr:(S r)
        end
    end
    in search xs.

(** specialization of indexOf_nat to project from type **)
Ltac typesIndex x types :=
  indexOf_nat Impl x types.

(** given the list of types (of type [list type]) and a raw type
 ** (of type [Type]), return the [tvar] that corresponds to the
 ** given raw type.
 **)
Ltac reflectType types t :=
  match t with
    | Prop => constr:(tvProp)
    | _ =>
      let i := typesIndex t types in
      let r := constr:(tvType i) in
      r
    | _ =>
      fail 10000 "couldn't find " t " inside types"
  end.  
      
(** essentially this is [map (reflectType types) ts] **)
Ltac reflectTypes_toList types ts :=
  match eval hnf in ts with 
    | nil => constr:(@nil tvar)
    | ?T :: ?TS =>
      let i := typesIndex T types in
      let rest := reflectTypes_toList types TS in
      constr:(@cons tvar (tvType i) rest)
  end.

(** Build a signature for the given function 
 ** - types is a list of reflected types, i.e. type [list type]
 ** the type of f can NOT be dependent, i.e. it must be of the
 ** form, 
 **   _ -> ... -> _
 **)
Ltac reify_function types f :=
  let T := type of f in
  let rec refl dom T :=
    match T with
        (* no dependent types *)
      | ?A -> ?B =>
        let A := reflectType types A in
        let dom := constr:(A :: dom) in
        refl dom B 
      | ?R =>
        let R := reflectType types R in
        let dom := eval simpl rev in (rev dom) in
        constr:(@Sig types dom R f)
    end
  in refl (@nil tvar) T.

(** lookup a function in a list of reflected functions.
 ** if the function does not exist in the list, the list is extended.
 ** - k is the continutation and is passed the resulting list of functions
 **   and the index of f in the list.
 **   (all elements passed into funcs' are preserved in order)
 **)
Ltac getFunction types f funcs' k :=
  let rec lookup funcs acc :=
    match funcs with
      | nil =>
        let F := reify_function types f in
        let funcs := eval simpl app in (funcs' ++ (F :: nil)) in
        k funcs acc
      | Sig _ _ _ ?F :: ?FS =>
        match F with
          | f => k funcs' acc
          | natToW =>
            match f with
              | natToWord 32 => k funcs' acc
            end
          | natToWord 32 =>
            match f with
              | natToW => k funcs' acc
            end
          | _ =>
            let acc := constr:(S acc) in
            lookup FS acc
        end
    end
  in lookup funcs' 0.

Ltac getAllFunctions types funcs' fs :=
  match fs with
    | tt => funcs'
    | ?F =>
      getFunction types F funcs' ltac:(fun funcs _ => funcs)
    | ( ?fl , ?fr ) =>
      let funcs := getAllFunctions types funcs' fl in
      getAllFunctions types funcs fr
  end.

Ltac getVar' idx :=
  match idx with
    | fun x => x => constr:(0)
    | fun x => @openUp _ _ (@snd _ _) (@?X x) =>
      let r := getVar' X in
      constr:(S r)
    | _ => idtac "couldn't find variable! [1]" idx
  end.

Ltac getVar idx :=
  (** NOTE: reification as indicies **)
  match idx with
    | fun x => @openUp _ _ (@fst _ _) (@?X x) =>
      getVar' X
    | fun x => @openUp _ _ (@snd _ _) (@?X x) =>
      let r := getVar X in
      constr:(S r)
    | _ => idtac "couldn't find variable! [2]" idx
  end.

Ltac get_or_extend_var types all t v k :=
  let rec doIt rem acc :=
    match rem with
      | nil => 
        (** NOTE: reification as levels **)
        let all := 
          eval simpl app in (all ++ (@existT tvar (tvarD types) t v) :: nil)
        in
        k all acc
      | @existT _ _ _ ?v' :: _ => constr_eq v v' ; k all acc
      | _ :: ?rem =>
        let acc := constr:(S acc) in
        doIt rem acc
    end
  in
  doIt all 0.

(** reflect an expression gathering the functions at the same time.
 ** - k is the continuation and is passed the list of reflected
 **   uvars, functions, and the reflected expression.
 **)
Ltac reify_expr isConst e types funcs uvars vars k :=
  let rec reflect e funcs uvars k :=
    match e with
      | ?X => is_evar X ;
        (** this is a unification variable **)
        let t := type of X in
        let T := reflectType types t in
        get_or_extend_var types uvars T X ltac:(fun uvars v =>
          let r := constr:(@UVar types v) in
          k uvars funcs r)
      | fun _ => ?X => is_evar X ;
        (** TODO : test this **)
        (** this is a unification variable **)
        let t := type of X in
        let T := reflectType types t in
        get_or_extend_var types uvars T X ltac:(fun uvars v =>
          let r := constr:(@UVar types v) in
          k uvars funcs r)
      | fun x => (@openUp _ _ _ _) =>
        (** this is a variable **)
        let v := getVar e in
        let r := constr:(@Var types v) in
        k uvars funcs r

      | @eq ?T ?e1 ?e2 =>
        let T := reflectType types T in
          reflect e1 funcs uvars ltac:(fun uvars funcs e1 =>
            reflect e2 funcs uvars ltac:(fun uvars funcs e2 =>
              k uvars funcs (Equal T e1 e2)))
      | fun x => @eq ?T (@?e1 x) (@?e2 x) =>
        let T := reflectType types T in
          reflect e1 funcs uvars ltac:(fun uvars funcs e1 =>
            reflect e2 funcs uvars ltac:(fun uvars funcs e2 =>
              k uvars funcs (Equal T e1 e2)))

      | not ?e1 =>
        reflect e1 funcs uvars ltac:(fun uvars funcs e1 =>
          k uvars funcs (Not e1))
      | ?e1 -> False =>
        reflect e1 funcs uvars ltac:(fun uvars funcs e1 =>
          k uvars funcs (Not e1))
      | fun x => not (@?e1 x) =>
        reflect e1 funcs uvars ltac:(fun uvars funcs e1 =>
          k uvars funcs (Not e1))
      | fun x => @?e1 x -> False =>
        reflect e1 funcs uvars ltac:(fun uvars funcs e1 =>
          k uvars funcs (Not e1))
      | fun x => ?e =>
        reflect e funcs uvars k
      | _ =>
        let rec bt_args uvars funcs args k :=
          match args with
            | tt => 
              let v := constr:(@nil (@expr types)) in
              k uvars funcs v
            | (?a, ?b) =>
              reflect a funcs uvars ltac:(fun uvars funcs a =>
                bt_args uvars funcs b ltac:(fun uvars funcs b =>
                  let r := constr:(@cons (@expr types) a b) in
                  k uvars funcs r))
          end
        in
        let cc f Ts args :=
          getFunction types f funcs ltac:(fun funcs F =>
            bt_args uvars funcs args ltac:(fun uvars funcs args =>
              let r := constr:(@Func types F args) in 
              k uvars funcs r))
        in
        match e with
          | _ =>
            match isConst e with
              | true =>
                let ty := type of e in
                let ty := reflectType types ty in
                let r := constr:(@Const types ty e) in
                k uvars funcs r
              | false => refl_app cc e
            end
          | _ => refl_app cc e
        end
    end
  in reflect e funcs uvars k.

(** collect all the types in es into a list.
 ** it return a value of type [list Type]
 ** NOTE: this function accepts either a tuple or a list for es
 **) 
Ltac collectTypes_exprs isConst es Ts := 
  match es with
    | tt => Ts
    | nil => Ts
    | (?e, ?es) =>
      let Ts := collectTypes_expr ltac:(isConst) e Ts in
      collectTypes_exprs ltac:(isConst) es Ts
    | ?e :: ?es =>
      let Ts := collectTypes_expr ltac:(isConst) e Ts in
      collectTypes_exprs ltac:(isConst) es Ts
  end.

(** reflect all the expressions in a list.
 ** - k :: env types -> functions types -> list (expr types)
 ** NOTE: this function accepts either a tuple or a list for es
 **) 
Ltac reify_exprs isConst es types funcs uvars vars k :=
  match es with
    | tt => k uvars funcs (@nil (expr types))
    | nil => k uvars funcs (@nil (expr types))
    | (?e, ?es) =>
      reify_expr ltac:(isConst) e types funcs uvars vars ltac:(fun uvars funcs e =>
        reify_exprs ltac:(isConst) es types funcs uvars vars ltac:(fun uvars funcs es =>
          let res := constr:(e :: es) in
          k uvars funcs res))
    | ?e :: ?es =>
      reify_expr ltac:(isConst) e types funcs uvars vars ltac:(fun uvars funcs e =>
        reify_exprs ltac:(isConst) es types funcs uvars vars ltac:(fun uvars funcs es =>
          let res := constr:(e :: es) in
          k uvars funcs res))
  end.
End ReifyExpr.