Require Import List DepList.
Require Import EqdepClass.
Require Import IL Word.
Require Import Bool.
Require PropX.

Set Implicit Arguments.

Section env.
  Record type := Typ {
    Impl : Type;
    Eq : forall x y : Impl, option (x = y)
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
   ; Eq := fun x _ => match x with end
   |}.

  Definition typeFor (t : tvar) : type :=
    match t with
      | tvProp => {| Impl := Prop ; Eq := fun _ _ => None |}
      | tvType t => 
        match nth_error types t with
          | None => EmptySet_type
          | Some v => v 
        end
    end.

  Definition tvar_val_sdec (t : tvar) : forall (x y : tvarD t), option (x = y) :=
    match t as t return forall (x y : tvarD t), option (x = y) with
      | tvProp => fun _ _ => None
      | tvType t => 
        match nth_error types t as k return forall x y : match k with 
                                                           | None => Empty_set
                                                           | Some t => Impl t
                                                         end, option (x = y) with
          | None => fun x _ => match x with end
          | Some t => fun x y => match Eq t x y with
                                   | None => None
                                   | Some pf => Some pf
                                 end
        end

    end.

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
  | Var : forall x : var, expr
  | UVar : forall x : uvar, expr
  | Func : forall f : func, list expr -> expr
  | Equal : tvar -> expr -> expr -> expr
  | Not : expr -> expr.

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

  Fixpoint typeof (e : expr) : option tvar :=
    match e with
      | Const t _ => Some t
      | Var x => match nth_error var_env x with
                   | None => None
                   | Some (existT t _) => Some t
                 end
      | UVar x => match nth_error meta_env x with
                    | None => None
                    | Some (existT t _) => Some t
                  end
      | Func f _ => match nth_error funcs f with
                      | None => None
                      | Some r => Some (Range r)
                    end
      | Equal _ _ _
      | Not _ => Some tvProp
    end.

  Theorem exprD_principal : forall e t, exprD e t <> None
    -> match typeof e with
         | None => False
         | Some t' => exprD e t' <> None
       end.
  Proof.
    induction e; simpl; unfold lookupAs; intros;
      repeat (simpl in *; try congruence; 
        match goal with
          | [ |- context[nth_error ?E ?F] ] => destruct (nth_error E F) as [ [ ] | ]
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
        end).
    unfold equiv in *. subst. auto.
  Qed.

  Section All2.
    Variable X Y : Type.
    Variable F : X -> Y -> bool.

    Fixpoint all2 (xs : list X) (ys : list Y) : bool :=
      match xs , ys with
        | nil , nil => true
        | x :: xs, y :: ys => if F x y then all2 xs ys else false
        | _ , _ => false
      end.
  End All2.

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

  Fixpoint is_well_typed (e : expr) (t : tvar) {struct e} : bool :=
    match e with 
      | Const t' _ => 
        if equiv_dec t' t then true else false
      | Var x => if lookupAs var_env t x then true else false 
      | UVar x => if lookupAs meta_env t x then true else false 
      | Func f xs => 
        match nth_error funcs f with
          | None => false
          | Some f =>
            if equiv_dec t (Range f) then 
              all2 is_well_typed xs (Domain f)
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

  Definition well_typed (e : expr) : option tvar :=
    match e with 
      | Const t' _ => Some t'
      | Var x => 
        match nth_error var_env x with
          | None => None
          | Some z => Some (projT1 z)
        end
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

  Definition ValidProp (e : expr) := 
    exists v, exprD e tvProp = Some v.
  Definition ValidExp (e : expr) := 
    exists t, exists v, exprD e t = Some v.

  Theorem is_well_typed_correct : forall e t, 
    is_well_typed e t = true ->
    exists v, exprD e t = Some v.
  Proof.
    clear. induction e; simpl; intros; 
    repeat match goal with
             | [ H : context [ equiv_dec ?X ?Y ] |- _ ] => 
               destruct (equiv_dec X Y)
             | [ |- context [ equiv_dec ?X ?Y ] ] => 
               destruct (equiv_dec X Y)
             | [ H : context [ lookupAs ?X ?Y ?Z ] |- _ ] => 
               destruct (lookupAs X Y Z)
             | [ H : context [ nth_error ?X ?Y ] |- _ ] => destruct (nth_error X Y)
        end; eauto; try congruence.
    generalize e0. rewrite <- e0. unfold "===". uip_all.
    generalize dependent (Denotation s). generalize dependent (Domain s).
    generalize (Range s). generalize dependent l. clear. 
    induction l; simpl; intros.
      destruct l; eauto; congruence.
      destruct l0; try congruence.
      generalize dependent H0. inversion H; clear H; subst. specialize (H2 t0). generalize dependent H2.
      case_eq (is_well_typed a t0); intros; try congruence.
      destruct H2; auto. rewrite H1. eauto.
    destruct t0; try discriminate.
      apply andb_true_iff in H; intuition.
      destruct (IHe1 _ H0) as [ ? Heq ]; rewrite Heq.
      destruct (IHe2 _ H1) as [ ? Heq' ]; rewrite Heq'.
      eauto.
    specialize (IHe tvProp).
      destruct t; intuition.
      destruct H0; rewrite H0; eauto.
  Qed.

  Theorem is_well_typed_typeof : forall e t, 
    is_well_typed e t = true -> typeof e = Some t.
  Proof.
    induction e; simpl; intros.
      destruct (equiv_dec t t1); try congruence.
      unfold lookupAs in *. destruct (nth_error var_env x); try congruence.
        destruct s; simpl in *. destruct (equiv_dec x0 t); congruence.
      unfold lookupAs in *. destruct (nth_error meta_env x); try congruence.
        destruct s; simpl in *. destruct (equiv_dec x0 t); congruence.
      destruct (nth_error funcs f); try congruence.
        destruct (equiv_dec t (Range s)); congruence.
      destruct t0; congruence.
      destruct t; congruence.
  Qed.
 
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

  Fixpoint expr_seq_dec (a b : expr) : option (a = b) :=
    match a as a, b as b return option (a = b) with 
      | Const t c , Const t' c' =>
        match t as t , t' as t' return forall (c : tvarD t) (c' : tvarD t'), option (Const t c = Const t' c') with
          | tvType t , tvType t' =>
            match Peano_dec.eq_nat_dec t t' with
              | left pf => 
                match pf in _ = t' return forall (x : tvarD (tvType t)) (y : tvarD (tvType t')), 
                  option (Const (tvType t) x = Const (tvType t') y)
                  with
                  | refl_equal => fun x y =>
                    match tvar_val_sdec _ x y with
                      | None => None
                      | Some pf => Some (match pf in _ = z return Const (tvType t) x = Const (tvType t) z with
                                           | refl_equal => refl_equal
                                         end)  
                    end
                end 
              | right _ => fun _ _ => None
            end
          | _ , _ => fun _ _ => None
        end c c'
      | Var x , Var y => 
        match Peano_dec.eq_nat_dec x y with 
          | left pf => Some match pf in _ = t return Var x = Var t with
                              | refl_equal => refl_equal
                            end
          | right _ => None
        end
      | UVar x , UVar y => 
        match Peano_dec.eq_nat_dec x y with 
          | left pf => Some match pf in _ = t return UVar x = UVar t with
                              | refl_equal => refl_equal
                            end
          | right _ => None
        end
      | Func x xs , Func y ys =>
        match Peano_dec.eq_nat_dec x y with
          | left pf =>
            match (fix seq_dec' a b : option (a = b) :=
              match a as a, b as b return option (a = b) with
                | nil , nil => Some (refl_equal _)
                | x :: xs , y :: ys => 
                  match expr_seq_dec x y with
                    | None => None
                    | Some pf => 
                      match seq_dec' xs ys with
                        | None => None
                        | Some pf' => 
                          match pf in _ = t , pf' in _ = t' return option (x :: xs = t :: t') with
                            | refl_equal , refl_equal => Some (refl_equal _)
                          end
                      end
                  end
                | _ , _ => None
              end) xs ys with
              | None => None
              | Some pf' => Some (match pf in _ = t, pf' in _ = t' return Func x xs = Func t t' with
                                    | refl_equal , refl_equal => refl_equal
                                  end)
            end              
          | right _ => None
        end
      | Equal t1 e1 f1 , Equal t2 e2 f2 =>
        match equiv_dec t1 t2, expr_seq_dec e1 e2, expr_seq_dec f1 f2 with
          | left pf1, Some pf2, Some pf3 => Some (expr_seq_dec_Equal pf1 pf2 pf3)
          | _, _, _ => None
        end
      | Not e1 , Not e2 =>
        match expr_seq_dec e1 e2 with
          | Some pf => Some (expr_seq_dec_Not pf)
          | _ => None
        end
      | _ , _ => None
    end.

  Global Instance SemiDec_expr : SemiDec expr.
    let v := eval cbv delta [ expr_seq_dec ] in expr_seq_dec in
    constructor; exact v.
  Defined.

  (** lift the "real" variables in the range [a,...)
   ** to the range [a+b,...)
   **)
  Fixpoint liftExpr (a b : nat) (e : expr) : expr :=
    match e with
      | Const t' c => Const t' c
      | Var x => 
        if Compare_dec.lt_dec x a
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
        if Compare_dec.lt_dec a x
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
          if Compare_dec.lt_dec x a 
          then Var x
          else if Compare_dec.lt_dec x b
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
    destruct (Compare_dec.lt_dec x a); f_equal; omega.
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
    destruct (Compare_dec.lt_dec x a); simpl.
    destruct (Compare_dec.lt_dec x a); auto. exfalso; auto.
    destruct (Compare_dec.lt_dec (x + c) a). exfalso; omega. f_equal; omega.
    
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

Lemma liftExpr_ext : forall types (funcs : functions types) EG G G' G'' e t,
  exprD funcs EG (G'' ++ G) e t = exprD funcs EG (G'' ++ G' ++ G) (liftExpr (length G'') (length G') e) t.
Proof.
  clear. induction e; simpl; intros; try reflexivity.
  destruct (Compare_dec.lt_dec x (length G'')).
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
 
Ltac build_default_type T := 
  match goal with
    | [ |- _ ] => constr:(@Typ T (@seq_dec T _))
    | [ |- _ ] => constr:({| Impl := T ; Eq := fun _ _ : T => None |})
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

Ltac reflectable shouldReflect P :=
  match P with
    | @PropX.interp _ _ _ _ => false
    | @PropX.valid _ _ _ _ _ => false
    | forall x, _ => false
    | context [ PropX.PropX _ _ ] => false
    | context [ PropX.spec _ _ ] => false
    | _ => match type of P with
             | Prop => shouldReflect P
           end
  end.

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
        match reflectable shouldReflect X with
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
        let all := eval simpl app in (all ++ (@existT tvar (tvarD types) t v) :: nil) in
        k all acc
      | @existT _ _ _ v :: _ => k all acc
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
