(** TODO List
 ** - Merging states
 ** - Lifting expressions to new states
 ** - Unification variables?
 **)
Require Import List Env.
Require Import EqdepClass.

Set Implicit Arguments.

Section env.
  Record type := {
    Impl : Type;
    Eq : forall x y : Impl, option (x = y)
  }.

  Variable types : list type.

  Definition tvar := option (fin types).
  Definition tvarD x := match x with
                          | None => Prop
                          | Some x => Impl (get types x)
                        end.

  Fixpoint functionTypeD (domain : list Type) (range : Type) : Type :=
    match domain with
      | nil => range
      | d :: domain' => d -> functionTypeD domain' range
    end.

  Record signature := {
    Domain : list tvar;
    Range : tvar;
    Denotation : functionTypeD (map tvarD Domain) (tvarD Range)
  }.

  Definition functions := list signature.
  Definition variables := list tvar.

  Variable funcs : functions.
  Variable uvars : variables.
  Variable vars : variables.

  Definition func := fin funcs.
  Definition var := fin vars.
  Definition uvar := fin uvars.

  Inductive expr : tvar -> Type :=
  | Const : forall t : tvar, tvarD t -> expr t
  | Var : forall x : var, expr (get vars x)
  | UVar : forall x : uvar, expr (get uvars x)
  | Func : forall f : func, hlist expr (Domain (get funcs f)) -> expr (Range (get funcs f)).

  Lemma expr_ind_strong : forall (P : forall t, expr t -> Prop),
    (forall (t : tvar) (t0 : tvarD t), P t (Const t t0)) ->
    (forall x : var, P (get vars x) (Var x)) ->
    (forall x : uvar, P (get uvars x) (UVar x)) ->
    (forall (f2 : func) (h : hlist expr (Domain (get funcs f2))),
      hlist_All P h ->
      P (Range (get funcs f2)) (Func f2 h)) ->
    forall (t : tvar) (e : expr t), P t e.
  Proof.
    intros P Hconst Hvar Huvar Hfunc.
    refine (fix expr_ind_strong t e {struct e} : P t e :=
      match e as e in expr t return P t e with
        | Var _ => Hvar _ 
        | Const _ _ => Hconst _ _
        | UVar _ => Huvar _
        | Func _ h  => 
          Hfunc _ _ ((fix prove_sub ls (h : hlist expr ls) : hlist_All P h :=
            match h with
              | HNil => I
              | HCons _ _ e r => conj (expr_ind_strong _ e) (prove_sub _ r)
            end) _ h)
      end).
  Qed.

  Section applyD.
    Variable exprD : forall t, expr t -> tvarD t.

    Fixpoint applyD domain (xs : hlist expr domain)
      : forall range, functionTypeD (map tvarD domain) range -> range :=
        match xs in hlist _ domain return forall range, functionTypeD (map tvarD domain) range -> range with
          | HNil => fun _ x => x
          | HCons _ _ x xs' => fun _ f => applyD xs' _ (f (exprD x))
        end.

    Fixpoint etaD domain {struct domain}
      : forall (xs : hlist expr domain) range, functionTypeD (map tvarD domain) (tvarD range) -> tvarD range :=
        match domain return forall (xs : hlist expr domain) range, functionTypeD (map tvarD domain) (tvarD range) -> tvarD range with
          | nil => fun _ _ D => D
          | a :: b => fun hl r D => @etaD b (hlist_tl hl) r (D (exprD (hlist_hd hl)))
        end.
  End applyD.

  Variable uenv : hlist tvarD uvars.
  Variable env : hlist tvarD vars.

  Fixpoint exprD t (e : expr t) {struct e} : tvarD t :=
    match e with
      | Const _ c => c
      | Var x => hlist_get x env
      | UVar x => hlist_get x uenv
      | Func f xs => applyD exprD xs _ (Denotation (get funcs f))
    end.
  
  Lemma tvar_dec : forall (a b : tvar), {a = b} + {a <> b}.
    decide equality. eapply finEq. 
  Defined.

  Definition tvarCmp (a : tvar) : forall b, dcomp a b :=
    match a as a return forall b, dcomp a b with
      | None => fun b => match b with
                           | None => Env.Eq (eq_refl _)
                           | _ => Env.Lt _ _
                         end
      | Some a => fun b => match b return dcomp (Some a) b with
                             | None => Env.Gt _ _ 
                             | Some b =>
                               match finCmp a b with
                                 | Env.Eq pf => Env.Eq (match pf in _ = t return Some a = Some t with 
                                                          | refl_equal => refl_equal _
                                                        end)
                                 | Env.Lt => Env.Lt _ _
                                 | Env.Gt => Env.Gt _ _
                               end
                           end
    end.

  Definition exprEq : forall t (x y : expr t), option (x = y).
  refine (fix exprEq t (x : expr t) {struct x} : forall y : expr t, option (x = y) :=
    match x in expr t return forall y : expr t, option (x = y) with
      | Const t c1 => fun y : expr t => 
        match y in expr t' return forall c1 : tvarD t', option (Const t' c1 = y) with
          | Const t c2 => match t return forall c2 c1 : tvarD t, option (Const t c1 = Const t c2) with
                            | None => fun _ _ => None
                            | Some t => fun x y => if Eq (get types t) x y then Some _ else None
                          end c2
          | _ => fun _ => None
        end c1
      | Var x1 => fun y => 
        match y in expr t return forall Heq : t = get vars x1, option (Var x1 = match Heq in _ = T return expr T with
                                                                                  | refl_equal => y
                                                                                end) with
          | Var x2 => fun Heq => if finEq x1 x2 then Some _ else None
          | _ => fun _ => None
        end (refl_equal _)
      | UVar x1 => fun y => 
        match y in expr t 
          return forall Heq : t = get uvars x1, 
            option (UVar x1 = match Heq in _ = T return expr T with
                                | refl_equal => y
                              end) with
          | UVar x2 => fun Heq => if finEq x1 x2 then Some _ else None
          | _ => fun _ => None
        end (refl_equal _)
      | Func f1 xs1 => fun y => 
        match y in expr t return forall Heq : t = Range (get funcs f1),
          (forall xs2, option (xs1 = xs2))
          -> option (Func f1 xs1 = match Heq in _ = T return expr T with
                                     | refl_equal => y
                                   end) with
          | Func f2 xs2 => fun Heq cmp => match finEq f1 f2 with
                                            | right _ => None
                                            | left Heq' =>
                                              if cmp (match sym_eq Heq' in _ = F
                                                        return hlist expr (Domain (get funcs F)) with
                                                        | refl_equal => xs2
                                                      end) then Some _ else None
                                          end
          | _ => fun _ _ => None
        end (refl_equal _) (hlistEq exprEq xs1)
    end); clear exprEq; try abstract (subst;
      repeat match goal with
               | [ Heq : _ = _ |- _ ] => rewrite (@UIP_refl _ _ _ Heq) in *; clear Heq; simpl in *
             end; congruence).
  Defined.

  Fixpoint exprCmp t (x : expr t) : forall y : expr t, option (dcomp x y).
    refine (match x as x in expr t return forall y : expr t, option (dcomp x y) with
              | Const _ v => fun y =>
                match y as y in expr t 
                  return forall x : tvarD t, option (dcomp (Const _ x) y) with
                  | Const t y => fun x => 
                    match t as t
                      return forall x y : tvarD t, option (dcomp (Const _ x) (Const _ y)) with 
                      | None => fun _ _ => None
                      | Some t => fun x y => match Eq _ x y with 
                                               | None => None
                                               | Some pf => 
                                                 Some (Env.Eq match pf in _ = z return Const _ x = Const _ _ with
                                                                | refl_equal => refl_equal
                                                              end)
                                             end
                    end x y
                  | _ => fun _ => Some (Env.Lt _ _)
                end v
              | Var v => fun y =>
                match y as y in expr t 
                  return forall pf : t = get vars v, 
                    option (dcomp (Var v) match pf in _ = t return expr t with 
                                            | refl_equal => y
                                          end) with 
                  | Const _ _ => fun _ => Some (Env.Gt _ _)
                  | Var v' => fun _ => match finCmp v v' with 
                                         | Env.Lt => Some (Env.Lt _ _)
                                         | Env.Gt => Some (Env.Gt _ _)
                                         | Env.Eq _ => Some (Env.Eq _)
                                       end
                  | _ => fun _ => Some (Env.Lt _ _)
                end refl_equal
              | UVar v => fun y =>
                match y as y in expr t 
                  return forall pf : t = get uvars v, 
                    option (dcomp (UVar v) match pf in _ = t return expr t with 
                                            | refl_equal => y
                                          end) with 
                  | Const _ _ | Var _ => fun _ => Some (Env.Gt _ _)
                  | UVar v' => fun _ => match finCmp v v' with 
                                          | Env.Lt => Some (Env.Lt _ _)
                                          | Env.Gt => Some (Env.Gt _ _)
                                          | Env.Eq _ => Some (Env.Eq _)
                                        end
                  | _ => fun _ => Some (Env.Lt _ _)
                end refl_equal
              | Func f args => fun y =>
                match y as y in expr t
                  return forall pf : t = Range (get funcs f), option (dcomp (Func f args) 
                    match pf in _ = z return expr z with
                      | refl_equal => y
                    end) with
                  | Const _ _ | Var _ | UVar _ => fun _ => Some (Env.Gt _ _)
                  | Func f' args' => fun pf =>
                    match finCmp f f' with 
                      | Env.Lt => Some (Env.Lt _ _)
                      | Env.Gt => Some (Env.Gt _ _)
                      | Env.Eq pf' =>
                        match pf' in _ = t 
                          return forall (args : hlist expr (Domain (get funcs f))) (args' : hlist expr (Domain (get funcs t))) (pf : Range (get funcs t) = Range (get funcs f)) ,
                            option (dcomp (Func f args) 
                              match pf in _ = z return expr z with
                                | refl_equal => Func t args'
                              end)
                          with
                          | refl_equal => fun args args' pf => _
                        end args args' pf
                    end
                end refl_equal
            end); try solve [ subst; uip_all; reflexivity ].
    refine (None). (** TODO **)
  Defined.
End env.

Section Lifting.
  Variable types : list type.
  Variable funcs : functions types.
  Section Vars.
    Variable uvars : variables types.
    Variable vars' ext vars : variables types.

    Fixpoint liftExpr (T : tvar types) (e : expr funcs uvars (vars' ++ vars) T) 
      : expr funcs uvars (vars' ++ ext ++ vars) T :=
      match e in expr _ _ _ T return expr funcs uvars (vars' ++ ext ++ vars) T with
        | Var v => 
          match @liftDmid _ vars vars' ext v with
            | existT v pf => match pf in _ = t 
                               return expr funcs uvars (vars' ++ ext ++ vars) t
                               with
                               | refl_equal => Var _ uvars v
                             end
          end
        | UVar v => UVar _ _ v
        | Const t x => Const funcs uvars (vars' ++ ext ++ vars) t x 
        | Func f a => 
          Func f (@hlist_map _ _ (expr funcs uvars (vars' ++ ext ++ vars)) (fun t (x : expr funcs uvars (vars' ++ vars) t) => liftExpr x) _ a)
      end.
  End Vars.

  Lemma liftExpr_liftExpr_app : forall uvars x y z a T
    (P : expr _ uvars (x ++ z) T),
    liftExpr x y (a ++ z) (liftExpr x a z P) =
    match app_ass _ _ _ in _ = t return expr  _ _ (x ++ t) T with
      | refl_equal => liftExpr x (y ++ a) z P
    end.
  Proof.
    intros; uip_all.
    assert (forall k (exp : expr _ uvars k T) (E : k = x ++ z),
      liftExpr x y (a ++ z) (liftExpr x a z match E in _ = t return expr _ _ t _ with
                                              | refl_equal => exp
                                            end) =
      match e in (_ = t) return (expr _ uvars (x ++ t) T) with
        | eq_refl => liftExpr x (y ++ a) z match E in _ = t return expr _ _ t _ with
                                             | refl_equal => exp
                                           end
      end).
    clear. induction exp using expr_ind_strong; intros; simpl in *; subst; uip_all; simpl;
      try solve [ generalize e; rewrite e; uip_all; reflexivity ].
      (** vars **)
      case_eq (liftDmid z x (y ++ a) x0).
      intros; assert (projT1 (liftDmid z x (y ++ a) x0) = x1). rewrite H. auto.
      generalize (liftDmid_liftDmid_app _ x y z a x0). clear H. intros.
      case_eq (liftDmid z x a x0). simpl. intros.
      assert (projT1 (liftDmid z x a x0) = x2). rewrite H1. auto. clear H1.
      rewrite H2 in *. rewrite H0 in H. revert H. clear. uip_all.
      generalize e e1 e0. rewrite <- e1. uip_all. simpl. revert H.
      destruct (liftDmid (a ++ z) x y x2). simpl. intros; subst. clear.
      generalize e6. generalize e2 e3 e5. rewrite <- e2. rewrite <- e5. uip_all.
      generalize e7. rewrite (UIP_refl e0). uip_all. reflexivity.

      (** functions **)
      etransitivity. 
      instantiate (1 := Func f2 
        match e in _ = t return hlist (expr funcs uvars (x ++ t)) (Domain (get funcs f2)) with
          | refl_equal => 
            hlist_map (expr funcs uvars (x ++ (y ++ a) ++ z))
            (fun (t : tvar types) (x0 : expr funcs uvars (x ++ z) t) =>
              liftExpr x (y ++ a) z x0) h
        end).
        f_equal. destruct (get funcs f2); simpl in *. clear Denotation0. induction Domain0.
        rewrite (hlist_nil_only _ h) in *. simpl in *. uip_all. reflexivity.
        rewrite (hlist_eta _ h) in *. rewrite (hlist_eta _ h) in H. simpl in *. intuition. 
        specialize (H0 refl_equal). simpl in *. rewrite H0. rewrite IHDomain0.
        generalize (hlist_tl h). generalize (hlist_hd h). clear.
        generalize e. rewrite <- e. uip_all. reflexivity. eauto.
        clear. generalize e. rewrite <- e. uip_all. reflexivity.
      eapply (H _ P refl_equal).
    Qed.

    Lemma liftExpr_liftExpr_apps : forall uvars x y z a ls
      (h : hlist (expr _ uvars (x ++ z)) ls),
      (hlist_map (expr funcs uvars (x ++ y ++ a ++ z))
        (fun (x0 : tvar types) (e0 : expr funcs uvars (x ++ a ++ z) x0) =>
          liftExpr x y (a ++ z) e0)
        (hlist_map (expr funcs uvars (x ++ a ++ z))
          (fun (x0 : tvar types) (e0 : expr funcs uvars (x ++ z) x0) =>
            liftExpr x a z e0) h)) = 
      match app_ass _ _ _ in _ = t return hlist (expr funcs uvars (x ++ t)) ls with
        | refl_equal => 
          hlist_map (expr funcs uvars (x ++ (y ++ a) ++ z))
          (fun (x0 : tvar types) (e0 : expr funcs uvars (x ++ z) x0) =>
            liftExpr x (y ++ a) z e0) h
      end.
    Proof.
      intros. uip_all. induction ls.
        rewrite (hlist_nil_only _ h) in *. simpl in *. uip_all. reflexivity.
        rewrite (hlist_eta _ h) in *. specialize (IHls (hlist_tl h)).
        simpl. rewrite liftExpr_liftExpr_app. rewrite IHls. uip_all.
        generalize e0 e. rewrite <- e. uip_all. reflexivity.
    Qed.

  Lemma liftExpr_nil : forall uvars vars' vars T (e : expr funcs uvars (vars' ++ vars) T),
    liftExpr vars' nil vars e = e.
  Proof.
    induction e using expr_ind_strong; simpl; auto.
    generalize (liftDmid_lift_nil vars vars' x).
    destruct (liftDmid vars vars' nil x). simpl; intros; subst.
    simpl in *. uip_all. auto.
    f_equal. induction h; simpl; auto. simpl in *. firstorder. f_equal; auto.
  Qed.


  Lemma liftExpr_denote : forall uvars vars' vs vars T (e : expr funcs uvars (vars' ++ vars) T) U G G' G'', 
      exprD U (hlist_app G (hlist_app G' G'')) (liftExpr vars' vs vars e) = exprD U (hlist_app G G'') e.
  Proof.
    induction e using expr_ind_strong; simpl; auto.
      case_eq (liftDmid vars vars' vs x); intros. 
      generalize (@hlist_get_lift _ _ _ vars' vs vars x G G' G''). intros.
      unfold tvar in *. rewrite H0. rewrite H. clear.
      generalize (hlist_app G (hlist_app G' G'')). generalize e.
      rewrite <- e. intros. uip_all. reflexivity.

      generalize dependent h. destruct (get funcs f2). simpl. 
        generalize dependent Denotation0.      
        induction Domain0; simpl; intros. clear H.
        rewrite (hlist_nil_only _ h). simpl. auto.
       
      rewrite (hlist_eta _ h) in H. rewrite (hlist_eta _ h).
        simpl in *. rewrite IHDomain0; try tauto.
        f_equal. destruct H. rewrite H. reflexivity.
  Qed.

  Section UVars.
    Variable uvars' ext uvars : variables types.
    Variable vars : variables types.

    Fixpoint liftExprU (T : tvar types) (e : expr funcs (uvars' ++ uvars) vars T) 
      : expr funcs (uvars' ++ ext ++ uvars) vars T :=
      match e in expr _ _ _ T return expr funcs (uvars' ++ ext ++ uvars) vars T with
        | UVar v => 
          match @liftDmid _ uvars uvars' ext v with
            | existT v pf => match pf in _ = t 
                               return expr funcs (uvars' ++ ext ++ uvars) vars t
                               with
                               | refl_equal => UVar _ vars v
                             end
          end
        | Var v => Var _ _ v
        | Const t x => Const funcs (uvars' ++ ext ++ uvars) vars t x 
        | Func f a => 
          Func f (@hlist_map _ _ (expr funcs (uvars' ++ ext ++ uvars) vars) (fun t (x : expr funcs (uvars' ++ uvars) vars t) => liftExprU x) _ a)
      end.
  End UVars.

  Section Usubst.
    Fixpoint exprSubstU T a b c d (s : expr funcs a (b ++ c ++ d) T) {struct s}
      : expr funcs (c ++ a) (b ++ d) T :=
      match s in expr _ _ _ T return expr funcs (c ++ a) (b ++ d) T with
        | Const _ t => Const _ _ _ _ t
        | Var x => 
          fin_remove_range _ _ x 
          (fun x' pf => 
            match pf in _ = t return expr funcs (c ++ a) (b ++ d) t with
              | refl_equal =>
                let s := liftDend a x' in
                match projT2 s in _ = t return expr funcs (c ++ a) (b ++ d) t with
                  | refl_equal => UVar _ _ (projT1 s)
                end
            end)
          (fun x' pf => match pf in _ = t return expr _ _ _ t with
                          | refl_equal => Var _ _ x'
                        end)
        | UVar x => @liftExprU nil c a (b ++ d) (get a x) (UVar funcs _ x)
        | Func f args => Func f (hlist_map _ (fun T e => @exprSubstU T a b c d e) args)
      end.

    Lemma existT_eta : forall T (F : T -> Type) (a : {x : T & F x}), 
      a = existT _ (projT1 a) (projT2 a).
    Proof.
      intros. destruct a. simpl. reflexivity.
    Qed.

    Lemma exprSubstU_denote : forall T a b c d (A : hlist _ a) (B : hlist _ b) (C : hlist _ c) 
      (D : hlist _ d) (e : expr funcs a _ T), 
      exprD A (hlist_app B (hlist_app C D)) e =
      exprD (hlist_app C A) (hlist_app B D) (@exprSubstU _ a b c d e).
    Proof.
      induction e using expr_ind_strong; intros; auto.
        Focus.
        simpl. eapply hlist_get_remove_range.
        instantiate (1 := C). instantiate (1 := D). instantiate (1 := B).
        intros x' pf. uip_all. generalize dependent H. intro.
        change (option (fin types)) with (tvar types) in *.
        rewrite H. clear H. generalize pf. rewrite <- pf. uip_all. clear.
        rewrite (hlist_get_lift_end _ A x' C). destruct (liftDend a x'). simpl in *.
        generalize e e0. rewrite <- e. uip_all. auto.
        simpl. intros. change (option (fin types)) with (tvar types) in *.
        rewrite H. clear H. generalize pf. rewrite <- pf. uip_all. simpl. auto.
        
        simpl. generalize (@hlist_get_lift _ _ _ nil _ _ x HNil C A). simpl in *.
          intro. rewrite H. clear. unfold tvar in *. destruct (liftD c x).
          change (hlist_get x0 (hlist_app C A)) with
            (exprD (hlist_app C A) (hlist_app B D) (UVar funcs (b ++ d) x0)).
          generalize (UVar funcs (b ++ d) x0). clear.
          generalize e. rewrite <- e. uip_all. auto.
          
          simpl. generalize dependent (Denotation (get funcs f2)).
          generalize dependent (Domain (get funcs f2)).
          induction l. intros; rewrite (hlist_nil_only _ h) in *. simpl. auto.
          
          intros. simpl in *. rewrite (hlist_eta _ h) in *. rewrite (hlist_eta _ h) in H. 
          simpl in *. inversion H. intuition; rewrite IHl. rewrite H0. auto. auto.
    Qed.

  End Usubst.



End Lifting.

Section Qexpr.
  Context {types : list type}.
  Variable fs : functions types.

  Definition Qexpr := { x : variables types & expr fs nil x None }.

  Fixpoint denoteQuant (ls : variables types) : (hlist (@tvarD types) ls -> Prop) -> Prop :=
    match ls as ls return (hlist (@tvarD types) ls -> Prop) -> Prop with
      | nil => fun cc => cc (HNil)
      | a :: b => fun cc => 
        forall x, denoteQuant (fun g => cc (HCons x g))
    end.

  Definition qexprD (p : Qexpr) : Prop :=
    @denoteQuant (projT1 p) (fun x => exprD HNil x (projT2 p)).
End Qexpr.

Section ProverT.
  Context {types : list type}.
  Variable fs : functions types.

  Definition ProverT : Type := forall 
    (hyps : list (@expr types fs nil nil None))
    (goal : @expr types fs nil nil None), 
    hlist (fun e => @exprD _ fs _ _ HNil HNil None e) hyps -> 
    option (exprD HNil HNil goal).
  
End ProverT.

Section PartialApply.
  Fixpoint funtype (ls : list Type) (r : Type) : Type :=
    match ls with 
      | nil => r
      | a :: b => a -> funtype b r
    end.

  Fixpoint apply_ls (ls : list Type) (T : Type) (R : T -> Type) (V : T)
    : funtype ls (forall x : T, R x) -> funtype ls (R V) :=
    match ls with
      | nil => fun F => F V
      | a :: b => fun F => fun x : a => apply_ls b R V (F x)
    end.
End PartialApply.

(** Reflection Tactics **)
(************************)
Require Import Reflect.

Ltac extend_type T D types :=
  match T with
    | Prop => types
    | _ => 
      let rec find types :=
      match types with
        | nil => constr:(false)
        | ?a :: ?b =>
          let T' := eval simpl Impl in (Impl a) in
          match T' with
            | T => constr:(true)
            | _ => find b
          end
      end
    in
    match find types with
      | true => types
      | _ => constr:(D :: types)
    end
  end.

Definition defaultType T := {| Impl := T; Eq := fun _ _ => None |}.

Ltac extend_all_types Ts types :=
  match Ts with
    | nil => types
    | ?a :: ?b => 
      let types := extend_type a (defaultType a) types in
      extend_all_types b types
  end.

Ltac buildTypes e types :=
  let rec bt_args args types :=
    match args with
      | tt => types
      | (?a, ?b) => 
        let types := buildTypes a types in
        bt_args b types
    end
  in
  let cc _ Ts args :=
    let Ts := bt_args args Ts in
    let Ts := eval simpl app in Ts in
    extend_all_types Ts types
  in
  refl_app cc e.

Ltac collectTypes_expr e types :=
  let rec bt_args args types :=
    match args with
      | tt => types
      | (?a, ?b) =>
        let types := collectTypes_expr a types in
        bt_args b types
    end
  in
  let cc _ Ts args := 
    let types := append_uniq Ts types in
    let types := bt_args args types in
    types
  in
  refl_app cc e.

Ltac typesIndex x types :=
  indexOf Impl x types.

Ltac funcIndex x funcs :=
  indexOf Denotation x funcs.

Ltac refl_type types types' T :=
  match T with
    | Prop => constr:(None : tvar types)
    | _ => 
      let i := typesIndex T types types' in
      constr:(Some i)
  end.

Ltac refl_signature types types' f :=
  let rec refl T :=
    match T with 
      | ?A -> ?B =>
        let Ta := refl_type types types' A in
        match refl B with
          | ( ?args , ?rt ) =>
            let res := constr:(((Ta : @tvar types) :: args , rt)) in
                res
        end
      | _ =>
        let T := refl_type types types' T in
        constr:((@nil (@tvar types), T))
    end
  in
  let T := type of f in
  (** NOTE: T should never be dependent **)
  match refl T with
    | ( ?args , ?rt ) =>
      constr:(@Build_signature types args rt f)
  end.

Ltac extend_func types types' f funcs :=
  let rec find fs :=
    match fs with
      | nil => false
      | ?X :: ?Y =>
        let X' := eval simpl in (Denotation X) in
        match X' with
          | f => true
          | _ => find Y
        end
    end
  in
  match find funcs with
    | true => funcs
    | false => 
      let s := refl_signature types types' f in
      constr:(s :: funcs)
  end.

Ltac buildFuncs isConst types types' e funcs :=
  let rec refl_args args funcs :=
    match args with
      | tt => funcs
      | (?X, ?Y) => 
        let funcs := bf X funcs in
        refl_args Y funcs
    end
  with bf e funcs :=
    match isConst e with
      | true => funcs
      | _ => 
        let cc f Ts args := 
          let funcs := extend_func types types' f funcs in
          refl_args args funcs
        in
        refl_app cc e
    end
  in bf e funcs.

Ltac buildExpr isConst types types' funcs vars e :=
  let rec refl_args args :=
    match args with
      | tt => 
        let res := constr:(@HNil _ (@expr types funcs vars)) in
        res
      | (?X, ?Y) => 
        let x := be X in
        let y := refl_args Y in
            let res := constr:(HCons x y) in
              res
    end
  with be e :=
    match isConst e with
      | false =>
        let cc f Ts args := 
          let f := funcIndex f funcs in
          let args := refl_args args in
          constr:(@Func types funcs vars f args)
        in        
        refl_app cc e
      | true =>
        let t := type of e in
        let t := refl_type types types' t in
        let res := constr:(@Const types funcs vars t e) in
        res
    end
  in be e.

Ltac extendEnv isConst types funcs vars G :=
  match G with
    | forall x : _ , ?G' =>
      let types := buildTypes G types in
      let types' := eval simpl in (map Impl types) in
      let funcs := buildFuncs isConst types types' G funcs in
      let funcs := eval simpl in funcs in
      extendEnv isConst types funcs vars G'
    | forall x : _ , @?G' x => fail (** TODO : how do I fill the hole in G'? **)
    | _ => 
      let types := buildTypes G types in
      let types' := eval simpl in (map Impl types) in
      let funcs := buildFuncs isConst types types' G funcs in
      let funcs := eval simpl in funcs in
      constr:((types, funcs, vars))
  end.

Ltac reflect_goal isConst types funcs vars :=
  match goal with
    | [ |- ?G ] =>
      let types := buildTypes G (@nil type) in
      let types' := eval simpl in (map Impl types) in
      let funcs := buildFuncs isConst types types' G (@nil (signature types)) in
      let funcs := eval simpl in funcs in
      let vars := constr:(@nil (tvar types)) in
      let e := buildExpr isConst types types' funcs vars G in
      change (exprD HNil HNil e)
  end.

Ltac reflect isConst :=
  match goal with
    | [ |- ?G ] =>
      let types := buildTypes G (@nil type) in
      let types' := eval simpl in (map Impl types) in
      let funcs := buildFuncs isConst types types' G (@nil (signature types)) in
      let funcs := eval simpl in funcs in
      let vars := constr:(@nil (tvar types)) in
      let e := buildExpr isConst types types' funcs vars G in
      change (exprD HNil HNil e)
  end.


Ltac consts e :=
  match e with
    | true => true
    | false => true
    | O => true
    | S ?n => consts n
    | _ => false
  end.

(** Three simple test cases **) 
(** These terms get pretty big since we have to store the list instead of just the length.
 ** It would probably be beneficial to let-bind some terms unless Coq is doing its own sharing
 **)
(* TODO: Fix this if unification works out well this way....

Goal forall a b : nat, a + b = a + b.
  intros; reflect consts.
(* Performance Evaluation *)
  match goal with
    | [ |- exprD _ (Func _ (HCons ?A (HCons ?B _))) ] => 
      pose A ; pose B
  end.
  pose (exprEq e e0). hnf in o.
Abort.

Goal negb false = true.
  intros; reflect consts.
Abort.

Goal forall n m, n + m = m + 0 + n.
  intros; reflect consts.
Abort.
*)

Require Export Env.