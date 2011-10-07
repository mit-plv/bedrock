Require Import List Eqdep_dec.
Require Import Env.

Set Implicit Arguments.

Section env.
  Record type := {
    Impl : Type;
    Eq : forall x y : Impl, option (x = y)
  }.

  Variable types : list type.

  Definition tvar := option (fin (length types)).
  Definition tvarD x := match x with
                          | None => Prop
                          | Some x => Impl (get types x)
                        end.

  Fixpoint functionTypeD (domain : list tvar) (range : tvar) : Type :=
    match domain with
      | nil => tvarD range
      | d :: domain' => tvarD d -> functionTypeD domain' range
    end.

  Record signature := {
    Domain : list tvar;
    Range : tvar;
    Denotation : functionTypeD Domain Range
  }.

  Definition functions := list signature.
  Definition variables := list tvar.

  Variable funcs : functions.
  Variable vars : variables.

  Definition func := fin (length funcs).
  Definition var := fin (length vars).

  Inductive expr : tvar -> Type :=
  | Const : forall t : tvar, tvarD t -> expr t
  | Var : forall x : var, expr (get vars x)
  | Func : forall f : func, hlist expr (Domain (get funcs f)) -> expr (Range (get funcs f)).

  Section applyD.
    Variable exprD : forall t, expr t -> tvarD t.

    Fixpoint applyD domain (xs : hlist expr domain)
      : forall range, functionTypeD domain range -> tvarD range :=
        match xs in hlist _ domain return forall range, functionTypeD domain range -> tvarD range with
          | HNil => fun _ x => x
          | HCons _ _ x xs' => fun _ f => applyD xs' _ (f (exprD x))
        end.
  End applyD.

  Variable env : hlist tvarD vars.

  Fixpoint exprD t (e : expr t) {struct e} : tvarD t :=
    match e with
      | Const _ c => c
      | Var x => hlist_get x env
      | Func f xs => applyD exprD xs _ (Denotation (get funcs f))
    end.
  
  Lemma tvar_dec : forall (a b : tvar), {a = b} + {a <> b}.
    decide equality. eapply finEq. 
  Defined.

  Definition exprEq : forall t (x y : expr t), option (x = y).
  refine (fix exprEq t (x : expr t) {struct x} : forall y : expr t, option (x = y) :=
    match x in expr t return forall y : expr t, option (x = y) with
      | Const t c1 => fun y : expr t => match y in expr t' return forall c1 : tvarD t', option (Const t' c1 = y) with
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
      | Func f1 xs1 => fun y => match y in expr t return forall Heq : t = Range (get funcs f1),
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
                 | [ Heq : _ = _ |- _ ] => rewrite (UIP_dec tvar_dec Heq (refl_equal _)) in *; clear Heq; simpl in *
               end; congruence).
  Defined.
End env.

Section Qexpr.
  Context {types : list type}.
  Variable fs : functions types.

  Definition Qexpr := { x : variables types & expr fs x None }.

  Fixpoint denoteQuant (ls : variables types) : (hlist (tvarD types) ls -> Prop) -> Prop :=
    match ls as ls return (hlist (tvarD types) ls -> Prop) -> Prop with
      | nil => fun cc => cc (HNil)
      | a :: b => fun cc => 
        forall x, denoteQuant (fun g => cc (HCons x g))
    end.

  Definition qexprD (p : Qexpr) : Prop :=
    @denoteQuant (projT1 p) (fun x => exprD x (projT2 p)).
End Qexpr.

Section ProverT.
  Context {types : list type}.
  Context {fs : functions types}.

  Definition ProverT : Type := forall 
    (hyps : list (@Qexpr types fs))
    (goal : @expr types fs nil None), 
    hlist (@qexprD _ fs) hyps -> option (exprD HNil goal).

(*
  Definition unify (T : type) (e1 e2 : expr fs vs T) : option (expr fs )
*)


  Definition assumptionProver : ProverT.
    unfold ProverT.
    refine (fix assumptionProver hyps (goal : expr fs nil None) : hlist (@qexprD _ fs) hyps -> option (exprD HNil goal) :=
      match hyps with
        | nil => fun _ => None
        | existT vs exp :: b => 
          match vs as vs return forall exp : expr fs vs None, hlist (@qexprD _ fs) (existT (fun vs => expr fs vs None) vs exp :: b) -> _ with
            | nil => fun exp pfHyps => if exprEq goal exp then Some _ else assumptionProver b goal (hlist_tl pfHyps)
            | _ => fun _ pfHyps => assumptionProver b goal (hlist_tl pfHyps)
          end exp
      end).
  generalize ((hlist_hd pfHyps)). unfold qexprD. simpl. rewrite _H. intro. apply H.

    (** TODO :
        - How would I implement one of these? 
        - Termination will be problematic...
     **)
  Defined.
  
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

Ltac refl_app cc e := 
  let rec refl cc e As :=
    match e with
      | ?A ?B =>
        let Ta := type of A in
        match type of A with
          | _ -> ?TT => 
            let As := constr:((B, As)) in
            let Tb := type of B in
            let cc f Ts args := 
              let Ts' := constr:(Ts ++ (Tb : Type) :: nil) in
              cc f Ts' args
            in 
            refl cc A As
          | forall x : ?T1, @?T2 x => 
            let cc f Ts args := 
              let Tb  := type of B in
              let f'  := eval simpl in (@apply_ls Ts T1 T2 B f) in
              cc f' Ts args
            in
            refl cc A As
        end
      | _ =>
        let Ts := constr:(@nil Type) in
        cc e Ts As
    end
  in
  let b := constr:(tt) in
  refl cc e b.

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
      | nil => types
      | ?a :: ?b => 
        let types := buildTypes a types in
        bt_args b types
    end
  in
  let cc _ Ts args :=
    let Ts := eval simpl app in Ts in
    extend_all_types Ts types
  in
  refl_app cc e. 

(*
Ltac buildFuncs types e funcs :=
  let cc f Ts args :=
    
  refl_app cc e 

Goal forall a b : nat, a + b = b + a.
  intros. Set Printing Implicit.
  match goal with
    | [ |- ?G ] =>
      let ls := constr:(@nil type) in
      let ts := buildTypes G ls in
      idtac ts
  end.

Ltac inList x ls :=
  match ls with
    | nil => false
    | x :: _ => true
    | _ :: ?ls' => inList x ls'
  end.

Ltac extend x ls :=
  let b := inList x ls in
    match b with
      | true => ls
      | _ => constr:(x :: ls)
    end.





Ltac buildTypes e types :=
  match e with
    | ?f ?a ?b ?c => match type of f with
                       | ?D1 -> ?D2 -> ?D3 -> ?R =>
                         let types := extend_type (defaultType D1) types in
                         let types := extend_type (defaultType D2) types in
                         let types := extend_type (defaultType D3) types in
                         let types := extend_type (defaultType R) types in
                         let types := buildTypes a types in
                         let types := buildTypes b types in
                           buildTypes c types
                       | _ =>
                         match type of (f a) with
                           | ?D1 -> ?D2 -> ?R =>
                             let types := extend (defaultType D1) types in
                             let types := extend (defaultType D2) types in
                             let types := extend (defaultType R) types in
                             let types := buildTypes b types in
                               buildTypes c (defaultType Empty_set) types
                         end
                     end
    | ?f ?a ?b => match type of f with
                    | ?D1 -> ?D2 -> ?R =>
                      let types := extend (defaultType D1) types in
                      let types := extend (defaultType D2) types in
                      let types := extend (defaultType R) types in
                      let types := buildTypes a types in
                        buildTypes b types
                    | _ =>
                      match type of (f a) with
                        | ?D1 -> ?R =>
                          let types := extend (defaultType D1) types in
                          let types := extend (defaultType R) types in
                            buildTypes b types
                      end
                  end
    | ?f ?a => match type of f with
                 | ?D1 -> ?R =>
                   let types := extend (defaultType D1) types in
                   let types := extend (defaultType R) types in
                     buildTypes a types
               end
    | _ => types
  end.

Ltac indexOf x ls :=
  match ls with
    | x :: ?ls' => constr:(FO (length ls'))
    | _ :: ?ls' => let f := indexOf x ls' in constr:(FS f)
  end.

Definition default t (ts : list type) : signature (t :: ts) :=
  Build_signature (types := t :: ts) (Some (FO _) :: nil) (Some (FO _)) (fun x => x).

Ltac buildFuncs e types types' funcs :=
  match e with
    | ?f ?a ?b ?c => match type of f with
                       | ?D1 -> ?D2 -> ?D3 -> ?R =>
                         let D1 := indexOf D1 types' in
                         let D2 := indexOf D2 types' in
                         let D3 := indexOf D3 types' in
                         let R := indexOf R types' in
                         let funcs := extend (Build_signature (types := types) (D1 :: D2 :: D3 :: nil) R f) funcs in
                           buildFuncs a types types' funcs
                       | _ => match type of (f a) with
                                | ?D1 -> ?D2 -> ?R =>
                                  let D1 := indexOf D1 types' in
                                  let D2 := indexOf D2 types' in
                                  let R := indexOf R types' in
                                  let funcs := extend (Build_signature (types := types) (D1 :: D2 :: nil) R f) funcs in
                                    buildFuncs a types types' funcs
                              end 
                     end
    | ?f ?a ?b => match type of f with
                    | ?D1 -> ?D2 -> ?R =>
                      let D1 := indexOf D1 types' in
                      let D2 := indexOf D2 types' in
                      let R := indexOf R types' in
                      let funcs := extend (Build_signature (types := types) (D1 :: D2 :: nil) R f) funcs in
                        buildFuncs a types types' funcs
                    | _ => match type of (f a) with
                             | ?D1 -> ?R =>
                               let D1 := indexOf D1 types' in
                               let R := indexOf R types' in
                               let funcs := extend (Build_signature (types := types) (D1 :: nil) R f) funcs in
                                 buildFuncs a types types' funcs
                           end
                  end
    | ?f ?a => match type of f with
                 | ?D1 -> ?R =>
                   let D1 := indexOf D1 types' in
                   let R := indexOf R types' in
                   let funcs := extend (Build_signature (types := types) (D1 :: nil) R f) funcs in
                     buildFuncs a types types' funcs
               end
    | _ => funcs
  end.

Ltac indexOfF x ls :=
  match ls with
    | Build_signature _ _ x :: ?ls' => constr:(FO (length ls'))
    | _ :: ?ls' => let f := indexOfF x ls' in constr:(FS f)
  end.

Ltac buildVars isConst types types' funcs e vars :=
  match e with
    | ?f ?a =>
      let f := indexOfF f funcs in
        buildVars isConst types types' funcs a vars
    | ?f ?a ?b =>
      let f := indexOfF f funcs in
      let vars := buildVars isConst types types' funcs a vars in
        buildVars isConst types types' funcs b vars
    | ?f ?a ?b =>
      let f := indexOfF (f a) funcs in
        buildVars isConst types types' funcs b vars
    | ?f ?a ?b ?c =>
      let f := indexOfF f funcs in
      let vars := buildVars isConst types types' funcs a vars in
      let vars := buildVars isConst types types' funcs b vars in
        buildVars isConst types types' funcs c vars
    | ?f ?a ?b ?c =>
      let f := indexOfF (f a) funcs in
      let vars := buildVars isConst types types' funcs b vars in
        buildVars isConst types types' funcs c vars
    | _ =>
      match isConst e with
        | true => vars
        | _ =>
          let t := type of e in
          let t := indexOf t types' in
          extend (Build_variable (types := types) t e) vars
      end
  end.

Ltac indexOfV x ls :=
  match ls with
    | Build_variable _ x :: ?ls' => constr:(FO (length ls'))
    | _ :: ?ls' => let f := indexOfV x ls' in constr:(FS f)
  end.

Ltac buildExpr isConst types types' funcs vars e :=
  match e with
    | ?f ?a =>
      let f := indexOfF f funcs in
      let a := buildExpr isConst types types' funcs vars a in
        constr:(Func (types := types) (funcs := funcs) (vars := vars) f (HCons a HNil))
    | ?f ?a ?b =>
      let f := indexOfF f funcs in
      let a := buildExpr isConst types types' funcs vars a in
      let b := buildExpr isConst types types' funcs vars b in
        constr:(Func (types := types) (funcs := funcs) (vars := vars) f (HCons a (HCons b HNil)))
    | ?f ?a ?b =>
      let f := indexOfF (f a) funcs in
      let b := buildExpr isConst types types' funcs vars b in
        constr:(Func (types := types) (funcs := funcs) (vars := vars) f (HCons b HNil))
    | ?f ?a ?b ?c =>
      let f := indexOfF f funcs in
      let a := buildExpr isConst types types' funcs vars a in
      let b := buildExpr isConst types types' funcs vars b in
      let c := buildExpr isConst types types' funcs vars c in
        constr:(Func (types := types) (funcs := funcs) (vars := vars) f (HCons a (HCons b (HCons c HNil))))
    | ?f ?a ?b ?c =>
      let f := indexOfF (f a) funcs in
      let b := buildExpr isConst types types' funcs vars b in
      let c := buildExpr isConst types types' funcs vars c in
        constr:(Func (types := types) (funcs := funcs) (vars := vars) f (HCons b (HCons c HNil)))
    | _ =>
      match isConst e with
        | false =>
          let t := type of e in
            let t := indexOfV e vars in
              constr:(Var (types := types) funcs (vars := vars) t)
        | true =>
          let t := type of e in
            let t := indexOf t types' in
              constr:(Const (types := types) funcs vars t e)
      end
  end.

Ltac reflect isConst := intros;
  match goal with
    | [ |- ?G ] =>
      let types := buildTypes G (@nil type) in
        let types' := eval simpl in (map Impl types) in
          let funcs := buildFuncs G types types' (@nil (signature types)) in
            let funcs := eval simpl in funcs in
              let vars := buildVars isConst types types' funcs G (@nil (variable types)) in
                let e := buildExpr isConst types types' funcs vars G in
                  change (exprD e)
  end.

Ltac consts e :=
  match e with
    | true => true
    | false => true
    | O => true
    | S ?n => consts n
    | _ => false
  end.

Theorem test1 : negb false = true.
  reflect consts.
Abort.

Theorem test2 : forall n m, n + m = m + 0 + n.
  reflect consts. simpl length.
Abort.
*)