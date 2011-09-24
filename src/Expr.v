(** TODO List
 ** - Merging states
 ** - Lifting expressions to new states
 ** - Prover for simple domain
 ** - Unification variables?
 ** - Expression equality
 **)

Require Import String.
Require Import List Arith.

Set Implicit Arugments.
Set Strict Implicit.

Section FunType.
  Context {T U : Type}.
  Variable D : T -> Type.
  Variable R : U -> Type.

  Fixpoint funtype (ls : list T) (r : U) : Type :=
    match ls with 
      | nil => R r
      | a :: b => D a -> funtype b r
    end.

  Definition funtype' (x : list T * U) : Type :=
    match x with
      | (x,y) => funtype x y
    end.
End FunType.

Section Member.
  Context {T : Type}. 

  Inductive Mem (V : T) : list T -> Type :=
  | MHere : forall R, Mem V (V :: R)
  | MNext : forall V' R, Mem V R -> Mem V (V' :: R).

  Variable D : T -> Type.

  Fixpoint Env (g : list T) : Type :=
    match g with
      | nil => unit
      | a :: b => D a * Env b
    end%type.

  Fixpoint Env_app {s s' : list T} : Env s -> Env s' -> Env (s ++ s') :=
    match s with 
      | nil => fun _ x => x
      | a :: b => fun l r => 
        (fst l, Env_app (snd l) r)
    end.

  Fixpoint get {t} (s : list T) (m : Mem t s) : Env s -> D t :=
    match m with
      | MHere _ => fun x => fst x
      | MNext _ _ r => fun x => get _ r (snd x)
    end.

  Fixpoint lift {V} ls lse : Mem V ls -> Mem V (lse ++ ls) :=
    match lse with 
      | nil => fun x => x 
      | a :: b => fun x => MNext _ _ _ (lift ls b x)
    end.

  Fixpoint extend {V} ls lse (m : Mem V ls) : Mem V (ls ++ lse) :=
    match m with 
      | MHere x => MHere V (x ++ lse)
      | MNext _ R m => MNext V _ (R ++ lse) (extend R lse m)
    end.

  Require Import Program.

  Fixpoint count {V ls} (m : Mem V ls) : nat :=
    match m with
      | MHere _ => 0
      | MNext _ _ m => 1 + count m
    end.
  
  Theorem eq_if_count : forall V ls (l r : Mem V ls), 
    count l = count r -> l = r.
  Proof.
    induction l; dependent destruction r; simpl in *; intros; try congruence; auto.
    inversion H. eapply IHl in H1. subst; reflexivity.
  Qed.

  Theorem neq_if_ncount : forall V ls (l r : Mem V ls), 
    count l <> count r -> l <> r.
  Proof.
    induction l; dependent destruction r; simpl in *; intros; try congruence; auto.
    intro. inversion H0. intro. inversion H0.
    Require Import EqdepFacts.
    intro. apply H. inversion H0. eapply inj_pair2 in H2. subst; reflexivity.
  Qed.


  Definition eqMem {V ls} (l r : Mem V ls) : {l = r} + {l <> r} :=
    match eq_nat_dec (count l) (count r) with 
      | left pf => left _ (eq_if_count _ _ _ _ pf) 
      | right pf => right _ (neq_if_ncount _ _ _ _ pf)
    end.

End Member.

Notation "'$>' a" := (@MNext _ _ _ _ a) (at level 5).
Notation "'$$'" := (@MHere _ _ _) (at level 5).

(** Reflection State **)
Fixpoint List2Fun (D : Type) (ls : list Type) (n : nat) : nat -> Type :=
  match ls with
    | nil => fun _ => D
    | a :: b => 
      let r := List2Fun D b (S n) in
      fun x => if eq_nat_dec x n then a else r x
  end.

Definition maybe {T U : Type} (D : T) (F : U -> T) (o : option U) : T :=
  match o with
    | None => D
    | Some t => F t
  end.

Record ReflSpine : Type :=
{ Typs        : list Type
; constsOf    : nat -> Type
; Sym_type    : list (list nat * option nat)
}.

Inductive empty : Type := .

Record ReflDenote (RS : ReflSpine) : Type :=
{ Typ_denote  := List2Fun empty (Typs RS) 0
; constIn     : forall T, constsOf RS T -> Typ_denote T
; Sym_denote  : Env (funtype' Typ_denote (maybe Prop Typ_denote)) (Sym_type RS)
}.

Implicit Arguments Typ_denote [ RS ].
Implicit Arguments constIn [ RS ].
Implicit Arguments Sym_denote [ RS ].

(** Syntax of Expressions **)
Section Expr.
  Variable RS : ReflSpine.
  Variable RD : ReflDenote RS.
  Variable vs : list nat.
  Variable VE : Env (Typ_denote RD) vs.

  Inductive Expr : option nat -> Type := 
    (** variables **)
  | Var  : forall T, Mem T vs -> Expr (Some T)
    (** functions **)
  | App : forall Ts T, Mem (Ts,T) (Sym_type RS) -> Exprs Ts -> Expr T
    (** constants **)
  | Const : forall T, constsOf RS T -> Expr (Some T)
  with Exprs : list nat -> Type :=
  | Enil  : Exprs nil
  | Econs : forall T Ts, Expr (Some T) -> Exprs Ts -> Exprs (T :: Ts)
  .

  (** TODO : Expr Equality **)

  Fixpoint denoteExpr T (e : Expr T) : maybe Prop (Typ_denote RD) T :=
    match e in Expr T return maybe Prop (Typ_denote RD) T with 
      | Var _ m => get _ _ m VE
      | App Ts T s es =>
        denoteExprs Ts T es (get (funtype' (Typ_denote RD) (maybe Prop (Typ_denote RD))) (Sym_type RS) s (Sym_denote RD))
      | Const _ x => constIn RD _ x 
    end
  with denoteExprs Ts T (es : Exprs Ts) 
    : funtype (Typ_denote RD) (maybe Prop (Typ_denote RD)) Ts T -> maybe Prop (Typ_denote RD) T :=
    match es with 
      | Enil => fun r => r
      | Econs _ _ x y => fun f => denoteExprs _ _ y (f (denoteExpr _ x))
    end.

End Expr.

Implicit Arguments App [ RS Ts T ].
Implicit Arguments Const [ RS T ].
Implicit Arguments Var [ RS T ].
Implicit Arguments denoteExpr [ RS vs ].
Implicit Arguments denoteExprs [ RS vs ].

(*
Section Lifting.
  Context {Typ : Type}. 
  Variable constsOf : Typ -> Type.
  Variable (ss sse : list (list Typ * option Typ)).
  Variable (vs ve : list Typ).

  Fixpoint liftExpr T (e : Expr constsOf ss vs T) : Expr constsOf (sse ++ ss) (ve ++ vs) T :=
    match e with
      | App Ts T s es =>
        let es' := liftExprs Ts es in
        App constsOf (sse ++ ss) (ve ++ vs) Ts T (lift ss sse s) es'
      | Const a b => Const constsOf _ _ a b
      | Var _ m => Var _ _ _ _ (lift vs ve m)  
    end
  with liftExprs Ts (es : Exprs constsOf ss vs Ts) : Exprs constsOf (sse ++ ss) (ve ++ vs) Ts :=
    match es with
      | Enil => Enil constsOf (sse ++ ss) (ve ++ vs)
      | Econs _ _ x y => Econs constsOf _ _ _ _ (liftExpr _ x) (liftExprs _ y)
    end.
    
End Lifting.
*)

Section QExpr.
  Variable RS : ReflSpine.

  Definition QExpr := 
    { x : list nat & Expr RS x None }.

  Variable RD : ReflDenote RS.

  Fixpoint denoteQuant (ls : list nat) : (Env (Typ_denote RD) ls -> Prop) -> Prop :=
    match ls with
      | nil => fun cc => cc tt
      | a :: b => fun cc => 
        forall (x : Typ_denote RD a), denoteQuant b (fun g => cc (x, g))
    end.

  Definition denoteQExpr (p : QExpr) : Prop :=
    denoteQuant (projT1 p) 
      (fun x : Env (Typ_denote RD) (projT1 p) => denoteExpr RD x None (projT2 p)).
End QExpr.

(*
Definition extendReflState (a b : ReflState) : ReflState :=
  let atyp_count := length (Typs a) in
  {| Typs     := Typs a ++ Typs b
   ; constsOf := fun x => if lt_dec x atyp_count then constsOf x else 
*)

(* TODO : This type is a mess 
Definition ProverT (RS : ReflState) :=
  forall Typ_ext SymT_ext 
    (SymD_ext : Env (funtype' (List2Fun (Typs RS ++ Typ_ext) 0) (Typ_denote' (List2Fun (Typs RS ++ Typ_ext) 0))) (Sym_type RS ++ SymT_ext))
    (Hs : list (QExpr (constsOf RS) (Sym_type RS ++ SymT_ext))),
    Env (denoteQExpr (constsOf RS) (List2Fun (Typs RS ++ Typ_ext) 0) (constIn RS) (Sym_type RS ++ SymT_ext) (Env_app _ (Sym_denote RS) SymD_ext)) Hs -> 
    forall (G : Expr (constsOf RS) (Sym_type RS ++ SymT_ext) nil None),
      option (denoteExpr _ (Sym_type RS ++ SymT_ext) nil (Typ_denote RS) (constIn RS) (Env_app _ (Sym_denote RS) SymD_ext) tt None G).


Definition nat_prover : ProverT ReflState_nat. 
Admitted.
*)

Definition ReflSpine_nat : ReflSpine := Eval simpl in 
  let typs := (nat:Type) :: @nil Type in
  let constsOf := List2Fun empty typs 0 in (* fun x : nat => if eq_nat_dec x 0 then nat else empty in *)
  {| Typs       := typs
   ; constsOf   := constsOf
   ; Sym_type   := (0 :: 0 :: nil, Some 0) :: (*0 :: 0 :: nil, None) ::*) nil
   |}.

Definition ReflDenote_nat : ReflDenote ReflSpine_nat := 
  let Typ_denote := List2Fun empty (Typs ReflSpine_nat) 0 in
  {| constIn   := fun T => match T as T return constsOf ReflSpine_nat T  -> Typ_denote T with
                             | 0 => fun x => x
                             | _ => fun x => match x with
                                             end
                           end
  ; Sym_denote := (plus, tt)
  |}.

(**********************
 ** Reflecting Types **
 **********************)
Ltac refl_type env i T :=
  match env with
    | T :: _ => constr:((i, env))
    | ?X :: ?E =>
      let n := constr:(S i) in
      match refl_type E n T with
        | ( ?I , ?E ) =>
          constr:((X :: E, I))
      end
    | nil => constr:((i, T :: nil))
  end.

Ltac refl_ret_type Ts T :=
  match T with
    | Prop => None
    | _ => match refl_type Ts 0 T with
             | ( ?rT , _ ) => 
               constr:(Some rT)
           end
  end.

Ltac refl_fun_type env T :=
  match T with
    | Prop => 
      constr:(((@nil nat , @None nat), env))
    | ?T1 -> ?T2 => 
      match refl_type env 0 T1 with
        | ( ?t1 , ?env' ) => 
          match refl_fun_type env' T2 with
            | ( ( ?AS , ?RT ) , ?E ) => 
              constr:(((t1 :: AS , RT), E))
          end
      end
    | _ => 
      match refl_type env 0 T with
        | ( ?I , ?E ) => 
          constr:(((@nil nat, Some I), E))
      end
  end.


(** Ltac "lookup a symbol in an Env". fail if non-existant **)
Ltac lookup x es ev :=
  match ev with
    | ( x , _ ) => 
      match es with
        | ?T :: ?TS =>
          let r := constr:(@MHere _ T TS) in r
      end
    | ( _ , ?R ) =>
      match es with
        | ?T :: ?TS =>
          let r := lookup x TS R in
          constr:(@MNext _ _ T TS r)
      end
  end.

Ltac lookup_cc fcc scc es ev x :=
  match ev with
    | ( x , _ ) => 
      match es with
        | ?T :: ?TS =>
          let r := constr:(@MHere _ T TS) in scc r
      end
    | ( _ , ?R ) =>
      match es with
        | ?T :: ?TS =>
          let scc' r := 
            let k := constr:(@MNext _ _ T TS r) in scc k
          in
          lookup_cc fcc scc' TS R x
      end
    | tt => fcc x
  end.


Fixpoint apply_ls (ls : list Type) (T : Type) (R : T -> Type) (V : T)
  : funtype (fun x => x) (fun _ => forall x, R x) ls tt -> funtype (fun x => x) (fun x => R V) ls tt :=
  match ls with
    | nil => fun F => F V
    | a :: b => fun F => fun x : a => apply_ls b T R V (F x)
  end.

Ltac refl_app cc e := 
  let aT := constr:(@nil Type) in
  let rec refl e As :=
    match e with
      | ?A ?B =>
        let As' := constr:((B, As)) in
        refl A As' 
      | _ => 
        let T := type of e in
        cc e aT T As
    end
  in
  let b := constr:(tt) in
  refl e b.

Ltac reflect_expr refl_const RS Ts Ss Sv Vs Vv e :=
  let aT := constr:(@nil Type) in
  let rec refl_expr e :=
    let app_case e :=
      match refl_app reflect_args e with
        | ( ?args , ?F ) =>
          let m := lookup F Ss Sv in
          constr:(@App RS Vs _ _ m args)
      end        
    in
    let var_case m :=
      constr:(Var RS Vs _ m)
    in
    let const_case m :=
      let T := type of e in
      match refl_type Ts 0 T with
        | ( ?rT , _ ) =>  (** the second component should be equal to Ts **)
          constr:(@Const RS Vs rT m)
      end
    in
    let var_app_case := lookup_cc app_case var_case Vs Vv in
    refl_const const_case var_app_case e 
      
  with reflect_args F Typs Ft As :=
    match As with
      | tt =>
        constr:((Enil RS Vs, F))
      | ( ?A , ?As ) => 
        match Ft with
          | ?T1 -> ?T2 => 
            let Typs' := constr:(Typs ++ (T1:Type) :: @nil Type) in
            match reflect_args F Typs' T2 As with
              | ( ?res , ?F' ) => 
                match refl_type Ts 0 T1 with
                  | ( ?rT , _ ) =>
                    let Ae := refl_expr A in
                    constr:((Econs RS Vs rT _ Ae res , F'))
                 end
            end  
          | forall x : ?T1 , @?T2 x => 
            let Ft' := eval simpl in (T2 A) in
            let Typs' := eval simpl app in Typs in
            let F'' := eval simpl in (apply_ls Typs' T1 T2 A F) in
            reflect_args F'' Typs' Ft' As
        end
    end
  in
  refl_expr e.

(** lookup "x" in "Vs" (spine of Vs is given in Ts, denotation of Ts given in E) **)
Ltac set_add Ts Ss Sv x :=
  match Sv with
    | ( x , _ ) => constr:((Ts, Ss, Sv))
    | tt => 
      let t := type of x in
      match refl_fun_type Ts t with
        | ( ?T , ?Ts ) =>
          constr:((Ts, T :: nil, (x, tt)))
      end
    | ( ?V , ?Vs ) =>
      match Ss with
        | ?S :: ?Ss =>
          match set_add Ts Ss Vs x with
            | ( ?Ts , ?Ss , ?Vs ) => constr:((Ts , S :: Ss, (V, Vs)))
          end
      end
  end.

Ltac set_add' st x :=
  match st with
    | ( ?Ts , ?Ss , ?Sv ) => set_add Ts Ss Sv x
  end.

Ltac refl_nat_const scc fcc e := 
  match e with
    | 0   => scc e 
    | S _ => scc e
    | _ => fcc e
  end.

Ltac gather_symbols refl_const Ts Ss Sv exp :=
  let rec gather st e :=
    let fcc x :=
      let v := gather_args st in
      refl_app v e
    in
    let scc _ := st in
    refl_const scc fcc e
  with gather_args st F Typs Ft As :=
    match As with
      | tt => 
        let st' := set_add' st F in
        st'
      | ( ?A , ?As ) => 
        match Ft with
          | ?T1 -> ?T2 =>
            let Typs' := constr:(Typs ++ (T1:Type) :: @nil Type) in
            let st' := gather st A in
            gather_args st' F Typs' T2 As
          | forall x : ?T1, @?T2 x =>
            let Ft' := eval simpl in (T2 A) in
            let F'' := eval simpl in (apply_ls Typs T1 T2 A F) in
            gather_args st F'' Typs Ft' As
         end
    end
  in
  let st := constr:((Ts, Ss, Sv)) in
  let r := gather st exp in
  r.

Ltac reflect_state refl_const RS RD exp :=
  let Ts := eval simpl in (Typs RS) in
  let Ss := eval simpl in (Sym_type RS) in
  let Sv := eval simpl in (Sym_denote RD) in
  let E := gather_symbols refl_const Ts Ss Sv exp in
  match E with
    | ( ?Ts , ?Ss , ?Sv ) =>
      let constsOf := eval simpl in (constsOf RS) in
      let rs := constr:({| Typs       := Ts 
                         ; constsOf   := constsOf
                         ; Sym_type   := Ss
                         |}) in
      let RS := fresh "RS" in
      pose (RS := rs) ;
      let constIn := eval simpl in (constIn RD) in
      let rd := constr:(Build_ReflDenote RS constIn Sv) in
      let RD := fresh "RD" in
      pose (RD := rd) ;
      let Vs := constr:(@nil nat) in
      let Vv := constr:(tt) in
      let r := reflect_expr refl_const RS Ts Ss Sv Vs Vv exp in
      let r' := r in
      pose r'
  end.

Goal (nat -> nat) -> (nat -> Prop) -> True.
intros H P.
  match goal with
    | [ |- _ ] =>
      let exp := constr:(@eq nat (H 1) 1) in
      reflect_state refl_nat_const ReflSpine_nat ReflDenote_nat exp
  end.
trivial.
Qed.
