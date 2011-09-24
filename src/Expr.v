Require Import String.
Require Import List.
(*Require Import SepTheory.*)

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

End Member.

(** Syntax of Expressions **)
Section TypedList.
  Context {Typ : Type}.

  Variable constsOf : Typ -> Type.
  Hypothesis dec : forall T (x y : constsOf T), {x = y} + {x <> y}.

  Variable ss : list (list Typ * option Typ).
  Variable vs : list Typ.

  Inductive Expr : option Typ -> Type := 
    (** variables **)
  | Var  : forall T, Mem T vs -> Expr (Some T)
    (** functions **)
  | App : forall Ts T, Mem (Ts,T) ss -> Exprs Ts -> Expr T
    (** constants **)
  | Const : forall T, constsOf T -> Expr (Some T)
  with Exprs : list Typ -> Type :=
  | Enil  : Exprs nil
  | Econs : forall T Ts, Expr (Some T) -> Exprs Ts -> Exprs (T :: Ts)
  .

  (** TODO: Equality on Expr **)

  Section Denote.
    Variable Typ_denote : Typ -> Type.
    Variable constIn : forall T, constsOf T -> Typ_denote T.
    
    Definition Typ_denote' (o : option Typ) : Type :=
      match o with
        | None => Prop
        | Some t => Typ_denote t
      end.

    Variable SE : Env (funtype' Typ_denote Typ_denote') ss.
    Variable VE : Env (Typ_denote) vs.

    Fixpoint denoteExprs Ts T (es : Exprs Ts) : funtype Typ_denote Typ_denote' Ts T -> Typ_denote' T :=
      match es with 
        | Enil => fun r => r
        | Econs _ _ x y => fun f => denoteExprs _ _ y (f (denoteExpr _ x))
      end
    with denoteExpr T (e : Expr T) : Typ_denote' T :=
      match e with 
        | Var _ m => get _ _ m VE
        | App Ts T s es =>
          denoteExprs Ts T es (get (funtype' Typ_denote Typ_denote') ss s SE)
        | Const _ x => constIn _ x 
      end.
  
  End Denote.
End TypedList.

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
(*
      | App s es =>
        let es' := liftExprs (fst (constsOf s)) es in
        App _ _ s es'
*)
      | Const a b => Const constsOf _ _ a b
      | Var _ m => Var _ _ _ _ (lift vs ve m)  
    end
  with liftExprs Ts (es : Exprs constsOf ss vs Ts) : Exprs constsOf (sse ++ ss) (ve ++ vs) Ts :=
    match es with
      | Enil => Enil constsOf (sse ++ ss) (ve ++ vs)
      | Econs _ _ x y => Econs constsOf _ _ _ _ (liftExpr _ x) (liftExprs _ y)
    end.
    
End Lifting.

Section QExpr.
  Context {Typ : Type}.
  Variable (constsOf : Typ -> Type).

  Definition QExpr ss := 
    { x : list Typ & Expr constsOf ss x None }.

  Variable (Typ_denote : Typ -> Type). 

  Fixpoint denoteQuant (ls : list Typ) : (Env Typ_denote ls -> Prop) -> Prop :=
    match ls as ls return (Env Typ_denote ls -> Prop) -> Prop with
      | nil => fun cc => cc tt
      | a :: b => fun cc => 
        forall (x : Typ_denote a), denoteQuant b (fun g => cc (x, g))
    end.

  Variable constIn : forall T, constsOf T -> Typ_denote T.    
  Variable ss : list (list Typ * option Typ).
  Variable SE : Env (funtype' Typ_denote (Typ_denote' Typ_denote)) ss.

  Definition denoteQExpr (p : QExpr ss) : Prop :=
    denoteQuant (projT1 p) 
      (fun x : Env Typ_denote (projT1 p) => denoteExpr constsOf ss (projT1 p) Typ_denote constIn SE x None (projT2 p)).
End QExpr.

Inductive empty : Type := .

Require Import Arith.

Fixpoint List2Fun_g (ls : list Type) (n : nat) : nat -> Type :=
  match ls with
    | nil => fun _ => unit
    | a :: b => 
      let r := List2Fun_g b (S n) in
      fun x => if Peano_dec.eq_nat_dec x n then a else r x
  end.

Record ReflState : Type :=
{ Typs        : list Type
; Typ_denote  := List2Fun_g Typs 0
; constsOf    : nat -> Type
; constsIn    : forall T, constsOf T -> Typ_denote T
; Sym_type    : list (list nat * option nat)
; Sym_denote  : Env (funtype' Typ_denote (Typ_denote' Typ_denote)) Sym_type
}.

Definition ProverT (RS : ReflState) :=
  forall SymT_ext SymD_ext
    (Hs : list (QExpr (constsOf RS) (Sym_type RS ++ SymT_ext))),
    Env (denoteQExpr _ _ (constsIn RS) (Sym_type RS ++ SymT_ext) (Env_app _ (Sym_denote RS) SymD_ext)) Hs -> 
    forall (G : Expr (constsOf RS) (Sym_type RS ++ SymT_ext) nil None),
      option (denoteExpr _ (Sym_type RS ++ SymT_ext) nil (Typ_denote RS) (constsIn RS) (Env_app _ (Sym_denote RS) SymD_ext) tt None G).

Definition ReflState_nat : ReflState :=
  let typs := (nat:Type) :: @nil Type in
  let constsOf := fun x : nat => if eq_nat_dec x 0 then nat else empty in
  let Typ_denote := List2Fun_g typs 0 in
  {| Typs       := typs
   ; constsOf   := constsOf
   ; constsIn   := fun T => match T as T return constsOf T  -> Typ_denote T with
                              | 0 => fun x => x
                              | _ => fun x => match x with
                                              end
                            end
   ; Sym_type   := (0 :: 0 :: nil, Some 0) :: (*0 :: 0 :: nil, None) ::*) nil
   ; Sym_denote := (plus, tt)
   |}.

Definition nat_prover : ProverT ReflState_nat. 
Admitted.


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
About App.

Ltac reflect_expr refl_const constsOf Ts Ss Sv Vs Vv e :=
  let aT := constr:(@nil Type) in
  let rec refl_expr e :=
    let app_case e :=
      match e with 
        | ?F ?A ?B ?C => 
          let Ft := type of F in
          let args' := constr:((A, (B, (C, tt)))) in
          let ra := reflect_args F aT Ft args' in
          match ra with 
            | ( ?args, ?F' ) =>
              let m := lookup F' Ss Sv in
              constr:(@App _ constsOf Ss Vs _ _ m args)
          end

        | ?F ?A => 
          let Ft := type of F in
          let args' := constr:((A, tt)) in
          match reflect_args F aT Ft args' with
            | ( ?args, ?F' ) =>
              let m := lookup F' Ss Sv in
              constr:(@App _ constsOf Ss Vs _ _ m args)
          end
      end
    in
    let var_case m := 
      constr:(Var constsOf Ss Vs _ m)
    in
    let const_case m :=
      let T := type of e in
      match refl_type Ts 0 T with
        | ( ?rT , _ ) =>  (** the second component should be equal to Ts **)
          constr:(@Const _ constsOf Ss Vs rT m)
      end
    in
    refl_const const_case app_case e
  with reflect_args F Typs Ft As :=
    match As with
      | tt =>
        constr:((Enil constsOf Ss Vs, F))
      | ( ?A , ?As ) => 
        match Ft with
          | ?T1 -> ?T2 => 
            let Typs' := constr:(Typs ++ (T1:Type) :: @nil Type) in
            match reflect_args F Typs' T2 As with
              | ( ?res , ?F' ) => 
                match refl_type Ts 0 T1 with
                  | ( ?rT , _ ) =>
                    let Ae := refl_expr A in
                    constr:((Econs constsOf Ss Vs rT _ Ae res , F'))
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
    let fcc _ :=
      match e with
        | ?F ?A ?B ?C =>
          let T := type of F in
          let As := constr:((A, (B, (C, tt)))) in
          let Typs := constr:(@nil Type) in
          gather_args F Typs T As st
        | ?F ?A => 
          let T := type of F in
          let As := constr:((A, tt)) in
          let Typs := constr:(@nil Type) in
          gather_args F Typs T As st

      end
    in
    let scc _ := st in
    refl_const scc fcc e
  with gather_args F Typs Ft As st :=
    match As with
      | tt => 
        let st' := set_add' st F in
        st'
      | ( ?A , ?As ) => 
        match Ft with
          | ?T1 -> ?T2 =>
            let Typs' := constr:(Typs ++ (T1:Type) :: @nil Type) in
            let st' := gather st A in
            gather_args F Typs' T2 As st' 
          | forall x : ?T1, @?T2 x =>
            let Ft' := eval simpl in (T2 A) in
            let F'' := eval simpl in (apply_ls Typs T1 T2 A F) in
            gather_args F'' Typs Ft' As st
         end
    end
  in
  let st := constr:((Ts, Ss, Sv)) in
  let r := gather st exp in
  r.

Ltac reflect_state refl_const S exp :=
  let Ts := eval simpl in (Sym_type S) in
  let Vs := eval simpl in (Sym_denote S) in
  let Tys := eval simpl in (Typs S) in
  let constsOf := eval simpl in (constsOf S) in
  let E := gather_symbols refl_const Tys Ts Vs exp in
  match E with
    | ( ?Ts , ?Ss , ?Sv ) =>
      idtac "Ts" Ts ;
      idtac "Ss" Ss ;
      idtac "Sv" Sv ;
      let Vs := constr:(@nil nat) in
      let Vv := constr:(tt) in
      let r := reflect_expr refl_const constsOf Ts Ss Sv Vs Vv exp in
      let st' := constr:({| Typs       := Ts 
                          ; constsOf   := constsOf
                          ; constsIn   := constsIn S
                          ; Sym_type   := Ss
                          ; Sym_denote := Sv
                          |}) in
      pose st' ;
      let r' := r in
      pose r'
  end.

Goal (nat -> nat) -> (nat -> Prop) -> True.
intros H P.
Set Printing Implicit.
  match goal with
    | [ |- _ ] =>
      let exp := constr:(@eq nat (H 1) 1) in
      reflect_state refl_nat_const ReflState_nat exp
  end.
trivial.
Qed.
