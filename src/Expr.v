Require Import String.
Require Import (*Data*) List.
(*Require Import SepTheory.*)

Set Implicit Arugments.
Set Strict Implicit.

(*
Fixpoint prod (ls : list Type) : Type :=
  match ls with
    | nil => unit
    | a :: b => a * prod b
  end%type.

Fixpoint prodN (T : Type) (n : nat) : Type :=
  match n with
    | 0 => unit
    | S n => T * prodN T n
  end%type.
*)

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

Record ReflState (Typ : Type) : Type :=
{ Typs          : list (Typ * Type)
; Typ_denote    : Typ -> Type
; constsOf      : Typ -> Type
; constsIn      : forall T, constsOf T -> Typ_denote T
; Sym_type      : list (list Typ * option Typ)
; Sym_denote    : Env (funtype' Typ_denote (Typ_denote' Typ_denote)) Sym_type
}.

Require Import Arith.

Inductive empty : Type := .

Definition ProverT T (RS : ReflState T) :=
  forall SymT_ext SymD_ext
    (Hs : list (QExpr (constsOf _ RS) (Sym_type _ RS ++ SymT_ext))),
    Env (denoteQExpr _ _ (constsIn _ RS) (Sym_type _ RS ++ SymT_ext) (Env_app _ (Sym_denote _ RS) SymD_ext)) Hs -> 
    forall (G : Expr (constsOf _ RS) (Sym_type _ RS ++ SymT_ext) nil None),
      option (denoteExpr _ (Sym_type _ RS ++ SymT_ext) nil (Typ_denote _ RS) (constsIn _ RS) (Env_app _ (Sym_denote _ RS) SymD_ext) tt None G).

Definition ReflState_nat : ReflState nat :=
{| Typs       := (0, nat:Type) :: @nil (nat * Type)
 ; Typ_denote := fun x => if eq_nat_dec x 0 then nat else unit
 ; constsOf   := fun x => if eq_nat_dec x 0 then nat else empty
 ; constsIn   := fun T => match T with
                            | 0 => fun x => x
                            | _ => fun x => match x with
                                            end
                          end
 ; Sym_type   := (0 :: 0 :: nil, Some 0) :: (0 :: 0 :: nil, None) :: nil
 ; Sym_denote := (plus, (@eq nat, tt))
 |}.

Definition nat_prover SymT_ext SymD_ext
  (Hs : list (QExpr (constsOf _ ReflState_nat) (Sym_type _ ReflState_nat ++ SymT_ext)))
  (Hpfs : Env (denoteQExpr _ _ (constsIn _ ReflState_nat) (Sym_type _ ReflState_nat ++ SymT_ext) (Env_app _ (Sym_denote _ ReflState_nat) SymD_ext)) Hs)
  (G : Expr (constsOf _ ReflState_nat) (Sym_type _ ReflState_nat ++ SymT_ext) nil None) :
  option (denoteExpr _ (Sym_type _ ReflState_nat ++ SymT_ext) nil (Typ_denote _ ReflState_nat) (constsIn _ ReflState_nat) (Env_app _ (Sym_denote _ ReflState_nat) SymD_ext) tt None G).
Admitted.

(** TODO : Reflection **)

(*
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

Ltac refl_fun_type env T :=
  match T with
    | ?T1 -> ?T2 => 
      match refl_type env 0 T1 with
        | ( ?t1 , ?env' ) =>
          match refl_fun_type env' T2 with
            | ( ( ?AS , ?RT ) , ?E ) => constr:(((t1 :: AS , RT), E))
          end
      end
    | _ =>
      let v := refl_type env 0 T in
      match v with
        | ( ?I , ?E ) => 
          constr:(((@nil nat, I), E))
      end
  end.

Ltac extend n T cc :=
  constr:(fun x : nat => if Peano_dec.eq_nat_dec x n then T else cc x).

Ltac List2Fun ls i :=
  match ls with
    | nil => constr:(fun _ : nat => unit)
    | ?A :: ?B => 
      let ni := constr:(S i) in
      let rr := List2Fun B ni in
      extend i A rr
  end.

(*
Ltac reflect_expr ext e :=
  let rec refl_expr sts stv e :=
    let sts_orig := sts in
    let gen_refl e :=
      match e with
        | ?F ?A => 
          let m := lookup F sts stv in
          match m with
            | ( ?m , ?ss , ?sv , ?L ) =>
              let sts := ss in
              let stv := sv in
              let a := refl_expr sts stv A in
              match a with
                | ( ?a , ?ss , ?sv , ?L' ) =>
                  let args := constr:(Econs Sym_type ss _ _ a (Enil Sym_type ss)) in
                  let v := constr:(App Sym_type ss _ (L' _ m) args) in
                  let cc := constr:(fun x : Expr sts_orig _ => L' _ (L _ x)) in
                  constr:((v , ss, sv , cc))
              end
          end
      end
    in 
    let k := ext refl_expr gen_refl sts stv e in
    match k with
      | ( _ , _ , _ , _ ) => k
      | _ => constr:(( k , sts , stv , tt , fun x : Expr _ sts => x ))
    end
  in
  let ns := constr:(@nil (list nat * nat)) in
  let ss := constr:(ns) in
  let vs := constr:(tt) in
  let r := refl_expr ss vs e in
  r.
*)

Ltac lookup_cc x es ev f s :=
  match ev with
    | ( x , _ ) => 
      match es with
        | ?T :: ?TS =>
          let r := constr:(@MHere _ T TS) in s r
      end
    | ( _ , ?R ) =>
      match es with
        | ?T :: ?TS =>
          let scc r := 
            let k := constr:(@MNext _ _ T TS r) in s k
          in
          lookup_cc x TS R f scc          
      end
    | tt => f x
  end.

Ltac reflect_expr Sym_fun ext Ts Ss Sv e :=
  let rec refl_expr e :=
    let gen_refl e :=
      let fcc _ :=
        match e with 
          | ?F ?A => 
            let m := lookup F Ss Sv in
            let a := refl_expr A in 
            let args := constr:(Econs Sym_fun Ss _ _ a (Enil Sym_fun Ss)) in
            let r := constr:(@App _ _ Sym_fun Ss _ _ m args) in
            r
        end
      in
      let scc m := 
        constr:(App Sym_fun Ss _ _ m (Enil Sym_fun Ss))
      in
      lookup_cc e Ss Sv fcc scc
    in 
    ext Sym_fun Ss refl_expr gen_refl e
  in
  refl_expr e.

(** lookup "x" in "Vs" (spine of Vs is given in Ts, denotation of Ts given in E) **)
Ltac lookup_or_add E Ts Vs x :=
  match Vs with
    | ( x , _ ) => constr:(((Ts, Vs), E))
    | tt => 
      let t := type of x in
      match refl_fun_type E t with
        | ( ?T , ?E ) =>
          constr:(((T :: nil, (x, tt)), E))
      end
    | ( ?V , ?VS ) =>
      match Ts with
        | ?T :: ?Ts =>
          match lookup_or_add E Ts Vs x with
            | ( (?Ts , ?Vs) , ?E ) => constr:(((T :: Ts, (V, Vs)), E))
          end
      end
  end.

Ltac lookup_or_add' st x :=
  match st with
    | ( ?A , ?B , ?E ) => lookup_or_add E A B x
  end.

Ltac gather_symbols ext Ts Ss Vs exp :=
  let rec gather st e :=
    let gen_refl e :=
      match e with
        | ?F ?A =>
          let st' := lookup_or_add' st F in
          let st'' := gather st' A in
          st''
      end
    in 
    let k := ext gather gen_refl st e in
    k
  in
  let st := constr:((Ss, Vs, Ts)) in
  let r := gather st exp in
  r.


Inductive Sym_nat :=
| Nat : nat -> Sym_nat
| Plus : Sym_nat.

Definition Nat_type (s : Sym_nat) : list nat * nat :=
  match s with
    | Nat _ => (nil , 0)
    | Plus => (0 :: 0 :: nil, 0)
  end.

Ltac nat_gather recur cc env exp :=
  match exp with
    | 0 => env
    | S _ => env     
    | ?X + ?Y => 
      let st := recur env X in recur st Y
    | _ => cc exp
  end.

Ltac nat_refl Sym_fun Ss recur cc e :=
  match e with 
    | O   => 
      let args := constr:(@Enil _ _ Sym_fun Ss) in
      let f := constr:(@App _ _ Sym_fun Ss (Nat 0) args) in f
    | S _ => constr:(@App _ _ Sym_fun Ss (Nat e) (Enil Sym_fun Ss))
    | plus ?X ?Y =>
      let l := recur X in
      let r := recur Y in
      constr:(App Sym_fun Ss Plus (Econs Sym_fun Ss _ _ l (Econs Sym_fun Ss _ _ r (Enil Sym_fun Ss))))
    | _ => cc e
  end.

Fixpoint List2Fun_g (ls : list Type) (n : nat) : nat -> Type :=
  match ls with
    | nil => fun _ => unit
    | a :: b => 
      let r := List2Fun_g b (S n) in
      fun x => if Peano_dec.eq_nat_dec x n then a else r x
  end.

Ltac reflect_state S gather_ext refl_ext exp :=
  let Ts := constr:(@nil (list nat * nat)) in (* eval simpl in (Native_type S) in *)
  let Vs := constr:(tt) in (* eval simpl in (Native_denote S) in *)
  let Tys := eval simpl in (Typs S) in
  let Sym_type := eval simpl in (Native_type S) in
  let E := gather_symbols gather_ext Tys Ts Vs exp in
  match E with
    | ( ?Ss , ?Sv , ?Ts ) =>
      let r := reflect_expr Sym_type refl_ext Ts Ss Sv exp in
      let st' := constr:({| Typs := Ts ; Typ_denote := List2Fun_g Ts 0 ; 
                            Native := Native S ; Native_type := Native_type S ;
                            Native_denote := Native_denote S |}) in
      pose st' ;
      let r' := eval simpl in r in
        pose r'
  end.

Definition NatReflEnv : ReflState := Eval simpl in
{| Typs := @cons Type nat nil
 ; Typ_denote := List2Fun_g (@cons Type nat nil) 0
 ; Native     := Sym_nat
 ; Native_type := Nat_type
 ; Native_denote := 
   fun x => 
     match x with
       | Nat n => n
       | Plus => plus
     end
(*
 ; sym_types := nil
 ; sym_denote := tt
*)
|}.

Goal (nat -> nat) -> True.
intro H.
  match goal with
    | [ |- _ ] =>
      let exp := constr:(H (H 1) + 1) in
      reflect_state NatReflEnv nat_gather nat_refl exp
  end. simpl in *.

  

trivial.
Qed.
*)