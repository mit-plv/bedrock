Require Import String.
Require Import Data List.
Require Import SepTheory.

Set Implicit Arugments.
Set Strict Implicit.

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

Section FunType.
  Context {T : Type}.
  Variable D : T -> Type.

  Fixpoint funtype (ls : list T) (r : T) : Type :=
    match ls with 
      | nil => D r
      | a :: b => D a -> funtype b r
    end.

  (** This is a fixed point so coq unfolds it more often. **)
  Fixpoint funtype' (x : list T * T) {struct x} : Type :=
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

End Member.

(** Syntax of Expressions **)
Section TypedList.
  Context {Typ Sym : Type}.
  Variable Sym_type : Sym -> list Typ * Typ.

  Variable ss : list (list Typ * Typ).
  Variable vs : list Typ.

  Inductive Expr : Typ -> Type := 
    (** variables **)
  | Var  : forall T, Mem T vs -> Expr T
    (** known functions **)
  | App  : forall (S : Sym), Exprs (fst (Sym_type S)) -> Expr (snd (Sym_type S))
    (** "uninterpreted functions" **)
  | UApp : forall Ts T, Mem (Ts,T) ss -> Exprs Ts -> Expr T
  with Exprs : list Typ -> Type :=
  | Enil  : Exprs nil
  | Econs : forall T Ts, Expr T -> Exprs Ts -> Exprs (T :: Ts)
  .

  Section Denote.
    Variable Typ_denote : Typ -> Type.
    Variable Sym_denote : forall (S : Sym), funtype Typ_denote (fst (Sym_type S)) (snd (Sym_type S)).
    
    Variable SE : Env (funtype' Typ_denote) ss.
    Variable VE : Env Typ_denote vs.

    Fixpoint denoteExpr {T : Typ} (e : Expr T) : Typ_denote T :=
      match e with
        | Var _ v => get _ _ v VE
          
        | UApp Ts T s es =>
          (fix denoteExprs Ts T (es : Exprs Ts) : funtype Typ_denote Ts T -> Typ_denote T :=
            match es with
              | Enil => fun r => r
              | Econs _ _ x y => fun f => denoteExprs _ _ y (f (denoteExpr x))
            end) Ts T es (get (funtype' Typ_denote) ss s SE)
        | App s es =>
          (fix denoteExprs Ts T (es : Exprs Ts) : funtype Typ_denote Ts T -> Typ_denote T :=
            match es in Exprs Ts return funtype Typ_denote Ts T -> Typ_denote T with
              | Enil => fun r => r
              | Econs _ _ x y => fun f => denoteExprs _ _ y (f (denoteExpr x))
            end) (fst (Sym_type s)) (snd (Sym_type s)) es (Sym_denote s)
      end.
  
  End Denote.
End TypedList.

Section Lifting.
  Context {Typ Sym : Type}. 
  Variable Sym_type : Sym -> list Typ * Typ.
  Variable (ss sse : list (list Typ * Typ)). 
  Variable (vs vse : list Typ).

  Fixpoint liftExpr T (e : Expr Sym_type ss vs T) : Expr Sym_type (sse ++ ss) (vse ++ vs) T :=
    match e with
      | Var _ v => Var _ _ _ _ (lift vs vse v)
      | UApp Ts T s es =>
        let es' :=       
          (fix liftExprs Ts (es : Exprs Sym_type ss vs Ts) : Exprs Sym_type (sse ++ ss) (vse ++ vs) Ts :=
            match es with
              | Enil => Enil Sym_type (sse ++ ss) (vse ++ vs)
              | Econs _ _ x y => Econs _ _ _ _ _ (liftExpr _ x) (liftExprs _ y)
            end) Ts es
          in
          UApp _ _ _ Ts T (lift ss sse s) es'
      | App s es =>
        let es' :=       
          (fix liftExprs Ts (es : Exprs Sym_type ss vs Ts) : Exprs Sym_type (sse ++ ss) (vse ++ vs) Ts :=
            match es with
              | Enil => Enil Sym_type (sse ++ ss) (vse ++ vs)
              | Econs _ _ x y => Econs _ _ _ _ _ (liftExpr _ x) (liftExprs _ y)
            end) (fst (Sym_type s)) es
        in
        App _ _ _ s es'
    end.
End Lifting.

Record ReflState : Type :=
{ Typ : Type
; Typ_denote : Typ -> Type
; sym_types  : list (list Typ * Typ)
; sym_denote : Env (funtype' Typ_denote) sym_types
}.

(** Ltac "lookup a symbol in an Env" **)
Ltac lookup x es ev :=
  match ev with
    | ( x , _ ) => 
      match es with
        | ?T :: ?TS =>
          let r := constr:(@MHere T TS) in r
      end
    | ( _ , ?R ) =>
      match es with
        | ?T :: ?TS =>
          let r := lookup x TS R in
          constr:(@MNext T TS r)
      end
  end.

Inductive Sym_nat :=
| Nat : nat -> Sym_nat
| Plus : Sym_nat.

Definition Sym_type (s : Sym_nat) : list nat * nat :=
  match s with
    | Nat _ => (nil , 0)
    | Plus => (0 :: 0 :: nil, 0)
  end.

About Econs.

Ltac reflect_expr ext ss sv vs vv e :=
  let rec refl_expr ss sv vs vv e :=
    let gen_refl sts stv e :=
      match constr:(sts, stv) with 
        | ( ( ?ss , ?sv) , (?vs , ?vv ) ) =>
          match e with
            | _ => 
              let m := lookup e vs vv in
              constr:(Var Sym_type ss vs _ m)
            | ?F ?A ?B =>
              let m := lookup F ss sv in
              let a := reflect_expr ext vs vv ss sv A in
              match a with
                | ( ?a , (_ , _) , (_ , _) ) => 
                  let b := reflect_expr ext vs vv ss sv B in
                  match b with
                    | ( ?b , (_ , _) , (_ , _) ) =>
                      let args := constr:(Econs Sym_type ss vs _ _ a (Econs Sym_type ss vs _ _ b (Enil Sym_type ss vs))) in
                      constr:(UApp Sym_type ss vs _ m args)
                  end
              end
          end
      end
    in 
    let sts := constr:((ss, vs)) in
    let stv := constr:((sv, vv)) in
    let k := ext (* ?? *) gen_refl sts stv e in
    match k with
      | ( _ , _ , _ ) => k
      | _ => constr:( k , ( ss , vs ) , (sv , vv ) )
    end
  in
  let r := refl_expr ss sv vs vv e in
  match r with
    | ( ?X , (_ , _) , (_ , _) ) => X
  end.

Ltac nat_refl recur cc sts stv e :=
  match sts with
    | ( ?ss , ?vs ) =>
      match e with 
        | O => constr:(App Sym_type ss vs (Nat 0) (Enil Sym_type ss vs))
        | S _ => constr:(App Sym_type ss vs (Nat e) (Enil Sym_type ss vs))
        | plus ?X ?Y =>
          let l := recur sts stv X in
          match l with
            | ( ?l , ?sts , ?stv ) =>
              let r := recur sts stv Y in
              match r with
                | ( ?r , ( ?ss , ?vs ) , _ ) =>
                  constr:(App Sym_type ss vs Plus (Econs Sym_type ss vs _ _ l (Econs Sym_type ss vs _ _ r (Enil Sym_type ss vs))))
              end
          end
        | _ => cc e
      end
  end.

Ltac alwaysFail x := fail.

Goal True.
  match goal with
    | [ |- _ ] =>
      let e := constr:(tt) in
      let exp := constr:(1 + 1) in
      let ns := constr:(@nil (list nat * nat)) in
      let nv := constr:(@nil nat) in
      let r := nat_refl (nat_refl alwaysFail) in
(*      let r := reflect_expr nat_refl ns e nv e exp in *)
      pose r
  end.
        


(*
Definition StateDef := list { T : Type & T }.

Notation "$ a" := (@existT Type (fun x => x) _ a) (at level 0).

Theorem foo : forall a : nat, a = a.
  intros; reflexivity.
Qed.


Definition MyState : ReflState.
cut (($ foo) :: nil = nil); intros.
  Ltac refl t :=
    let rec refl_type T Ts nx :=
      match Ts with
        | T :: _ => 
          constr:(nx , Ts)
        | ?A :: ?R => 
          let nx' := constr:(S nx) in
          let r := refl_type T R nx' in
          match r with
            | ( ?L , ?R ) => constr:( L , A :: R )
          end
        | nil =>
          constr:(nx , T :: nil)
      end        
    in
    let rec refl_sym_type Typs sT :=
      match type of sT with
        | ?A -> ?B => 
          match refl_type A Typs 0 with
            | ( ?Typs , ?T ) => 
              match refl_sym_type Typs B with
                | ( ?Typs , (?L , ?R) ) =>
                  constr:((Typs, (T :: L , R)))
              end
          end
      end
    in
    let rec refl_sym Syms s :=
      match Syms with
        | 
      end
    in
    let rec refl_term Tys Syms t :=
      match t with
        | forall x : ?T , @?P x => idtac P
        | ?S ?A ?B => 
          let ra := refl_term Tys Syms A in
          match ra with
            | ( ?Tys , ?Syms , ?RA ) =>
              let rb := refl_term Tys Syms B in
              match rb with
                | ( ?Tys , ?Syms , ?RB ) =>
                  constr:( Tys , Syms , 
      end
    in
    let rec refl_rec t :=
      match t with
        | @existT ?A ?B ?T ?X :: ?R =>
          let h := constr:(@existT A B T X) in
          let r := refl_rec R in
          let f := constr:(@cons (@sigT Type (fun x => x)) h r) in 
          f
        | nil => 
          constr:(@nil (@sigT Type (fun x => x)))
      end
    in refl_rec t.
  match goal with
    | [ H : ?X = _ |- _ ] => 
      let k := refl X in
        idtac k
  end.



Section Extensible.
  Definition Typ := nat.

(*
  Fixpoint Typ_eq_dec (a b : Typ) {struct a} : {a = b} + {a <> b}.
  decide equality.
  Defined.
*)

  Definition Typ_denote (f : Typ) : Type :=
    match f with
      | 0 => nat
      | _ => unit
    end.

  Inductive Nat_sym : Type :=
  | Nat : nat -> Nat_sym
  | Plus : Nat_sym.

  Definition Sym_type_Nat (x : Nat_sym) : list Typ * Typ :=
    match x with
      | Nat _ => (nil, 0)
      | Plus => (0 :: 0 :: nil, 0)
    end.

  Definition Sym_denote_nat (f : Nat_sym) : option (funtype' Typ_denote (Sym_type_Nat f)) :=
    match f with
      | Plus => Some plus
      | Nat i => Some i 
    end.

End Extensible.
*)
(*
Check App2.

Ltac refl_nat e :=
  let rec refl e := 
    match e with
      | plus ?L ?R => 
        let l := refl L in
        let r := refl R in
        let r' := constr:(@App2 Typ Sym_nat nil Nat Nat Nat Plus l r) in r'
      | S _ => let r := constr:(@App0 _ _ nil Nat (Lit e)) in r
      | O => let r := constr:(@App0 _ _ nil Nat (Lit e)) in r
    end
  in 
  idtac e; 
  let res := refl e in
  idtac res;
  generalize (res).

Check map.

Fixpoint simplify_nat g (e : Expr Typ Sym_nat g Nat) {struct e} : Expr Typ Sym_nat g Nat :=
  match e return Expr Typ Sym_nat g Nat with
    | App2 _ _ _ c l r =>
      match c in Sym_nat T R return prod (@map Typ Type (Expr Typ Sym_nat g) T) -> Expr Typ Sym_nat g Nat with
        | Plus => fun lr =>
          let l := fst lr in
          let r := fst (snd lr) in
          match simplify_nat g l , simplify_nat g r return Expr Typ Sym_nat g Nat with
            | App0 _ (Lit l) , App0 _ (Lit r) => e (*App0 _ (Lit (l + r)) *)
            | l , r => e (*App2 _ _ _ Plus l r *)
          end
        | _ => fun _ => e
      end (l,(r,tt))
    | App0 _ (Lit _) => e 
    | _ => e
  end.


Goal 1 + 0 = 1.



match goal with 
  | [ |- ?X = ?Y ] => idtac X; refl_nat X
end.





refl_nat constr:(1).
*)