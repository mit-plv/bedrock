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
(*  Variable vs : list Typ. *)

  Inductive Expr : Typ -> Type := 
(** Variables are just uninterpreted 0 argument functions 
    (** variables **)
  | Var  : forall T, Mem T vs -> Expr T
**)
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

    Fixpoint denoteExpr {T : Typ} (e : Expr T) : Typ_denote T :=
      match e with
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

  Fixpoint liftExpr T (e : Expr Sym_type ss T) : Expr Sym_type (sse ++ ss) T :=
    match e with
      | UApp Ts T s es =>
        let es' :=       
          (fix liftExprs Ts (es : Exprs Sym_type ss Ts) : Exprs Sym_type (sse ++ ss) Ts :=
            match es with
              | Enil => Enil Sym_type (sse ++ ss)
              | Econs _ _ x y => Econs _ _ _ _ (liftExpr _ x) (liftExprs _ y)
            end) Ts es
          in
          UApp _ _ Ts T (lift ss sse s) es'
      | App s es =>
        let es' :=       
          (fix liftExprs Ts (es : Exprs Sym_type ss Ts) : Exprs Sym_type (sse ++ ss) Ts :=
            match es with
              | Enil => Enil Sym_type (sse ++ ss)
              | Econs _ _ x y => Econs _ _ _ _ (liftExpr _ x) (liftExprs _ y)
            end) (fst (Sym_type s)) es
        in
        App _ _ s es'
    end.
End Lifting.

Record ReflState : Type :=
{ Typs          : list Type
; Typ_denote    : nat -> Type
; Native        : Type 
; Native_type   : Native -> (list nat * nat)
; Native_denote : forall x : Native, funtype' Typ_denote (Native_type x)
; sym_types     : list (list nat * nat)
; sym_denote    : Env (funtype' Typ_denote) sym_types
}.

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
                  let v := constr:(UApp Sym_type ss _ (L' _ m) args) in
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
            constr:(UApp Sym_fun Ss _ _ m args)
        end
      in
      let scc m := 
        constr:(UApp Sym_fun Ss _ _ m (Enil Sym_fun Ss))
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
    | _ => idtac e ; cc e
  end.

Fixpoint List2Fun_g (ls : list Type) (n : nat) : nat -> Type :=
  match ls with
    | nil => fun _ => unit
    | a :: b => 
      let r := List2Fun_g b (S n) in
      fun x => if Peano_dec.eq_nat_dec x n then a else r x
  end.

Ltac reflect_state S gather_ext refl_ext exp :=
  let Ts := eval simpl in (sym_types S) in
  let Vs := eval simpl in (sym_denote S) in
  let Tys := eval simpl in (Typs S) in
  let Sym_type := eval simpl in (Native_type S) in
  let E := gather_symbols gather_ext Tys Ts Vs exp in
  match E with
    | ( ?Ss , ?Sv , ?Ts ) =>
      idtac Ss Sv Ts Sym_type ;
      let r := reflect_expr Sym_type refl_ext Ts Ss Sv exp in
        pose r
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
 ; sym_types := nil
 ; sym_denote := tt
|}.

Goal (nat -> nat) -> True.
intro H.
Set Printing Implicit.
  match goal with
    | [ |- _ ] =>
      let exp := constr:(1 + 0) in
      reflect_state NatReflEnv nat_gather nat_refl exp
  end.

trivial.
Qed.
        


(*

(*
      let Ts := constr:(@nil (list nat * nat)) in
      let Vs := constr:(tt) in
      let Tys := constr:(nat :: nil) in
      let E := gather_symbols nat_gather Tys Ts Vs exp in
      match E with
        | ( ?Ss , ?Sv , ?Ts ) => 
          idtac "OFO"; 
          let r := reflect_expr Nat_type nat_refl Ts Ss Sv exp in
          r
      end
*)


(** lookup the symbol x in the environment ev (with a spine of es).
 ** - assume that evI is the start of the entire environment (with esI as the spine)
 **)
Ltac lookup_sym x esI evI ts es ev :=
  match ev with
    | nil => 
      let T := type of x in
      let t := refl_fun_type ts T in
      let r := constr:((@MHere esI evI, T :: esI, (x, evI), @liftExpr _ _ _ esI (T :: nil) _, @lift _ (T :: nil) _)) in
      r
    | ( x , _ ) => 
      match es with
        | ?T :: ?TS =>
          let r := constr:(@MHere T TS) in r
      end
    | ( _ , ?R ) =>
      match es with
        | ?T :: ?TS =>
          let r := lookup x esI evI TS R in
          match r with
            | ( _ , _ , _ , _ ) => r
            | _ => constr:(@MNext T TS r)
          end
      end
  end.

Ltac lookup' x es ev :=
  lookup_sym x es ev es ev.



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