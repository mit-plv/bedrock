(** Reusable Ltac procedures:
 ** - reflecting function applications
 ** - list lookup
 ** - 
 **)
Require Import List Env.

Set Implicit Arguments.

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

(** Reflect an application
 ** - reflects all the non-dependent arguments of e into a tuple
 ** - the tuple and the resulting function (may be partially applied)
 **   are passed to the continuation [cc]
 **) 
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
(** TODO : extend this to handle abstracted terms
      | fun x => (@?A x) (@?B x) =>
        let Ta := type of A in
        match type of A with
          | _ -> _ -> ?TT => 
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
*)
      | _ =>
        let Ts := constr:(@nil Type) in
        cc e Ts As
    end
  in
  let b := constr:(tt) in
  refl cc e b.

(** Set operations **)
Ltac contains e s :=
  match s with
    | nil => false
    | e :: _ => true
    | _ :: ?b => contains e b
    | ?X ++ ?Y => match contains e X with
                    | true => true
                    | false => contains e Y 
                  end
  end.

Ltac cons_uniq e s :=
  match contains e s with
    | false => constr:(e :: s)
    | false => 
      match type of s with
        | list ?T => constr:((e : T) :: s)
      end
    | true => s
  end.

Ltac add_end_uniq e s :=
  match contains e s with
    | false => 
      let z := eval simpl app in (s ++ (e :: nil)) in
      z
    | false => 
      match type of s with
        | list ?T => constr:(s ++ ((e : T) :: @nil T))
      end
    | true => s
  end.

Ltac prepend_uniq es s :=
  match es with 
    | nil => s 
    | ?a :: ?b =>
      let k := prepend_uniq b s in
      cons_uniq a k
    | ?a ++ ?b =>
      let k := prepend_uniq b s in
      prepend_uniq a k
  end.

Ltac append_uniq es s :=
  let rec recur es ext :=
    match es with
      | nil => ext
      | ?a :: ?b =>
        match contains a s with
          | true => recur b ext
          | false => 
            let ext' := cons_uniq a ext in
            recur b ext'
        end
      | ?a ++ ?b =>
        let k := recur a ext in
        let z := recur b k in
        z
    end
  in
  let n := 
    match type of es with
      | list ?T => constr:(@nil T)
      | ?X => idtac "append_uniq first argument must be a list! Got type: " X 
    end
  in
  let ext := recur es n in
  eval simpl app in (s ++ ext).

Ltac indexOf keyF x ls :=
  match ls with
    | ?F :: ?ls' =>
      let F' := eval simpl in (keyF F) in
      match F' with
        | x => constr:(@FO _ F ls')
        | _ => let f := indexOf keyF x ls' in constr:(@FS _ F ls' f)
      end
  end.

Goal forall a b c : Type, nil ++ (a :: nil) ++ nil ++ nil = nil.
  intros.
  match goal with
    | [ |- ?L = ?R ] =>
      let res := append_uniq R L in
      idtac res ;
      let nop := constr:(fun x : Type => x) in
      let i := indexOf nop a res in
      idtac i

  end.
Abort.