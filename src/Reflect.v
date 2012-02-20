(** Reusable Ltac procedures:
 ** - reflecting function applications
 ** - list lookup
 ** - 
 **)
Require Import List DepList.

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
  match e with
    | (fun _ => _) => 
      let rec getTypes As :=
        match As with
          | tt => constr:(@nil Type)
          | (?A, ?B) =>
            match type of A with 
              | _ -> ?TT =>
                let r := getTypes B in
                constr:((TT : Type) :: r)
            end
        end
      in
      let rec papply cc F T Tb Ts As :=
        match T with 
          | ?T1 -> ?TT =>
            match Ts with
              | ?T :: ?T' =>
                match As with
                  | (?A, ?A') =>
                    let cc' f Ts As :=
                      let Ts' := constr:((T : Type) :: Ts) in
                      let As' := constr:((A, As)) in
                      cc f Ts' As'
                    in
                    let Tb := constr:((T:Type) :: Tb) in
                    papply cc' F TT Tb T' A'
                end
            end
          | forall x : ?T1, @?T2 x =>
            match Ts with
              | _ :: ?T' =>
                match As with
                  | ((fun _ => ?A), ?A') =>
                    let TT' := eval simpl in (T2 A) in
                    let f' := eval simpl in (@apply_ls Tb T1 T2 A F) in
                    papply cc f' TT' Tb T' A'
                end
            end
          | _ =>
            cc F Ts As             
        end
      in
      match e with
        | fun x => ?F (@?A x) (@?B x) (@?C x) (@?D x) (@?E x) =>
          let As := constr:((A,(B,(C,(D,(E,tt)))))) in
          let Ts := getTypes As in
          let Tf := type of F in
          let Tb := constr:(@nil Type) in
          papply cc F Tf Tb Ts As
        | fun x => ?F (@?A x) (@?B x) (@?C x) (@?D x) =>
          let As := constr:((A,(B,(C,(D,tt))))) in
          let Ts := getTypes As in
          let Tf := type of F in
          let Tb := constr:(@nil Type) in
          papply cc F Tf Tb Ts As
        | fun x => ?F (@?A x) (@?B x) (@?C x) =>
          let As := constr:((A,(B,(C,tt)))) in
          let Ts := getTypes As in
          let Tf := type of F in
          let Tb := constr:(@nil Type) in
          papply cc F Tf Tb Ts As
        | fun x => ?F (@?A x) (@?B x) =>
          let As := constr:((A,(B,tt))) in
          let Ts := getTypes As in
          let Tf := type of F in
          let Tb := constr:(@nil Type) in
          papply cc F Tf Tb Ts As
        | fun x => ?F (@?A x) =>
          let As := constr:((A,tt)) in
          let Ts := getTypes As in
          let Tf := type of F in
          let Tb := constr:(@nil Type) in
          papply cc F Tf Tb Ts As
        | fun x => ?F =>
          let As := constr:(tt) in
          let Ts := getTypes As in
          let Tf := type of F in
          let Tb := constr:(@nil Type) in
          papply cc F Tf Tb Ts As
      end
    | _ => 
      let rec refl cc e As :=
        match e with
          | ?A ?B =>
            let Ta := type of A in
            match Ta with
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
        refl cc e b
  end.

(** Test whether two terms are unifiable *)
Ltac unifies a b :=
  match a with
    | b => true
    | _ =>
      let a := eval cbv in a in
      let b := eval cbv in b in
      match a with
        | b => true
        | _ => false
      end
  end.

Ltac guard_unifies a b :=
  unify a b.

(** Unification test **)
Definition foo := nat.

Goal True.
  guard_unifies foo nat.
  (guard_unifies unit nat || trivial).
Qed.

(** Set operations **)
Ltac contains e s :=
  match s with
    | nil => false
    | ?e' :: ?b => 
      match unifies e e' with
        | true => true
        | false => contains e b 
      end
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
      let F' := eval simpl keyF in (keyF F) in
      match unifies F' x with
        | true => constr:(@FO _ F ls')
        | false => let f := indexOf keyF x ls' in constr:(@FS _ F ls' f)
      end
  end.

Ltac map_tac T tac fs :=
  let rec map_tac fs :=
    match fs with
      | nil => constr:(@nil T)
      | ?f :: ?fs =>
        let f := tac f in
        let fs := map_tac fs in
        constr:(f :: fs)
      | ?fs ++ ?fs' =>
        let fs := map_tac fs in
        let fs' := map_tac fs' in
        constr:(fs ++ fs')
      | _ => 
        let fs' := eval unfold fs in fs in 
        match fs with
          | fs' => fs
          | _ => map_tac fs'
        end
    end
  in
  map_tac fs.

Goal (unit :: nil) ++ (foo :: nil) ++ (bool :: nil) ++ nil = unit :: foo :: bool :: nil.
  intros.
  match goal with
    | [ |- ?L = ?R ] =>
      let res := append_uniq R L in
      idtac res ;
      let nop := constr:(fun x : Type => x) in
      let i := indexOf nop nat res in
      idtac i
  end.
  reflexivity.
Abort.