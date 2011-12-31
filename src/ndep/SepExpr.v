Require Import List.
Require Import Bedrock.ndep.Expr.
Require Import Heaps SepTheoryX PropX.
Require Import PropXTac.
Require Import PMap.
Require Import RelationClasses EqdepClass.
Require Import Bedrock.ndep.ExprUnify.

Set Implicit Arguments.

Require Bedrock.ndep.NatMap.

Module FM := Bedrock.ndep.NatMap.IntMap.    

Module SepExpr (B : Heap) (ST : SepTheoryX.SepTheoryXType B).

  Section env.
    Variable types : list type.
    Variable funcs : functions types.

    Variable pcType : tvar.
    Variable stateType : tvar.
    Variable stateMem : tvarD types stateType -> B.mem.

    Record ssignature := {
      SDomain : list tvar ;
      SDenotation : functionTypeD (map (@tvarD types) SDomain) 
        (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.
    Variable sfuncs : list ssignature.

    Inductive sexpr : Type :=
    | Emp : sexpr
    | Inj : expr types -> sexpr
    | Star : sexpr -> sexpr -> sexpr
    | Exists : tvar -> sexpr -> sexpr
    | Func : func -> list (expr types) -> sexpr
    | Const : ST.hprop (tvarD types pcType) (tvarD types stateType) nil
      -> sexpr
    .

    Fixpoint sexprD (s : sexpr) (uvs vs : list { t : tvar & tvarD types t })
      : option (ST.hprop (tvarD types pcType) (tvarD types stateType) nil) :=
    match s with 
      | Emp => 
        Some (ST.emp _ _)
      | Inj p =>
        match exprD funcs uvs vs p tvProp with
          | None => None
          | Some p => 
            Some (ST.inj (PropX.Inj p))
        end
      | Star l r =>
        match sexprD l uvs vs , sexprD r uvs vs with
          | Some l , Some r =>
            Some (ST.star l r)
          | _ , _ => None
        end                    
      | Exists t b =>
        Some (ST.ex (fun x : tvarD types t =>
          match sexprD b uvs (@existT _ _ t x :: vs) with
            | None => ST.inj (PropX.Inj False)
            | Some s => s
          end))
      | Func f b =>
        match nth_error sfuncs f with
          | None => None
          | Some f =>
            applyD (@exprD types funcs uvs vs) (SDomain f) b _ (SDenotation f)
        end
      | Const p => Some p
    end.

    Section SProver.
      Definition himp (U1 U2 G : env types)
        (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
        (gl gr : sexpr) : Prop :=
        match sexprD gl U1 G , sexprD gr U2 G with
          | Some l , Some r => ST.himp cs l r
          | _ , _ => False
        end.

      Definition heq (U1 U2 G : env types)
        (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
        (gl gr : sexpr) : Prop :=
        match sexprD gl U1 G , sexprD gr U2 G with
          | Some l , Some r => ST.heq cs l r
          | _ , _ => False
        end.

      Global Instance Trans_himp U g cs : Transitive (@himp U U g cs).
      Proof.
        red. unfold himp. intros x y z. 
        destruct (sexprD x U g);
        destruct (sexprD y U g);
        destruct (sexprD z U g); try intuition.
        etransitivity; eauto.
      Qed.

      Global Instance Trans_heq U g cs : Transitive (@heq U U g cs).
      Proof.
        red. unfold heq. intros x y z. 
        destruct (sexprD x U g);
        destruct (sexprD y U g);
        destruct (sexprD z U g); try intuition.
        etransitivity; eauto.
      Qed.

      Theorem ST_himp_himp : forall (U1 U2 G : env types) cs L R,
        himp U1 U2 G cs L R ->
        match sexprD L U1 G , sexprD R U2 G with
          | Some l , Some r => ST.himp cs l r
          | _ , _ => False
        end.
      Proof.
        clear. auto.
      Qed.

      Theorem ST_heq_heq : forall (U1 U2 G : env types) cs L R,
        heq U1 U2 G cs L R ->
        match sexprD L U1 G , sexprD R U2 G with
          | Some l , Some r => ST.heq cs l r
          | _ , _ => False
        end.
      Proof.
        clear. auto.
      Qed.
(*
      Section exists_subst.
        Variable U1 : env types.
        
        Fixpoint exists_subst (u : variables types)
          (U : hlist (fun t => option (expr funcs nil u1 t)) u) :
          (hlist (@tvarD _) u -> Prop) -> Prop :=
          match U in hlist _ u
            return (hlist (@tvarD _) u -> Prop) -> Prop
            with
            | HNil => fun cc => cc HNil
            | HCons _ _ v r => fun cc =>
              match v with
                | None => exists v, exists_subst r (fun z => cc (HCons v z))
                | Some v =>
                  let v := exprD HNil U1 v in
                    exists_subst r (fun z => cc (HCons v z))
              end
          end.

      End exists_subst.

      Lemma exists_subst_exists : forall a (A : hlist _ a) 
        b (B : hlist (fun t => option (expr funcs nil a t)) b) P,
        exists_subst A B P ->
        exists C, P C.
      Proof.
        clear. induction B; simpl; intros.
          eauto.
          destruct b. eapply IHB in H. destruct H; eauto.
          destruct H. eapply IHB in H. destruct H; eauto.
      Qed.


      Fixpoint forallEach (ls : variables types) : (hlist (@tvarD types) ls -> Prop) -> Prop :=
        match ls with
          | nil => fun cc => cc HNil
          | a :: b => fun cc =>
            forall x : tvarD a, forallEach (fun r => cc (HCons x r))
        end.

      Lemma forallEach_forall : forall ls (P : hlist (@tvarD types) ls -> Prop),
        forallEach P -> forall V, P V.
      Proof.
        induction ls; simpl; intros. 
        rewrite (hlist_nil_only _ V). auto.
        rewrite (hlist_eta _ V). 
        specialize (H (hlist_hd V)). eapply IHls in H. eassumption.
      Qed.
*)

      Record SepResult (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
        (gl gr : sexpr) : Type :=
      { lhs : sexpr
      ; rhs : sexpr
      ; SUBST : Subst types
      }.

      Definition SProverT : Type := forall
        (cs : codeSpec (tvarD types pcType) (tvarD types stateType)) 
        (hyps : list (expr types)) (** Pure Premises **)
        (gl gr : sexpr),
        SepResult cs gl gr.
    
    End SProver.


    Record SHeap : Type :=
    { impures : FM.t (list (list (expr types)))
    ; pures   : list (expr types)
    ; other   : list (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.
  
    Definition SHeap_empty : SHeap := 
      {| impures := FM.empty _
       ; pures   := nil
       ; other   := nil
       |}.

    Fixpoint liftSExpr (a b : nat) (s : sexpr) : sexpr :=
      match s with
        | Emp => Emp
        | Inj p => Inj (liftExpr a b p)
        | Star l r => Star (liftSExpr a b l) (liftSExpr a b r)
        | Exists t s => 
          Exists t (liftSExpr (S a) b s)
        | Func f xs => Func f (map (liftExpr a b) xs)
        | Const c => Const c
      end.

    (** lift all the "real" variables in [a,...) 
     ** to the range [a+b,...)
     **)
    Definition liftSHeap (a b : nat) (s : SHeap) : SHeap :=
      {| impures := FM.map (map (map (liftExpr a b))) (impures s)
       ; pures   := map (liftExpr a b) (pures s)
       ; other   := other s
       |}.

    Fixpoint multimap_join T (l r : FM.t (list T)) : FM.t (list T) :=
      FM.fold (fun k v a =>
        match FM.find k a with
          | None => FM.add k v a
          | Some v' => FM.add k (v ++ v') a
        end) l r.

    Fixpoint star_SHeap (l r : SHeap) : SHeap :=
      {| impures := multimap_join (impures l) (impures r)
       ; pures := pures l ++ pures r
       ; other := other l ++ other r
       |}.

    Fixpoint hash (s : sexpr) : ( variables * SHeap ) :=
      match s with
        | Emp => (nil, SHeap_empty)
        | Inj p => (nil,
          {| impures := FM.empty _
            ; pures := p :: nil
            ; other := nil
          |})
        | Star l r =>
          let (vl, hl) := hash l in
          let (vr, hr) := hash r in
          (vl ++ vr,
           star_SHeap hl (liftSHeap 0 (length vl) hr))
        | Exists t b =>
          let (v,b) := hash b in
          (v ++ t :: nil, b)
        | Func f a =>
          (nil,
           {| impures := FM.add f (a :: nil) (FM.empty _)
            ; pures := nil
            ; other := nil
           |})
        | Const c => 
          (nil,
           {| impures := FM.empty _
            ; pures := nil
            ; other := c :: nil
            |})
      end.
 
    Definition starred (T : Type) (F : T -> sexpr) (ls : list T) (base : sexpr)
      : sexpr :=
      fold_right (fun x a => Star (F x) a) base ls.

    Definition sheapD (h : SHeap) : sexpr :=
      let a := FM.fold (fun k => starred (Func k)) (impures h) Emp in
      let a := starred (fun x => Inj x) (pures h) a in
      let a := starred (fun x => Const x) (other h) a in
      a.

    Definition sheapD' (h : SHeap) :  sexpr :=
      let a := FM.fold (fun k ls acc => 
        Star (starred (Func k) ls Emp) acc) (impures h) Emp in
      let c := starred (fun x => Inj x) (pures h) Emp in
      let e := starred (fun x => Const x) (other h) Emp in
      Star a (Star c e).

    Fixpoint existsEach (ls : list tvar) {struct ls} : sexpr -> sexpr :=
      match ls with
        | nil => fun x => x
        | t :: ts => fun y => @existsEach ts (Exists t y)
      end.

    Theorem hash_denote : forall cs G (s : sexpr), 
      heq nil nil G cs s 
        (@existsEach (fst (hash s)) (sheapD (snd (hash s)))).
    Proof.
      induction s; simpl.
        unfold sheapD; simpl. unfold FM.fold. simpl. admit.
        unfold sheapD; simpl. unfold FM.fold. simpl. admit.
    Admitted.

    (** replace "real" variables [a,b) and replace them with
     ** uvars [c,..]
     **)
    Definition sheapSubstU (a b c : nat) (s : SHeap) : SHeap :=
      {| impures := FM.map (map (map (exprSubstU a b c))) (impures s)
       ; pures := map (exprSubstU a b c) (pures s)
       ; other := other s
       |}.

    Section MM.
      Require Import Env.
      Variable T : Type.
      Variable T_sdec : SemiDec T.

      Fixpoint in_sdec (v : T) (m : list T) : option (In v m) :=
        match m with
          | nil => None
          | a :: b =>
            match seq_dec a v with
              | Some pf => 
                Some (or_introl _ pf)
              | None => match in_sdec v b with
                          | None => None
                          | Some pf => Some (or_intror _ pf)
                        end
            end
        end.

      Definition filter_all (m r : list T) : list T :=
        filter (fun v => if in_sdec v r then true else false) m.
        

      Definition mm_remove_all (m r : FM.t (list T)) : FM.t (list T) :=
        FM.fold (fun k v a =>
          match FM.find k r with
            | None => FM.add k v a
            | Some v' => FM.add k (filter_all v v') a
          end) m (FM.empty _).

    End MM.
    
    Definition sepCancel (l r : SHeap) :
      SHeap * SHeap * ExprUnify.Subst types * ExprUnify.Subst types.
(*
      let '(lf,rf,s) := dmap_fold (fun acc k v =>
        let '(lf,rf,s) := acc in
        match dmap_remove scmp_dec k rf with 
          | None => (dmap_replace scmp_dec _ v lf, rf, s)
          | Some (oths, rmed) => 
            let '(lf',rf',s') := sepCancel_refl_funcs oths v s in
            (dmap_replace scmp_dec _ lf' lf, 
             dmap_replace scmp_dec _ rf' rmed,
             s')
        end) (dmap_empty, impures r, empty_Subst _ _ _ _) (impures l)
      in
      ({| impures := lf ; pures := pures l ; other := other l |},
       {| impures := rf ; pures := pures r ; other := other r |},
       s).
*)
    Admitted.

    Definition CancelSep : SProverT :=
      fun cs _ gl gr =>
        let (ql, lhs) := hash gl in
        let (qr, rhs) := hash gr in
        let rhs' := liftSHeap 0 (length ql) (sheapSubstU 0 (length qr) 0 rhs) in
        let '(lhs',rhs',lhs_subst,rhs_subst) := sepCancel lhs rhs' in
        {| lhs := sheapD lhs' ; rhs := sheapD rhs' ; SUBST := rhs_subst |}.

  End env.

  Implicit Arguments Func [ types pcType stateType ].
  Implicit Arguments Exists [ types pcType stateType ].
  Implicit Arguments Star [ types pcType stateType ].

  (** Reflection **)
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

  Definition defaultType (T : Type) : type :=
    {| Impl := T; Eq := fun _ _ => None |}.

  Ltac extend_all_types Ts types :=
    match Ts with
      | nil => types
      | ?a :: ?b => 
        let types := extend_type a (defaultType a) types in
        extend_all_types b types
    end.  

  Record VarType (t : Type) : Type :=
    { open : t }.
  Definition openUp T U (f : T -> U) (vt : VarType T) : U :=
    f (open vt).

  Ltac collectTypes_expr e types :=
    match e with
      | fun x => (@openUp _ ?T _ x) =>
        let v := constr:(T:Type) in
        cons_uniq v types
      | fun x => ?e =>
        collectTypes_expr e types
      | _ =>
        let rec bt_args args types :=
          match args with
            | tt => types
            | (?a, ?b) =>
              let types := collectTypes_expr a types in
              bt_args b types
          end
        in
        let cc _ Ts args := 
          let T := 
            match e with 
              | fun x : VarType _ => _ => 
                match type of e with
                  | _ -> ?T => T
                end
              | _ => type of e
            end
          in
          let Ts :=
            let v := constr:(T : Type) in
            cons_uniq v Ts 
          in
          let types := append_uniq Ts types in
          bt_args args types
        in
        refl_app cc e
    end.

  Ltac map_non_dep ty args f acc :=
    match args with
      | tt => acc
      | (?A1, ?A2) =>
        match ty with
          | ?T1 -> ?T2 =>
            let acc := f T1 A1 acc in
            map_non_dep T2 A2 f acc
          | forall x : ?T1, @?T2 x =>
            match A1 with
              | fun _ => ?A => 
                let t := eval simpl in (T2 A) in
                map_non_dep t A2 f acc
            end
          | _ => acc
        end
    end.

  Ltac collectTypes_sexpr s types k :=
    match s with
      | fun x : VarType ?T => @ST.star _ _ _ (@?L x) (@?R x) =>
        collectTypes_sexpr L types ltac:(fun types =>
          collectTypes_sexpr R types k)
      | fun x : ?T => @ST.ex _ _ _ ?T' (fun y : ?T' => @?B x y) =>
        let v := constr:(fun x : VarType (T * T') => 
          B (@openUp _ T (@fst _ _) x) (@openUp _ T' (@snd _ _) x)) in
        let v := eval simpl in v in
        collectTypes_sexpr v types k
      | @ST.emp _ _ _ => k types
      | @ST.inj _ _ _ (PropX.Inj _ _ _ ?P) =>
        k ltac:(collectTypes_expr P types)
      | @ST.inj _ _ _ ?PX => k types
      | @ST.star _ _ _ ?L ?R =>
        collectTypes_sexpr L types
          ltac:(fun Ltypes => collectTypes_sexpr R Ltypes k)
      | @ST.ex _ _ _ ?T (fun x : ?T => @?B x) =>
        let v := constr:(fun x : VarType T => B (@openUp _ T (fun x => x) x)) in
        let v := eval simpl in v in 
        collectTypes_sexpr v types k
      | ?X =>
        let rec bt_args args types :=
          match args with
            | tt => k types
            | (?a,?b) => 
              let k := collectTypes_expr a types in
              bt_args b k
          end
        in
        let cc _ Ts args := 
          let types := append_uniq Ts types in
          bt_args args types
        in
        refl_app cc X
    end.

  Ltac indexOf_nat proj x xs :=
    let rec search xs :=
      match xs with
        | ?X :: ?XS =>
          let X' := eval simpl in (proj X) in
          match X' with
            | x => constr:(0)
            | _ => 
              let r := search XS in
              constr:(S r)
          end
      end
    in search xs.

  Ltac typesIndex x types :=
    indexOf_nat Impl x types.

  Ltac reflectType types t :=
    match t with
      | Prop => constr:(tvProp)
      | _ =>
        let i := typesIndex t types in
        let r := constr:(tvType i) in
        r
    end.  
        
  Ltac reflectTypes_toList types ts :=
    match ts with 
      | nil => constr:(@nil tvar)
      | ?T :: ?TS =>
        let i := typesIndex T types in
        let rest := reflectTypes_toList types TS in
        constr:(@cons tvar (tvType i) rest)
    end.

  Ltac collectAllTypes isConst ts goals :=
    match goals with
      | nil => ts
      | ?a :: ?b =>
        (** TODO : I may need to reflect the pcType and stateType **)
        let ts := collectTypes_sexpr a ts ltac:(fun ts => ts) in
        collectAllTypes isConst ts b
    end.

  Ltac getVar idx vars :=
    match vars with
      | nil => idtac "empty variable list!" idx
      | ?a :: ?b =>
        match idx with
          | fun x => @openUp _ _ (@fst _ _) _ =>
            constr:(0)
          | fun x => @openUp _ _ (@snd _ _) (@?X x) =>
            let r := getVar X vars in
            constr:(S r)
          | _ => idtac "couldn't find variable!" idx vars
        end
    end.

  Ltac reflect_function types f :=
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
          constr:(@Build_signature types dom R f)
      end
   in refl (@nil tvar) T.


  Ltac getFunction types f funcs k :=
    let rec lookup funcs acc :=
      match funcs with
        | nil =>
          let F := reflect_function types f in
          let funcs := eval simpl app in (funcs ++ (F :: nil)) in
          k funcs acc
        | ?F :: ?FS =>
          let F' := eval simpl Denotation in (Denotation F) in
          match F' with
            | f => k funcs acc
            | _ => 
              let acc := constr:(S acc) in
              lookup FS acc
          end
      end
    in lookup funcs 0.

  (** reflect an expression gathering the functions at the same time.
   ** - k funcs expr
   **)
  Ltac reflect_expr isConst e types funcs uvars vars k :=
    let rec reflect funcs e k :=
      match e with
        | fun _ => ?X =>
          is_evar X ; 
          (** this is a unification variable **)
          let r := constr:(@Expr.UVar) in (** TODO **)
          k funcs r 
        | fun x => (@openUp _ _ _ _) =>
          (** this is a variable **)
          let v := getVar e vars in
          let r := constr:(@Expr.Var types funcs uvars vars v) in
          k funcs r
        | fun x => ?e =>
          reflect funcs e k
        | _ =>
          let rec bt_args funcs args k :=
            match args with
              | tt => 
                let v := constr:(@nil (@expr types)) in
                k funcs v
              | (?a, ?b) =>
                reflect funcs a ltac:(fun funcs a =>
                  bt_args funcs b ltac:(fun funcs b =>
                    let r := constr:(@cons (@expr types) a b) in
                    k funcs r))
            end
          in
          let cc f Ts args :=
            getFunction types f funcs ltac:(fun funcs F =>
              bt_args funcs args ltac:(fun funcs args =>
                let r := constr:(@Expr.Func types F args) in 
                k funcs r))
          in
          match e with
            | _ => 
              match isConst e with
                | true => 
                  let ty := type of e in
                  let ty := reflectType types ty in
                  let r := eval simpl in (@Expr.Const types ty e) in
                  k funcs r
                | false => 
                  refl_app cc e
              end
            | _ => refl_app cc e
          end
      end
    in reflect funcs e k.

  Ltac reflect_sfunction pcT stT types f :=
    let T := type of f in
    let rec refl dom T :=
      match T with
        (* no dependent types *)
        | ?A -> ?B =>
          let A := reflectType types A in
          let dom := constr:(A :: dom) in
          refl dom B 
        | _ =>
          let dom := eval simpl rev in (rev dom) in
          constr:(@Build_ssignature types pcT stT dom f)
      end
   in refl (@nil tvar) T.

  Ltac getSFunction pcT stT types f sfuncs k :=
    let rec lookup sfuncs' acc :=
      match sfuncs' with
        | nil =>
          let F := reflect_sfunction pcT stT types f in
          let sfuncs := eval simpl app in (sfuncs ++ (F :: nil)) in
          k sfuncs acc
        | ?F :: ?FS =>
          let F' := eval simpl SDenotation in (SDenotation F) in
          match F' with
            | f => 
              k sfuncs acc 
            | _ => 
              let acc := constr:(S acc) in
              lookup FS acc
          end
      end
    in lookup sfuncs 0.


  (** reflect sexprs. simultaneously gather the funcs and sfuncs
   ** k funcs sfuncs sexpr
   **)
  Ltac reflect_sexpr isConst s types funcs pcType stateType sfuncs uvars vars k :=
    let implicits ctor :=
      constr:(ctor types pcType stateType)
    in
    let rec reflect s funcs sfuncs uvars vars k :=
      match s with
        | fun _ => ?s =>
          reflect s funcs sfuncs uvars vars k
        | fun x : VarType ?T => @ST.star _ _ _ (@?L x) (@?R x) =>
          reflect L funcs sfuncs uvars vars ltac:(fun funcs sfuncs L =>
            reflect R funcs sfuncs uvars vars ltac:(fun funcs sfuncs R => 
              let r := constr:(@Star) in
              let r := implicits r in
              let r := constr:(r L R) in
              k funcs sfuncs r))
        | fun x : ?T => @ST.ex _ _ _ ?T' (fun y : ?T' => @?B y x) =>
          let v := constr:(fun x : VarType (T' * T) => 
            B (@openUp _ T (@fst _ _) x) (@openUp _ T' (@snd _ _) x)) in
          let v := eval simpl in v in
          let vars' := 
            let nv := reflectType types T' in
            constr:(nv :: vars)
          in
          reflect v funcs sfuncs uvars vars' ltac:(fun funcs sfuncs B =>
            let r := constr:(@Exists) in
            let r := implicits r in
            let r := constr:(@r _ B) in
            k funcs sfuncs r)
        | @ST.emp _ _ _ => 
          let r := constr:(@Emp) in
          let r := implicits r in
          k funcs sfuncs r

        | @ST.inj _ _ _ (PropX.Inj _ _ _ ?P) =>
          reflect_expr isConst P types funcs uvars vars ltac:(fun funcs P =>
            let r := constr:(@Inj) in
            let r := implicits r in
            let r := constr:(r P) in
            k funcs sfuncs r)
        | @ST.inj _ _ _ ?PX =>
          let r := constr:(@Const) in
          let r := implicits r in
          let r := constr:(r PX) in
          k funcs sfuncs r
        | @ST.star _ _ _ ?L ?R =>
          reflect L funcs sfuncs uvars vars ltac:(fun funcs sfuncs L => 
            reflect R funcs sfuncs uvars vars ltac:(fun funcs sfuncs R => 
              let r := constr:(@Star) in
              let r := implicits r in
              let r := constr:(r L R) in
              k funcs sfuncs r))
        | @ST.ex _ _ _ ?T (fun x : ?T => @?B x) =>
          let v := constr:(fun x : VarType (T * unit) => B (@openUp _ T (@fst _ _) x)) in
          let v := eval simpl in v in
          let vars' := 
            let nv := reflectType types T in
            constr:(nv :: vars)
          in
          reflect v funcs sfuncs uvars vars' ltac:(fun funcs sfuncs B =>
            let r := constr:(@Exists) in
            let r := implicits r in
            let r := constr:(@r _ B) in
            k funcs sfuncs r)
        | ?X =>
          let rec bt_args args funcs k :=
            match args with
              | tt => 
                let v := constr:(@nil (@expr types)) in
                k funcs v
              | (?a,?b) =>
                reflect_expr isConst a types funcs uvars vars ltac:(fun funcs a =>
                  bt_args b funcs ltac:(fun funcs b => 
                  let v := constr:(@cons (@expr types) a b) in
                  k funcs v))
            end
          in
          let cc f Ts As :=
            getSFunction pcType stateType types f sfuncs ltac:(fun sfuncs F =>
            bt_args As funcs ltac:(fun funcs args =>
            let r := constr:(@Func) in
            let r := implicits r in
            let r := constr:(@r F args) in
            k funcs sfuncs r))
          in
          refl_app cc X
      end
    in
    reflect s funcs sfuncs uvars vars k.

  Ltac reflect_all pcT stT isConst Ts goals := 
    let rt := 
      collectAllTypes isConst ((pcT : Type) :: (stT : Type) :: @nil Type) goals
    in
    let Ts := extend_all_types rt Ts in
    let Ts := eval simpl in Ts in
    let pcTyp := typesIndex pcT Ts in
    let stTyp := typesIndex stT Ts in
    let pcTyp := constr:(tvType pcTyp) in
    let stTyp := constr:(tvType stTyp) in
    let fs := constr:(@nil (@signature Ts)) in
    let sfs := constr:(@nil (@ssignature Ts pcTyp stTyp)) in
    let rec reflect_all ls funcs sfuncs k :=
      match ls with
        | nil => 
          let r := constr:(@nil (@sexpr Ts pcTyp stTyp)) in
          k funcs sfuncs r
        | ?e :: ?es =>
          let vs := constr:(@nil tvar) in
          let us := constr:(@nil tvar) in
          reflect_sexpr isConst e Ts funcs pcTyp stTyp sfuncs us vs ltac:(fun funcs sfuncs e =>
            reflect_all es funcs sfuncs ltac:(fun funcs sfuncs es =>
              let es := constr:(e :: es) in
              k funcs sfuncs es)) 
      end
    in
    reflect_all goals fs sfs ltac:(fun funcs sfuncs es =>
      constr:((Ts, pcTyp, stTyp, funcs, sfuncs, es))).
    
(*
    match collectAllFunctions build_ssig isConst goals Ts fs sfs with
      | (?funcs, ?sfuncs) =>
        let goals := reflectAll isConst goals Ts pcTyp stTyp funcs sfuncs in
        goals
    end.
*)

  Section Tests.
    Variable f : forall a b, nat -> ST.hprop a b nil.
    Variable h : forall a b, nat -> ST.hprop a b nil.
    Variable i : forall a b, nat -> ST.hprop a b nil.
    Variable g : bool -> nat -> nat -> nat.

    Variable a : Type.
    Variable b : Type.
    
    Definition hpropB : list Type -> Type := ST.hprop a b.

    Variable p : forall {sos}, nat -> nat -> hpropB sos.

    Ltac isConst e :=
      match e with
        | true => true
        | false => true
        | O => true
        | S ?e => isConst e
        | _ => false
      end.

    Definition nat_type : type :=
      {| Impl := nat 
       ; Eq := fun x y => match equiv_dec x y with
                            | left pf => Some pf
                            | _ => None 
                          end
       |}.

    Lemma change_ST_himp_himp : forall (types : list type)
      (funcs : functions types) (pc st : tvar)
      (sfuncs : list (ssignature types pc st))
      
      (cs : codeSpec (tvarD types pc) (tvarD types st))
      (L R : sexpr types pc st),
      himp funcs sfuncs nil nil nil cs L R ->
      match 
        @sexprD types funcs pc st sfuncs L nil nil , 
        @sexprD types funcs pc st sfuncs R nil nil
        with
        | Some l , Some r => 
          ST.himp cs l r
        | _ , _ => False
      end.
    Proof.
      unfold himp. intros. 
      destruct (sexprD funcs sfuncs L nil nil);
        destruct (sexprD funcs sfuncs R nil nil); auto.
    Qed.

    Implicit Arguments Expr.Const [ types t ].

    Opaque himp.

    Goal forall c x, @ST.himp a b c (p nil 1 x) (p _ 1 x).
      intros.
      match goal with
        | [ |- @ST.himp ?p ?s ?cs ?L ?R ] =>
          let r := reflect_all p s isConst (nat_type :: nil) (L :: R :: nil) in
          match r with
            | (?types, ?pcTyp, ?stTyp, ?fs, ?sfs, ?L :: ?R :: nil) =>
              apply (@change_ST_himp_himp types fs pcTyp stTyp sfs cs L R)
          end
      end.
    Abort.

(*
      Lemma ApplyCancelSep : forall cs l r res,
        res = CancelSep cs nil l r ->
(*          | Prove vars u2 l' r' SUBST _ => *)
            forallEach
            (fun VS : hlist (@tvarD types) vars =>
              exists_subst VS SUBST
              (fun k : hlist (@tvarD types) u2 => himp HNil k VS cs l' r'))
(* -> *)
        himp nil nil nil cs l r.
      Proof.
        clear. intros. destruct (CancelSep cs nil l r). auto.
      Qed.
*)      


    Fixpoint all a b (f : nat -> ST.hprop a b nil) (n : nat) : ST.hprop a b nil :=
      match n with
        | 0 => f 0
        | S n => ST.star (f (S n)) (all f n)
      end.

    Fixpoint allb a b (f : nat -> ST.hprop a b nil) (n m : nat) : ST.hprop a b nil :=
      match n with
        | 0 => f m
        | S n => ST.star (f (m - S n)) (allb f n m)
      end.


    Goal forall c, @ST.himp a b c 
      (ST.star (allb (@h a b) 15 15) (allb (@f a b) 15 15))
      (ST.star (all (@f a b) 15) (all (@h a b) 15)).
      simpl all. simpl allb.
      intros. 
      match goal with
        | [ |- @ST.himp ?p ?s ?cs ?L ?R ] =>
          let r := reflect_all p s isConst (nat_type :: nil) (L :: R :: nil) in
          match r with
            | (?types, ?pcTyp, ?stTyp, ?fs, ?sfs, ?L :: ?R :: nil) =>
              apply (@change_ST_himp_himp types fs pcTyp stTyp sfs cs L R)
          end
      end.
    Abort.
End Tests.


End SepExpr.