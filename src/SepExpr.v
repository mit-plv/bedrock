Require Import List.
Require Import Expr.
Require Import Heaps PropX.
Require Import PMap.

Set Implicit Arguments.

Require Import PropXTac.

Ltac goPropX := 
  repeat match goal with
           | [ H : valid _ _ _ |- _ ] => apply simplify_fwd in H; simpl in H
           | [ |- valid _ _ _ ] => apply simplify_bwd; simpl
           | [ H : exists x , _ |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
         end.

Module SepExpr (B : Heap).
  Module HT := HeapTheory B.  

  Section env.

    Variable types : list type.
    Variable funcs : functions types.

    Variable pcType : tvar types.    
    Variable stateType : tvar types.
    Variable stateMem : tvarD stateType -> B.mem.

    Record ssignature := {
      SDomain : list (tvar types) ;
      SDenotation : functionTypeD (map (@tvarD types) SDomain) (HT.smem -> PropX (tvarD pcType) (tvarD stateType))
    }.
    Variable sfuncs : list ssignature.

    Variable consts : list (PropX (tvarD pcType) (tvarD stateType)).

    Inductive sexpr : variables types -> Type :=
    | Emp : forall vars, sexpr vars
    | Inj : forall vars, expr funcs vars None -> sexpr vars
    | Star : forall vars, sexpr vars -> sexpr vars -> sexpr vars
    | Exists : forall vars t, sexpr (t :: vars) -> sexpr vars
    | Cptr : forall vars, expr funcs vars pcType -> sexpr (stateType :: vars) -> sexpr vars
    | Func : forall vars (f : fin sfuncs), 
      hlist (expr funcs vars) (SDomain (get sfuncs f)) -> sexpr vars
    | Const : forall vars, fin consts -> sexpr vars
    (** If PtsTo is derived: we can handle different sizes easily, 
     ** If PtsTo is built-in: we can derive <> facts easily (also precision)
     **)
    .
    (** NOTE: If I want to be able to reflect arbitrary propX terms (ExistsX,ForallX), then I'm going to need
     ** another index on sexpr to express the (type -> PropX)
     **)


    Fixpoint sexprD (vars : variables types) (s : sexpr vars)
      : hlist (@tvarD types)  vars -> HT.smem -> PropX (tvarD pcType) (tvarD stateType) :=
      match s in sexpr vars return hlist (@tvarD types) vars -> HT.smem -> PropX (tvarD pcType) (tvarD stateType) with
        | Inj _ p => fun g _ => PropX.Inj (exprD g p)
        | Exists _ t b => fun g m => PropX.Exists (fun x : tvarD t => @sexprD _ b (HCons x g) m)
        | Func _ f b => fun g =>
          applyD (exprD g) b _ (SDenotation (get sfuncs f))
        | Const _ p => fun _ _ =>
          get consts p
        | Star _ l r => fun g m => 
          PropX.Exists (fun ml : HT.smem => PropX.Exists (fun mr : HT.smem => 
            PropX.And (PropX.Inj (HT.split m ml mr)) (And (sexprD l g ml) (sexprD r g mr))))
        | Emp _ => fun _ m => 
          PropX.Inj (HT.semp m)
        | Cptr _ p t => fun g m =>
          PropX.Cptr (exprD g p) 
          (fun x : tvarD stateType => PropX.Exists (fun m => 
            PropX.And (PropX.Inj (HT.satisfies m (stateMem x))) (sexprD t (HCons x g) m)))
      end.

    Section Cmp.
      Definition sexprCmp vars (a : sexpr vars) : forall b, dcomp a b.
        refine ((fix sexprCmp vars (a : sexpr vars) {struct a} : forall b, dcomp a b :=
          match a in sexpr vars return forall b : sexpr vars, dcomp a b with
            | Emp _ => fun b =>
              match b with
                | Emp _ => Env.Eq _
                | _ => Env.Lt _ _
              end
            | Inj v l => fun b =>
              match b in sexpr v' return forall l : expr funcs v' None, dcomp (Inj l) b with
                | Inj _ r => fun l => match exprEq l r with
                                        | Some _ => Env.Eq _
                                        | None => Env.Lt _ _ (** TODO: This is wrong! **)
                                      end
                | Emp _ => fun _ => Gt _ _
                | _ => fun _ => Lt _ _ 
              end l
            | Star v ll lr => fun b =>
              match b in sexpr v' 
                return forall (Heq : v' = v), (forall (x y : sexpr v'), dcomp (Star ll lr) (match Heq in _ = t 
                                                                                              return sexpr t
                                                                                              with
                                                                                              | refl_equal => Star x y
                                                                                            end))
                -> dcomp (Star ll lr) (match Heq in _ = t return sexpr t with
                                         | refl_equal => b
                                       end)
                with
                | Star _ rl rr => fun _ cc => cc rl rr
                | Emp _ | Inj _ _ => fun _ _ => Env.Gt _ _ 
                | _ => fun _ _ => Env.Lt _ _ 
              end (refl_equal _)
              (fun (x y : sexpr v) =>
                match sexprCmp _ ll x with
                  | Env.Lt => Env.Lt _ _
                  | Env.Gt => Env.Gt _ _
                  | Env.Eq _ => 
                    match sexprCmp _ lr y with
                      | Env.Lt => Env.Lt _ _
                      | Env.Gt => Env.Gt _ _
                      | Env.Eq _ => Env.Eq _
                    end
                end)
            | Exists v t body => fun b =>
              match b in sexpr v' 
                return forall (Heq : v' = v),
                  (forall t' (x : sexpr (t' :: v')), t' = t -> dcomp (Exists body) (match Heq in _ = t 
                                                                                      return sexpr t 
                                                                                      with
                                                                                      | refl_equal => Exists x
                                                                                    end)) ->
                  dcomp (Exists body) (match Heq in _ = t return sexpr t with
                                         | refl_equal => b
                                       end)
                with
                | Exists v' t' b' => fun Heq cc =>
                  match tvar_dec t' t with
                    | left pf => cc _ _ _
                    | right _ => Env.Lt _ _ (** TODO: wrong **)
                  end
                | Emp _ | Inj _ _ | Star _ _ _ => fun _ _ => Env.Gt _ _
                | _ => fun _ _ => Env.Lt _ _ 
              end (refl_equal _)
              (fun t x eqq => 
                match sexprCmp _ body match eqq in _ = t' return sexpr (t' :: v) with
                                        | refl_equal => x
                                      end
                  with
                  | Env.Lt => Env.Lt _ _
                  | Env.Gt => Env.Gt _ _
                  | Env.Eq _ => Env.Eq _
                end)
            | Cptr v lp ls => fun b =>
              match b in sexpr v' 
                return forall (Heq : v' = v), 
                  (forall (p : expr funcs v' pcType) (s : sexpr (stateType :: v')), dcomp (Cptr lp ls) (match Heq in _ = t
                                                                                                          return sexpr t
                                                                                                          with 
                                                                                                          | refl_equal => Cptr p s
                                                                                                        end)) ->
                  dcomp (Cptr lp ls) (match Heq in _ = t return sexpr t with
                                        | refl_equal => b
                                      end)
                with
                | Cptr _ rp rs => fun _ cc => cc rp rs
                | Emp _ | Inj _ _ | Star _ _ _ | Exists _ _ _ => fun _ _ => Env.Gt _ _
                | _ => fun _ _ => Env.Lt _ _
              end (refl_equal _)
              (fun x y =>
                match exprEq lp x with
                  | Some _ => match sexprCmp _ ls y with
                                | Env.Eq _ => Env.Eq _
                                | Env.Gt => Env.Gt _ _
                                | Env.Lt => Env.Lt _ _
                              end
                    
                  | _ => Env.Lt _ _ (** TODO: Wrong **)
                end)
            | Func v f args => fun b =>
              match b in sexpr v'
                return forall (Heq : v' = v), 
                  (forall args', option (args = args')) ->
                  dcomp (Func f args) (match Heq in _ = t 
                                          return sexpr t
                                          with
                                          | refl_equal => b
                                        end)
                with
                | Func v' f' args' => fun Heq cc => 
                  match finCmp f f' with
                    | Env.Eq pf => match cc match Heq in _ = t 
                                            return hlist (expr funcs t) (SDomain (get sfuncs f))
                                            with 
                                            | refl_equal => match sym_eq pf in _ = t 
                                                              return hlist (expr funcs v') (SDomain (get sfuncs t)) with
                                                              | refl_equal => args'
                                                            end
                                          end
                                   with
                                   | Some _ => Env.Eq  _
                                   | None => Env.Lt _ _ (** TODO : Wrong **)
                                 end                                     
                    | Env.Lt => Env.Lt _ _ 
                    | Env.Gt => Env.Gt _ _
                  end
                | Emp _ | Inj _ _ | Star _ _ _ | Exists _ _ _ | Cptr _ _ _ => fun _ _ => Env.Gt _ _
                | _ => fun _ _ => Env.Lt _ _
              end (refl_equal _) (hlistEq (@exprEq _ _ _) args)
            | Const _ x => fun b => 
              match b with
                | Const _ y => match finCmp x y with
                                 | Env.Eq _ => Env.Eq _ 
                                 | Env.Lt => Env.Lt _ _
                                 | Env.Gt => Env.Gt _ _
                               end
                | _ => Env.Gt _ _ 
              end
          end) vars a);
        clear sexprCmp; try abstract (subst; reflexivity).
      Defined.
    End Cmp.

    Section Himp.
      (** TODO: Ideally we would move this to another file 
       ** and treat it opaquely. That way this file focuses predominantly
       ** in a reflection of that syntax.
       **)
      Variable vars : variables types.
      Variable G : hlist (@tvarD _) vars.
      Variable cs : codeSpec (tvarD pcType) (tvarD stateType).

      Definition himp (gl gr : sexpr vars) : Prop :=
        forall m, valid cs nil (sexprD gl G m) -> valid cs nil (sexprD gr G m).

      Require Import RelationClasses.

      Global Instance Relf_himp : Reflexive himp.
      Proof.
        red. unfold himp. firstorder.
      Qed.
      Global Instance Trans_himp : Transitive himp.
      Proof.
        red. unfold himp. firstorder.
      Qed.

      Ltac doIt :=
        unfold himp; simpl; intros;
          repeat match goal with
                   | [ h : HT.smem , H : forall x : HT.smem , _ |- _ ] => specialize (H h)
                   | [ H : _ -> _ |- _ ] => apply H; clear H
                   | [ H : ?X -> _ , H' : ?X |- _ ] => apply H in H'; clear H
                 end; goPropX;
          repeat match goal with
                   | [ |- exists x, _ ] => eexists
                   | [ |- _ /\ _ ] => split
                   | [ |- simplify _ _ _ ] => eassumption
                 end.
          
      Theorem star_comm_p : forall P Q R, himp (Star P Q) R -> himp (Star Q P) R.
      Proof.
        doIt. eapply HT.split_comm. auto.
      Qed.
      Theorem star_comm_c : forall P Q R, himp R (Star P Q) -> himp R (Star Q P).
      Proof.
        doIt. eapply HT.split_comm. auto.
      Qed.
  
      Theorem star_assoc_p : forall P Q R S,
        himp (Star P (Star Q R)) S -> himp (Star (Star P Q) R) S.
      Proof.
        doIt. apply HT.split_comm. apply HT.split_comm in H. eapply HT.split_assoc; try eassumption. apply HT.split_comm. eassumption. eapply HT.disjoint_split_join.
        apply HT.disjoint_comm. eapply HT.split_split_disjoint; eauto.
        apply HT.split_comm in H0; eassumption.
      Qed.
      Theorem star_assoc_c : forall P Q R S, 
        himp S (Star P (Star Q R)) -> himp S (Star (Star P Q) R).
      Proof.
        doIt. eapply HT.split_assoc; eassumption. apply HT.split_comm.
        apply HT.disjoint_split_join. apply HT.disjoint_comm.
        eapply HT.split_split_disjoint. apply HT.split_comm. eassumption. eassumption.
      Qed.

      Theorem star_cancel : forall P Q R, himp Q R -> himp (Star P Q) (Star P R).
      Proof.
        unfold himp; simpl; intros;
          repeat match goal with
                   | [ H : _ -> _ |- _ ] => apply H; clear H
                   | [ H : ?X -> _ , H' : ?X |- _ ] => apply H in H'; clear H
                 end; goPropX. specialize (H x0). 
        doIt. eassumption. cut (valid cs nil (sexprD R G x0)). intros. doIt. apply H.
        doIt.
      Qed.
(*
      Lemma valid_smem_eq : forall vars (P : sexpr vars) G E m m',
        valid cs E (sexprD P G m) -> HT.smem_eq m m' -> valid cs E (sexprD P G m').
      Proof.
        clear. induction P. simpl.
          doIt. eapply Inj_E in H. eassumption. intros.  eapply Inj_I.
          eapply HT.semp_mor. 2: eassumption. symmetry. auto.
          
          doIt.  eapply Inj_E in H. eassumption. intros.  eapply Inj_I. auto.
          
          doIt. admit. (* star *)

          doIt. eapply Exists_E in H. eassumption. intros. eapply Exists_I.
          econstructor.
*)

      Theorem star_emp_p : forall P Q, himp P Q -> himp (Star (Emp _) P) Q.
        (** TODO: I need to prove sexpr is parametric on the memory.
         ** This is a hard proof with the current definition of symbolic heaps
         ** and omitting the extensional equality axiom.
         **)
      Proof.
      Admitted.
      Theorem star_emp_c : forall P Q, himp P Q -> himp P (Star (Emp _) Q).
      Admitted.

    End Himp.

    Section SProver.
      Definition Himp := @himp nil HNil.

      Inductive SepResult (cs : codeSpec (tvarD pcType) (tvarD stateType)) (gl gr : sexpr nil) : Type :=
      | Solved : Himp cs gl gr -> SepResult cs gl gr
      | Remaining : forall l r, (Himp cs l r -> Himp cs gl gr) -> SepResult cs gl gr.

      Definition SProverT : Type := forall
        (cs : codeSpec (tvarD pcType) (tvarD stateType)) 
        (hyps : list (@Qexpr types funcs)) (** Pure Premises **)
        (gl gr : sexpr nil),
        SepResult cs gl gr.
    
    End SProver.

  End env.

  Implicit Arguments Emp [ types funcs pcType stateType sfuncs consts vars ].
  Implicit Arguments Inj [ types funcs pcType stateType sfuncs consts vars ].
  Implicit Arguments Star [ types funcs pcType stateType sfuncs consts vars ].
  Implicit Arguments Exists [ types funcs pcType stateType sfuncs consts vars ].
  Implicit Arguments Cptr [ types funcs pcType stateType sfuncs consts vars ].
  Implicit Arguments Func [ types funcs pcType stateType sfuncs consts vars ].
  Implicit Arguments Const [ types funcs pcType stateType sfuncs consts vars ].

  Implicit Arguments Solved [ types funcs pcType stateType stateMem sfuncs consts cs gl gr ].
  Implicit Arguments Remaining [ types funcs pcType stateType stateMem sfuncs consts cs gl gr ].

  Section BabySep.
    Variable types : list type.
    Variable fs : functions types.
    Variable pcType : tvar types.    
    Variable stateType : tvar types.
    Variable stateMem : tvarD stateType -> B.mem.
    Variable sfuncs : list (ssignature pcType stateType).
    Variable consts : list (PropX (tvarD pcType) (tvarD stateType)).

    Definition ReflSep : @SProverT types fs pcType stateType stateMem sfuncs consts.
    red. refine (fun _ _ gl gr =>
      match sexprCmp gl gr with
        | Env.Eq _ => Solved _
        | _ => Remaining gl gr _ 
      end); eauto.
    subst. unfold Himp, himp, himp. auto.
    Defined.

    Require Import PMap.

    Parameter map : Type -> Type -> Type.

    Parameter dmap_join : forall {K} {V}, @dmap K V -> dmap K V -> dmap K V.
    Parameter map_empty : forall K V, map K V.
    Parameter map_fold : forall {A} {K} {V} (f : A -> K -> V -> A) (a : A) (m : map K V), A.
    Parameter map_insert : forall {K} {V}, K -> V -> @map K V -> map K V.
    Parameter map_join : forall {K} {V}, map K V -> @map K V -> map K V.
    Parameter map_remove : forall {K} {V}, K -> map K V -> option (V * map K V).

    Parameter dmap_join_empty : forall {K} {V} (v : @dmap K V), dmap_join dmap_empty v = v.
    Parameter map_join_empty : forall {K} {V} (v : map K V), map_join (map_empty _ _) v = v.
    
    Parameter dmap_fold_empty : forall A K V f (a : A), dmap_fold f a (@dmap_empty K V) = a.
    Parameter map_fold_empty : forall A K V f (a : A), map_fold f a (@map_empty K V) = a.


    Record SHeap vars : Type :=
    { funcs  : @dmap (fin sfuncs) (fun f => list (hlist (expr fs vars) (SDomain (get sfuncs f))))
    ; cptrs  : map (expr fs vars pcType) (sexpr fs sfuncs consts (stateType :: vars))
    ; pures  : list (expr fs vars None)
    ; cnsts  : list (fin consts)
    ; other  : list (sexpr fs sfuncs consts vars)
    }.
  
    Definition SHeap_empty vars : SHeap vars := 
      {| funcs := dmap_empty
        ; cptrs := map_empty _ _
        ; pures := nil
        ; cnsts := nil
        ; other := nil
        |}.

    Definition denote vars (h : SHeap vars) :  sexpr fs sfuncs consts vars :=
      let a := dmap_fold (fun a x y => fold_left (fun a y => Star (Func x y) a) y a) Emp (funcs h) in
      let b := map_fold (fun a x y => Star (Cptr x y) a) Emp (cptrs h) in
      let c := fold_right (fun x a => Star (Inj x) a) Emp (pures h) in
      let d := fold_right (fun x a => Star (Const x) a) Emp (cnsts h) in
      let e := fold_right (fun x a => Star x a) Emp (other h) in
      Star a (Star b (Star c (Star d e))).

    Fixpoint hash_rec T vars (s : sexpr fs sfuncs consts vars) 
      :  (   @dmap (fin sfuncs) (fun f => list (hlist (expr fs vars) (SDomain (get sfuncs f))))
          -> map (expr fs vars pcType) (sexpr fs sfuncs consts (stateType :: vars))
          -> list (expr fs vars None)
          -> list (fin consts)
          -> list (sexpr fs sfuncs consts vars) -> T)
      -> @dmap (fin sfuncs) (fun f => list (hlist (expr fs vars) (SDomain (get sfuncs f))))
      -> map (expr fs vars pcType) (sexpr fs sfuncs consts (stateType :: vars))
      -> list (expr fs vars None)
      -> list (fin consts)
      -> list (sexpr fs sfuncs consts vars)
      -> T :=
      match s in @sexpr _ _ _ _ _ _ vs 
        return 
           (   @dmap (fin sfuncs) (fun f => list (hlist (expr fs vs) (SDomain (get sfuncs f))))
            -> map (expr fs vs pcType) (sexpr fs sfuncs consts (stateType :: vs))
            -> list (expr fs vs None)
            -> list (fin consts)
            -> list (sexpr fs sfuncs consts vs) -> T)
        -> @dmap (fin sfuncs) (fun f => list (hlist (expr fs vs) (SDomain (get sfuncs f))))
        -> map (expr fs vs pcType) (sexpr fs sfuncs consts (stateType :: vs))
        -> list (expr fs vs None)
        -> list (fin consts)
        -> list (sexpr fs sfuncs consts vs)
        -> T
        with
        | Emp _ => fun cc => cc 
        | Inj _ p => fun cc fs cps ps cs ot =>
          cc fs cps (p :: ps) cs ot 
        | Star _ l r => fun cc =>
          hash_rec l (hash_rec r cc)
        | Func _ f args => fun cc fs cps ps cs ot =>
          match dmap_remove (@finCmp _ _) f fs with
            | None =>
              cc (dmap_insert (@finCmp _ _) f (args :: nil) fs) cps ps cs ot
            | Some (v,fs') =>
              cc (dmap_insert (@finCmp _ _) f (args :: v) fs') cps ps cs ot
          end
        | Cptr _ p s => fun cc fs cps ps cs ot =>
          cc fs (map_insert p s cps) ps cs ot 
        | x => fun cc fs cps ps cs ot =>
          (** TODO : Other cases are problematic... **)
          cc fs cps ps cs (x :: ot)
      end.

    Definition hash_cc T vars (s : sexpr fs sfuncs consts vars)
      (cc : @dmap (fin sfuncs) (fun f => list (hlist (expr fs vars) (SDomain (get sfuncs f))))
       -> map (expr fs vars pcType) (sexpr fs sfuncs consts (stateType :: vars))
       -> list (expr fs vars None)
       -> list (fin consts)
       -> list (sexpr fs sfuncs consts vars) -> T) : T :=
      @hash_rec T vars s cc dmap_empty (map_empty _ _) nil nil nil.

    Section WithCS.
    Variable cs : codeSpec (tvarD pcType) (tvarD stateType).

(*
    Existing Instance M.Refl_himp.
    Existing Instance M.Trans_himp.
*)

    Ltac cancel_all :=
      repeat apply star_assoc_p;
        do 10 (repeat eapply star_assoc_c;
          (reflexivity || simple apply star_emp_c || simple apply star_emp_p || simple apply star_cancel || simple apply star_comm_c)).

    Lemma denote_hash_rec : forall vars (s : sexpr fs sfuncs consts vars) P (cc : _ -> _ -> _ -> _ -> _ -> SHeap vars) G,
      (forall A B C D E, 
        himp stateMem G cs 
          (denote (cc D E A B C))
          (Star P (denote (Build_SHeap D E A B C)))) ->
      forall A B C D E,
      himp stateMem G cs (denote (hash_rec s cc A B C D E)) (Star (Star (denote (Build_SHeap A B C D E)) P) s).
    Proof.
      unfold hash_cc, Himp; do 2 intro.
      induction s; intros; simpl; instantiate;
        try solve [ cancel_all; eauto | etransitivity; [ eapply H | ]; unfold denote; simpl; do 5 cancel_all ].
        (* Star *)
        etransitivity. eapply IHs1. intros. etransitivity. eapply IHs2. intros. etransitivity. eapply H. reflexivity.
        instantiate (1 := Star P s2). cancel_all. repeat cancel_all.
    Admitted.

    Theorem denote_hash_cc : forall (s : sexpr fs sfuncs consts nil),
      Himp stateMem cs (denote (hash_cc s (@Build_SHeap nil))) s.
    Proof.
      unfold Himp. intros. unfold hash_cc. etransitivity. eapply denote_hash_rec.
      instantiate (1 := Emp). intros. 
      generalize (denote {| funcs := D; cptrs := E; pures := A; cnsts := B; other := C |}).
      intros; cancel_all. unfold denote. simpl. rewrite map_fold_empty. 
      repeat (apply star_emp_p || apply star_assoc_p). reflexivity.
    Qed.

    Theorem denote_hash_cc_p : forall (s : sexpr fs sfuncs consts nil),
      Himp stateMem cs s (denote (hash_cc s (@Build_SHeap nil))).
    Proof.
    Admitted.


    (** Procedure:
     ** - Hash the left hand side
     ** - ?? Handle implications...
     ** - ?? Generate <> constraints ??
     ** - For each right hand side conjunct
     **   - if it is in the SHeap
     **       cancel
     **     else 
     **       ?? is this automatically problematic, this procedure probably won't prove it
     ** - Discharge pure constraints with solver...
     **)

(*
    Goal forall cs (a : fin consts), 
      Himp stateMem cs (Const fs sfuncs nil a) (Const fs sfuncs nil a).
      intros.
      pose (ReflSep cs nil (Const _ _ nil a) (Const _ _ nil a)). simpl in *.
      (** Note: everything has to be concrete in order for simplification to work! **)
      unfold ReflSep in *. unfold sexprCmp in *.
      destruct (finCmp a a). simpl in *. 
      match goal with
        | [ H := Some ?X |- _ ] => generalize X
      end. auto.
      congruence.
    Defined.
*)

   Section TakeOut.
      Context {T : Type}.
      Variable Teq : T -> T -> bool.
      
      Require Import List.
      Fixpoint take_out (v : T) (ls : list T) (r : list T): option (list T) :=
        match ls with
          | nil => None
          | a :: b => if Teq a v then Some (r ++ b) else take_out v b (a :: r)
        end.
    End TakeOut.


    Fixpoint All vars (ls : list (expr fs vars None)) : hlist (@tvarD _) vars -> Prop :=
      match ls with
        | nil => fun _ => True
        | a :: b => fun G => exprD G a /\ All b G
      end.

    (** Eliminate e from the symbolic heap and return the set of pure facts that 
     ** imply the conclusion
     **)
    Fixpoint sepCancel vars (e : sexpr fs sfuncs consts vars) {struct e}
      : SHeap vars -> SHeap vars -> SHeap vars * SHeap vars :=
      match e in sexpr _ _ _ vars 
        return SHeap vars -> SHeap vars -> SHeap vars * SHeap vars
        with
        | Emp _ => fun h rem => (h, rem)
        | Func _ f a => fun h rem =>
          match dmap_remove (@finCmp _ _) f (funcs h) with
            | Some (ls, fs') => 
              match take_out (fun x y => if hlistEq (@exprEq _ _ _ ) x y then true else false) a ls nil with
                | None => (h,rem)
                | Some nil => 
                  ({| funcs := fs' 
                    ; cptrs := cptrs h
                    ; pures := pures h
                    ; other := other h
                    ; cnsts := cnsts h
                    |}, rem)
                | Some v =>
                  ({| funcs := dmap_insert (@finCmp _ _) f v fs'
                    ; cptrs := cptrs h
                    ; pures := pures h
                    ; other := other h
                    ; cnsts := cnsts h
                    |}, rem)
              end
            | None => (h,rem)
          end              
        | Cptr _ p s => fun h rem =>
          match map_remove p (cptrs h) with
            | Some (s', cp') => 
              match sexprCmp s s' with
                | Env.Eq _ => 
                ({| funcs := funcs h 
                  ; cptrs := cp'
                  ; pures := pures h
                  ; other := other h
                  ; cnsts := cnsts h
                  |}, rem)
                | _ => (h,rem)
              end
           | None => (h,rem)
          end              
        | Star _ l r => fun h rem =>
          let '(h',rem') := sepCancel l h rem in
          sepCancel r h' rem'
        | _ => fun h rem => (h,rem)
      end.
    
    Lemma sepCancel_cancels' : forall vars G e h r rl rr,
      @sepCancel vars e h r = (rl, rr) ->
      forall P,
      himp stateMem G cs (denote rl) (Star (denote rr) P) ->
      himp stateMem G cs (denote h) (Star (Star e (denote r)) P).
    Proof.
      induction e; simpl; intros;
        repeat match goal with
                 | [ H : (_,_) = (_,_) |- _ ] => inversion H; clear H; subst
                 | [ H : sepCancel _ _ _ = (_,_) , H' : _ |- _ ] => apply H' in H; clear H'
               end;
        try solve [ etransitivity; [ eassumption | ]; do 5 cancel_all ].
      Focus 2.
      (* star *)
      case_eq (sepCancel e1 h r). intros. rewrite H1 in *.
      specialize (@IHe1 G _ _ _ _ H1).
      specialize (@IHe2 G _ _ _ _ H). 
      etransitivity. eapply IHe1. etransitivity. eapply IHe2. eassumption.
      instantiate (1 := (Star e2 P)). generalize (denote s0); intros; cancel_all.
      generalize (denote r); intros; cancel_all.
    Admitted.

    Theorem sepCancel_cancels : forall e h rl rr,
      sepCancel e h (SHeap_empty nil) = (rl, rr) ->
      Himp stateMem cs (denote rl) (denote rr) ->
      Himp stateMem cs (denote h) e.
    Proof.
      unfold Himp; intros. etransitivity. eapply sepCancel_cancels'. eassumption.
      instantiate (1 := Emp). etransitivity. eassumption. generalize (denote rr).
      intros; cancel_all. unfold denote. simpl. rewrite map_fold_empty. 
      repeat (apply star_comm_p; repeat apply star_assoc_p; apply star_emp_p).
      apply star_comm_p;
        repeat (apply star_comm_p; repeat apply star_assoc_p; apply star_emp_p).
      apply star_comm_p;
        repeat (apply star_comm_p; repeat apply star_assoc_p; apply star_emp_p).
      apply star_comm_p;
        repeat (apply star_comm_p; repeat apply star_assoc_p; apply star_emp_p).
      apply star_comm_p;
        repeat (apply star_comm_p; repeat apply star_assoc_p; apply star_emp_p).
      reflexivity.
    Qed.
  
  End WithCS.

    Definition CancelSep : @SProverT types fs pcType stateType stateMem sfuncs consts.
    red. refine (fun _ _ gl gr =>
      let lhs := hash_cc gl (@Build_SHeap nil) in
      match sepCancel gr lhs (SHeap_empty _) as k 
        return sepCancel gr lhs (SHeap_empty _) = k -> _ with
        | (lhs',rhs') => fun pf =>
          Remaining (denote lhs') (denote rhs') _
      end (eq_refl _)).
      intros. etransitivity. 2: eapply sepCancel_cancels. 2: eassumption. 2: eauto.
      unfold lhs. etransitivity. eapply denote_hash_cc_p. reflexivity.
    Defined.


  End BabySep.

  


  Section QSexpr.
    (** Guarded separation logic expressions **)
  End QSexpr.
    

End SepExpr.
Require Export Expr.