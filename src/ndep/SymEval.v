Require Import List.
Require Import Heaps SepTheoryX.
Require Import IL.
Require Import Env.
Require Import Bedrock.ndep.Expr Bedrock.ndep.SepExpr Bedrock.ndep.Provers.

Require Import SepIL SepTac.

Set Implicit Arguments.
Set Strict Implicit.

(*
Module Evaluator (B : Heap with Definition mem := W -> B) (ST : SepTheoryX.SepTheoryXType B).
  
  Module Import SEP := SepExpr B ST.
*)
  Module Import SEP := SepTac.SEP.

  Section typed.

    Variable types' : list type.
    Definition pcType : tvar := tvType 0.
    Definition stateType : tvar := tvType 1.

    Definition types := bedrock_types ++ types'.

    Record SymEval : Type :=
    { Predicate : ssignature types pcType stateType
    ; sym_read  : 
      forall (hyps args : list (expr types)) (p : expr types), option (expr types)
    ; sym_write : 
      forall (hyps args : list (expr types)) (p v : expr types),
        option (list (expr types))
    ; sym_read_correct : forall funcs args uvars vars P cs hyps pe ve m s,
      sym_read hyps args pe = Some ve ->
      hlist (FalseDefault funcs) hyps ->
      match applyD (@exprD types funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate) with
        | None => False
        | Some p => ST.satisfies cs (ST.star p P) s m
      end ->
      match exprD funcs uvars vars pe pcType , exprD funcs uvars vars ve pcType with
        | Some p , Some v =>
          ReadWord s m p = v 
        | _ , _ => False
      end
    ; sym_write_correct : forall funcs args uvars vars P cs hyps pe ve v m s args',
      sym_write hyps args pe ve = Some args' ->
      hlist (FalseDefault funcs) hyps ->
      exprD funcs uvars vars ve pcType = Some v ->
      match applyD (@exprD types funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate) with
        | None => False
        | Some p => ST.satisfies cs (ST.star p P) s m
      end ->
      match exprD funcs uvars vars pe pcType with
        | Some p =>
          match applyD (@exprD types funcs uvars vars) (SDomain Predicate) args' _ (SDenotation Predicate) with
            | None => False
            | Some pr => ST.satisfies cs (ST.star pr P) s (WriteWord s m p v)
          end
        | _ => False
      end
    }.

    Definition defaultSymEval (P : ssignature types pcType stateType) : SymEval.
    refine (
      {| Predicate    := P
       ; sym_read     := fun _ _ _ => None
       ; sym_write    := fun _ _ _ _ => None
       ; sym_read_correct := _
       ; sym_write_correct := _
       |}); 
    abstract (simpl; intros; congruence).
    Defined.

    Section evaluator.
      Inductive matches : list (ssignature types pcType stateType) -> list SymEval -> Prop :=
      | Match_nil : matches nil nil
      | Match_cons : forall e es s ss, Predicate e = s -> matches ss es -> matches (s :: ss) (e :: es).
(*
      Fixpoint matches (sfuncs : list (ssignature types pcType stateType)) (evals : list SymEval) : Prop :=
        match evals with
          | nil => True
          | e :: es =>
            match sfuncs with
              | nil => False
              | s :: ss => Predicate e = s /\ matches ss es
            end 
        end.
*)
      Variable evals : list SymEval.

      Section fold_find.
        Variable T U : Type.
        Variable F : nat -> T -> option U.
        
        Fixpoint fold_find (m : FM.t T) : option (nat * U) :=
          match m with 
            | FM.MLeaf => None
            | FM.MBranch l k v r =>
              match F k v with
                | Some z => Some (k, z)
                | None => 
                  match fold_find l with
                    | None => fold_find r 
                    | Some k => Some k
                  end
              end
          end.
      End fold_find.

      Definition symeval_read (hyps : list (expr types)) (p : expr types) (s : SHeap types pcType stateType) 
        : option (expr types) :=
        let hyps := hyps ++ pures s in
        let res := 
          fold_find (fun k v => 
            match nth_error evals k with
              | Some ev =>
                let reader := sym_read ev hyps in
                  List.fold_left (fun acc args =>
                    match acc with
                      | Some _ => acc
                      | None => reader args p 
                    end) v None
              | _ => None
            end)
          (impures s)
        in match res with
             | None => None
             | Some a => Some (snd a)
           end.

      Variable funcs : functions types.
      Variable sfuncs : list (ssignature types pcType stateType).
      Hypothesis evals_matches : matches sfuncs evals.

      Theorem symeval_read_correct : forall hyps pe s ve,
        symeval_read hyps pe s = Some ve ->
        hlist (FalseDefault funcs) hyps ->
        forall uvars vars cs stn m,
        ST.satisfies cs (@sexprD types funcs pcType stateType sfuncs (SEP.sheapD s) uvars vars) stn m -> 
        match exprD funcs uvars vars ve pcType , exprD funcs uvars vars pe pcType with
          | Some v , Some p => ReadWord stn m p = v 
          | _ , _ => False
        end.
      Proof.
(*
        Opaque tvarD.
        unfold symeval_read. destruct s; simpl.
        induction impures0; simpl in *.
          intros; congruence.

          intros. 
          Lemma satisfies_lemma : forall cs stn funcs sfuncs uvars vars0 m mp k v other0 pures0,
            ST.satisfies cs
            (sexprD funcs sfuncs
              (sheapD
                {| impures := mp ;
                   pures := pures0;
                   other := other0 |}) uvars vars0) stn m ->
            FM.find k mp = Some v ->
            ST.satisfies cs 
            (sexprD funcs sfuncs (starred (Func k) v (@Emp types pcType stateType)) uvars vars0) stn m.
          Proof.
            clear. induction mp; simpl; intros.
              congruence.

              eapply ST.satisfies_himp in H.
              2: eapply ST.heq_himp; eapply sheapD_sheapD'.
              unfold sheapD' in H. simpl in H.
          generalize H0. unfold sheapD in H0. simpl in H0.

              destruct (Compare_dec.lt_eq_lt_dec k n). destruct s.
              eapply IHmp1 in H0; eauto.
              Focus 2.

eapply ST.satisfies_himp in H0.
          2: eapply ST.heq_himp; eapply sheapD_sheapD'.
          unfold sheapD' in H0. simpl in H0.
          generalize H0. unfold sheapD in H0. simpl in H0.
          

          assert (ST.satisfies cs (sexprD funcs sfuncs (sheapD {| impures := impures0_1 ; pures := pures0 ; other := other0 |}) uvars vars0) stn m).
          cut (ST.satisfies (sexprD funcs sfuncs (sheapD {| impures := impures0_2 ; pures := pures0 ; other := other0 |}) uvars vars0) cs stn m).
          Focus.

          Ltac head x :=
            match x with
              | match ?y with
                  | Some _ => _
                  | None => _
                end => head y
              | _ => x
            end.

          Print ST.
          Ltac more :=
          repeat match goal with
                   | [  H' : _ |- _ ] => 
                     specialize (H' _ (refl_equal _))
                   | [ H : hlist (FalseDefault _) _, H' : _  |- _ ] =>
                     specialize (H' H)
                   | [ H : ST.satisfies _ _ _ _ , H' : _  |- _ ] =>
                     specialize (H' _ _ _ _ _ H)
                   | _ => solve [ eauto ] 
                   | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; try subst
                   | [ H : forall x, None = Some x -> _ |- _ ] => clear H
                   | [ H : context [ match ?X with
                                       | Some _ => _
                                       | None => _
                                     end ] |- _ ] =>
                   let X := head X in
                     match X with 
                       | fold_left _ _ _ =>
                         generalize dependent H; case_eq (X); intros
                       | fold_find _ _ =>
                         generalize dependent X; let H := fresh in intro H; destruct H; intros
(*
                          (idtac "matched fold_find";
                          intros; generalize dependent H; case_eq X;
                            [ idtac "a"; let z := fresh "p" in intro z; let H' := fresh in intro H'; idtac "trying to rw"; 
                              let v := eval unfold H' in H' in idtac v ; rewrite H' in *; idtac "a done" |
                              idtac "b"; let H' := fresh in intros H'; rewrite H' in * ; idtac "b done" ]; intros ; idtac "completed")
*)

                       | exprD _ _ _ _ _ => fail 2
                     end
                   | _ => congruence
                 end; eauto.
          destruct (nth_error evals n); intros; more; try destruct o; more.
          Print sheapD.
          Lemma scan_function_correct : forall uvars vars0 t cs stn m pe ve k hyps s acc,
            fold_left
            (fun (acc : option (expr types)) (args : list (expr types)) =>
              match acc with
                | Some _ => acc
                | None => sym_read s hyps args pe
              end) t acc = Some ve ->
            match acc with
              | None => True
              | Some ve =>
                match exprD funcs uvars vars0 ve pcType with
                  | Some v =>
                    match exprD funcs uvars vars0 pe pcType with
                      | Some p0 => ReadWord stn m p0 = v
                      | None => False
                    end
                  | None => False
                end
            end ->                
            nth_error evals k = Some (Some s) ->
            ST.satisfies (@sexprD types funcs pcType stateType sfuncs (starred' (Func k) t Emp) uvars vars0) cs stn m ->
            match exprD funcs uvars vars0 ve pcType with
              | Some v =>
                match exprD funcs uvars vars0 pe pcType with
                  | Some p0 => ReadWord stn m p0 = v
                  | None => False
                end
              | None => False
            end.
          Proof.
            induction t; simpl in *.
              intros; subst; auto.

              intros. destruct acc.
              assert (e = ve).
              generalize H. clear.
              induction t; eauto; simpl; congruence.
              subst. eauto.
              eapply IHt; eauto.
              assert (nth_error sfuncs k = Some (Predicate s)).
              Focus.
              generalize H1. generalize evals_matches. clear. generalize sfuncs. clear. induction evals; simpl.
                destruct k; intros; simpl in *. inversion H1. inversion H1.
                destruct sfuncs; simpl in *; intros; try intuition.
                destruct k; simpl in *. inversion H1; clear H1; subst. subst. reflexivity.
                eapply IHl in H0; eauto.
                

                destruct k. simpl. inversion 2. subst. destruct sfuncs; auto.
                simpl in *; eauto. intuition. subst. reflexivity.
                destruct sfuncs; intuition. 

              simpl in *. dest
*)
      Admitted.

      Fixpoint map_maybe_map (T : Type) (F : nat -> T -> option T) (m : FM.t T) 
        : option (FM.t T) :=
        match m with
          | FM.MLeaf => None
          | FM.MBranch l k v r =>
            match F k v with
              | Some v' => Some (FM.MBranch _ l k v' r)
              | None => 
                match map_maybe_map F l with
                  | Some l' => Some (FM.MBranch _ l' k v r)
                  | None => 
                    match map_maybe_map F r with
                      | Some r' => Some (FM.MBranch _ l k v r')
                      | None => None
                    end
                end
            end
        end.
        
      Fixpoint list_maybe_map (T : Type) (F : T -> option T) (m : list T) 
        : option (list T) :=
        match m with
          | nil => None
          | a :: b => 
            match F a with
              | None => match list_maybe_map F b with
                          | None => None
                          | Some b' => Some (a :: b')
                        end
              | Some a' => Some (a' :: b)
            end
        end.

      Definition symeval_write (hyps : list (expr types)) (p v : expr types) 
        (s : SHeap types pcType stateType) : option (SHeap types pcType stateType) :=
        let hyps := hyps ++ pures s in
        let res := 
          map_maybe_map (fun k =>
            match nth_error evals k with 
              | None => fun _ => None
              | Some ev =>
                let writer := sym_write ev hyps in
                list_maybe_map (fun args =>
                  writer args p v)
            end) (impures s)
        in
        match res with
          | None => None
          | Some i => Some {| impures := i ; pures := pures s ; other := other s |}
        end.

      Theorem symeval_write_correct : forall hyps pe s s' ve,
        symeval_write hyps pe ve s = Some s' ->
        hlist (FalseDefault funcs) hyps ->
        forall uvars vars cs stn m,
        ST.satisfies cs (@sexprD types funcs pcType stateType sfuncs (SEP.sheapD s) uvars vars) stn m -> 
        match exprD funcs uvars vars ve pcType , exprD funcs uvars vars pe pcType with
          | Some v , Some p => 
            ST.satisfies cs (@sexprD types funcs pcType stateType sfuncs (SEP.sheapD s) uvars vars) stn (WriteWord stn m p v)
          | _ , _ => False
        end.
      Proof.
      Admitted.
  (*
End Evaluator.
*)
    End evaluator.
  End typed.

  Section ptsto32_sym_eval.
    Variable types' : list type.
    
    Definition ptsto32_Predicate : ssignature (types types') pcType stateType :=
      Build_ssignature (types types') pcType stateType (pcType :: pcType :: nil) (@ptsto32 nil).
    
    (** Let's see how this works with ptsto **)
    Definition ptsto32_sym_read (hyps args : list (expr (types types'))) (p : expr (types types')) : option (expr (types types')) :=
      match args with
        | p' :: v :: nil =>
          if seq_dec p p' then Some v else None
        | _ => None
      end.
    
    Definition ptsto32_sym_write (hyps : list (expr (types types'))) (args : list (expr (types types'))) (p v : expr (types types')) : option (list (expr (types types'))) :=
      match args with
        | p' :: _ :: nil =>
          if seq_dec p p' then Some (p' :: v :: nil) else None
        | _ => None
      end.

    Require Import PropXTac.

    Theorem ptsto32_sym_read_correct : forall (funcs : functions (types types'))
      (args : list (expr (types types'))) (uvars vars0 : env (types types'))
      (P : hprop (tvarD (types types') pcType)
        (tvarD (types types') stateType) nil)
      (cs : PropX.codeSpec (tvarD (types types') pcType)
        (tvarD (types types') stateType))
      (hyps : list (expr (types types'))) (pe ve : expr (types types'))
      (m : BedrockHeap.mem) (s : settings),
      ptsto32_sym_read hyps args pe = Some ve ->
      hlist (FalseDefault funcs) hyps ->
      match
        applyD (exprD funcs uvars vars0) (SDomain ptsto32_Predicate) args
        (hprop (tvarD (types types') pcType) (tvarD (types types') stateType)
          nil) (SDenotation ptsto32_Predicate)
        with
        | Some p => ST.satisfies cs (star p P) s m
        | None => False
      end ->
      match exprD funcs uvars vars0 pe pcType with
        | Some p =>
          match exprD funcs uvars vars0 ve pcType with
            | Some v => ReadWord s m p = v
            | None => False
          end
        | None => False
      end.
    Proof.
      unfold ptsto32_Predicate; simpl in *; intros.
      destruct args; simpl in *; try congruence.
      destruct args; simpl in *; try congruence.
      destruct args; simpl in *; try congruence.
      destruct (expr_seq_dec pe e); try congruence.
      inversion H; clear H; subst.
      destruct (exprD funcs uvars vars0 e pcType); auto.
      destruct (exprD funcs uvars vars0 ve pcType); auto.
      eapply ST.satisfies_star in H0. destruct H0. clear H0.
      destruct H as [ ? [ ? ? ] ]. (** Breaks abstraction **)
      propxFo. unfold implode in H6. subst.
      repeat match goal with 
               | [ H : smem_get _ _ = _ |- _ ] =>
                 eapply satisfies_get in H; [ | eassumption ]; unfold BedrockHeap.mem_get in H; inversion H; subst
             end;
      eapply ReadWordFootprint; simpl; auto.
    Qed.

    Theorem ptsto32_sym_write_correct : forall (funcs : functions (types types'))
      (args : list (expr (types types'))) (uvars vars0 : env (types types'))
      (P : hprop (tvarD (types types') pcType)
        (tvarD (types types') stateType) nil)
      (cs : PropX.codeSpec (tvarD (types types') pcType)
        (tvarD (types types') stateType))
      (hyps : list (expr (types types'))) (pe ve : expr (types types'))
      (v : tvarD (types types') pcType) (m : BedrockHeap.mem) 
      (s : settings) (args' : list (expr (types types'))),
      ptsto32_sym_write hyps args pe ve = Some args' ->
      hlist (FalseDefault funcs) hyps ->
      exprD funcs uvars vars0 ve pcType = Some v ->
      match
        applyD (exprD funcs uvars vars0) (SDomain ptsto32_Predicate) args
        (hprop (tvarD (types types') pcType) (tvarD (types types') stateType)
          nil) (SDenotation ptsto32_Predicate)
        with
        | Some p => ST.satisfies cs (star p P) s m
        | None => False
      end ->
      match exprD funcs uvars vars0 pe pcType with
        | Some p =>
          match
            applyD (exprD funcs uvars vars0) (SDomain ptsto32_Predicate) args'
            (hprop (tvarD (types types') pcType)
              (tvarD (types types') stateType) nil)
            (SDenotation ptsto32_Predicate)
            with
            | Some pr => ST.satisfies cs (star pr P) s (WriteWord s m p v)
            | None => False
          end
        | None => False
      end.
    Proof.
      unfold ptsto32_Predicate; simpl in *; intros.
      destruct args; simpl in *; try congruence.
      destruct args; simpl in *; try congruence.
      destruct args; simpl in *; try congruence.
      destruct (expr_seq_dec pe e); try congruence.
      inversion H; clear H; subst. simpl.
      destruct (exprD funcs uvars vars0 e pcType); auto.
      destruct (exprD funcs uvars vars0 e0 pcType); try tauto.
      rewrite H0. clear H0.
    Admitted.
      
    Definition SymEval_ptsto32 : SymEval types' :=
      {| Predicate := ptsto32_Predicate 
       ; sym_read  := ptsto32_sym_read
       ; sym_write := ptsto32_sym_write
       ; sym_read_correct := ptsto32_sym_read_correct
       ; sym_write_correct := ptsto32_sym_write_correct
       |}.
  End ptsto32_sym_eval.

  Section Tests.

    Ltac isConst x :=
      constr:(false).
    
    Require Import PropX.
    Goal forall specs stn p v x,
      PropX.interp specs (![ptsto32 _ p v]%PropX (stn, x)) ->
      ReadWord stn (Mem x) p = v.
    Proof.
      intros. Check skipn.
      match goal with
        | [ |- context [ ReadWord ?STN ?M ?P ] ] =>
          match goal with
            | [ H : interp ?CS (?S (STN, ?ST)) |- _ ] =>
              let m := eval simpl in (Mem ST) in 
              match M with
                | m => 
                  match S with
                    | context [ sepFormula ?X ] =>
                      let pcT := constr:(W) in
                      let stateT := constr:(prod settings state) in
                      let Ts := eval unfold bedrock_types in bedrock_types in
                      let goals := constr:(X :: nil) in
                      let goals := eval unfold starB exB hvarB in goals in
                      let v := SEP.reflect_all pcT stateT ltac:(isConst) Ts goals in
                      match v with
                        | (?Ts, ?pcType, ?stateType, ?funcs, ?sfuncs, ?X :: nil) =>
                          SEP.reflect_expr ltac:(isConst) P Ts funcs (@nil tvar) (@nil tvar)
                            ltac:(fun funcs' p => 
                              let tys := eval simpl in (List.skipn (length (types nil)) Ts) in
                              generalize (@symeval_read_correct tys (SymEval_ptsto32 tys :: nil) funcs sfuncs nil p (snd (hash X))))
                      end
                  end
              end
          end
      end.

      simpl. unfold symeval_read. simpl. intro. specialize (H0 _ (refl_equal _) HNil).
      simpl in H0. eapply H0. apply nil. apply nil.
      unfold ST.satisfies. rewrite sepFormula_eq in H. unfold sepFormula_def in H.
      simpl in *. eexists. split. 2: eassumption.
    Abort.
      
    End Tests.


(* This is the instantiation of the old evaluator.
  Section ptsto32_sym_eval.
    Definition denotesTo (sfuncs : list (ssignature types pcType stateType)) (f : nat) 
      (Predicate : ssignature types pcType stateType) : Prop :=
      nth_error sfuncs f = Some Predicate.

    Record SymEval : Type :=
      { Predicate : ssignature types pcType stateType
      ; sym_read  : 
        forall (hyps args : list (expr types)) (p : expr types), option (expr types)
      ; sym_write : 
        forall (hyps : list (expr types)) (f : nat) (args : list (expr types)) (p v : expr types),
          option (sexpr types pcType stateType)
      ; sym_read_correct : forall funcs sfuncs f args uvars vars P cs
          hyps
          pe ve m s,
        denotesTo sfuncs f Predicate ->
        sym_read hyps args pe = Some ve ->
        hlist (FalseDefault funcs) hyps ->
        ST.satisfies 
          (@sexprD types funcs pcType stateType sfuncs (Star (Func f args) P) uvars vars)
          cs s m ->
        match exprD funcs uvars vars pe pcType , exprD funcs uvars vars ve pcType with
          | Some p , Some v =>
            ReadWord s m p = v 
          | _ , _ => False
        end
      ; sym_write_correct : forall funcs sfuncs f args uvars vars P cs
          hyps
          (pfW : tvarD types pcType = W)
          pe ve v m s s',
        denotesTo sfuncs f Predicate ->
        sym_write hyps f args pe ve = Some s' ->
        hlist (FalseDefault funcs) hyps ->
        exprD funcs uvars vars ve pcType = Some v ->
        ST.satisfies 
          (@sexprD types funcs pcType stateType sfuncs (Star (Func f args) P) uvars vars)
          cs s m ->
        match exprD funcs uvars vars pe pcType with
          | Some p =>
            ST.satisfies 
              (@sexprD types funcs pcType stateType sfuncs (Star s' P) uvars vars)
              cs s (WriteWord s m p v)
          | _ => False
        end
      }.


    Definition btypes : list type := bedrock_types.
    Variable types : list type.

    Definition ptsto32_Predicate : ssignature (btypes ++ types) pcType stateType :=
      Build_ssignature (btypes ++ types) pcType stateType (pcType :: pcType :: nil) (@ptsto32 nil).
      
  (** Let's see how this works with ptsto **)
    Definition ptsto32_sym_read (hyps args : list (expr (btypes ++ types))) (p : expr (btypes ++ types)) : option (expr (btypes ++ types)) :=
      match args with
        | p' :: v :: nil =>
          if seq_dec p p' then Some v else None
        | _ => None
      end.

    Definition ptsto32_sym_write (hyps : list (expr (btypes ++ types))) f (args : list (expr (btypes ++ types))) (p v : expr (btypes ++ types)) : option (sexpr (btypes ++ types) pcType stateType) :=
      match args with
        | p' :: v :: nil =>
          if seq_dec p p' then Some (Func f (p' :: v :: nil)) else None
        | _ => None
      end.

    Require Import PropXTac.

    Theorem ptsto32_sym_read_correct : forall (funcs : functions (Top.types types))
     (sfuncs : list (ssignature (Top.types types) pcType stateType))
     (f : nat) (args : list (expr (Top.types types)))
     (uvars vars0 : list {t : tvar & tvarD (Top.types types) t})
     (P : sexpr (Top.types types) pcType stateType)
     (cs : PropX.codeSpec (tvarD (Top.types types) pcType)
             (tvarD (Top.types types) stateType))
     (hyps : list (expr (Top.types types))) (pe ve : expr (Top.types types))
     (m : BedrockHeap.mem) (s : settings),
     denotesTo sfuncs f ptsto32_Predicate ->
     ptsto32_sym_read hyps args pe = Some ve ->
     hlist (FalseDefault funcs) hyps ->
     ST.satisfies (sexprD funcs sfuncs (Star (Func f args) P) uvars vars0) cs s
     m ->
     match exprD funcs uvars vars0 pe pcType , exprD funcs uvars vars0 ve pcType with
       | Some p , Some v => ReadWord s m p = v
       | _ , _ => False
     end.
    Proof.
      intros.
      destruct args; simpl in H0; try congruence.
      destruct args; simpl in H0; try congruence.
      destruct args; simpl in H0; try congruence.
      unfold denotesTo in *. simpl in *. rewrite H in H1; clear H. simpl in *. 
      repeat match goal with
        | [ H : (if ?X then Some _ else None) = Some _ |- _ ] =>
          destruct X; inversion H; clear H; subst
        | [ |- match ?X with
                 | Some _ => _
                 | None => False
               end ] => destruct X
      end;
      destruct H1 as [ ? [ ? ? ] ]; try solve [ propxFo ].
      propxFo. unfold implode in H8. subst.
      eapply satisfies_split in H1; eauto. destruct H1.
      repeat match goal with 
               | [ H : smem_get _ _ = _ |- _ ] =>
                 eapply satisfies_get in H; [ | eassumption ]; unfold BedrockHeap.mem_get in H; inversion H; subst
             end;
      eapply ReadWordFootprint; simpl; auto.
    Qed.

    Theorem ptsto32_sym_write_correct : forall (funcs : functions (Top.types types))
      (sfuncs : list (ssignature (Top.types types) pcType stateType))
      (f : nat) (args : list (expr (Top.types types)))
      (uvars vars0 : env (Top.types types))
      (P : sexpr (Top.types types) pcType stateType)
      (cs : PropX.codeSpec (tvarD (Top.types types) pcType)
        (tvarD (Top.types types) stateType))
      (hyps : list (expr (Top.types types))),
      tvarD (Top.types types) pcType = W ->
      forall (pe ve : expr (Top.types types))
        (v : tvarD (Top.types types) pcType) (m : BedrockHeap.mem)
        (s : settings) (s' : sexpr (Top.types types) pcType stateType),
        denotesTo sfuncs f ptsto32_Predicate ->
        ptsto32_sym_write hyps f args pe ve = Some s' ->
        hlist (FalseDefault funcs) hyps ->
        exprD funcs uvars vars0 ve pcType = Some v ->
        ST.satisfies (sexprD funcs sfuncs (Star (Func f args) P) uvars vars0) cs s
        m ->
        match exprD funcs uvars vars0 pe pcType with
          | Some p =>
            ST.satisfies (sexprD funcs sfuncs (Star s' P) uvars vars0) cs s
            (WriteWord s m p v)
          | None => False
        end.
    Proof.
      intros.
      destruct args; simpl in H1; try congruence.
      destruct args; simpl in H1; try congruence.
      destruct args; simpl in H1; try congruence.
      unfold denotesTo in *. simpl in *. rewrite H0 in H3; clear H0. simpl in *. 
      repeat match goal with
               | [ H : (if ?X then Some _ else None) = Some _ |- _ ] =>
                 destruct X; inversion H; clear H; subst
               | [ |- match ?X with
                        | Some _ => _
                        | None => False
                      end ] => destruct X
             end;
      destruct (exprD funcs uvars vars0 e0 pcType); destruct H3 as [ ? [ ? ? ] ]; propxFo.
    Admitted.

    Definition SymEval_ptsto32 : SymEval types :=
      {| Predicate := ptsto32_Predicate
       ; sym_read  := ptsto32_sym_read
       ; sym_write := ptsto32_sym_write
       ; sym_read_correct := ptsto32_sym_read_correct
       ; sym_write_correct := ptsto32_sym_write_correct
      |}.

  End  ptsto32_sym_eval.

*)