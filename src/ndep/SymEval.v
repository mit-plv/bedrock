Require Import List Env Word.
Require Import Heaps SepTheoryX.
Require Import Bedrock.ndep.Expr Bedrock.ndep.SepExpr Bedrock.ndep.Provers.

Set Implicit Arguments.
Set Strict Implicit.

Definition W := word 32.

Module Evaluator (B : Heap) (ST : SepTheoryX.SepTheoryXType B).
  Module Import SEP := SepExpr B ST.

  Section typed.
    Variable types' : list type.

    Variable stateIndex : nat.
    Variable pcIndex : nat.
    Variable ptrIndex : nat.
    Definition ptrType : type :=
      {| Impl := B.addr
       ; Eq := fun x y => match B.addr_dec x y with
                           | left pf => Some pf
                           | _ => None
                         end
       |}.
(*
    Variable wordIndex : nat.
    Definition wordType : type :=
      {| Impl := W
       ; Eq := fun x y => match weq x y with
                           | left pf => Some pf
                           | _ => None
                         end
       |}.
*)
    Variable byteIndex : nat.
    Definition byteType : type :=
      {| Impl := B
       ; Eq := fun x y => match weq x y with
                            | left pf => Some pf
                            | _ => None
                          end
       |}.

    Fixpoint updatePosition {T} (n : nat) (v : T) (ls : list T) : list T :=
      match n , ls with
        | 0 , nil => v :: nil
        | 0 , _ :: b => v :: b 
        | S n , nil => v :: updatePosition n v nil
        | S n , a :: b => a :: updatePosition n v b
      end.

    Lemma updatePosition_tvarD_eq : forall n types' t,
      tvarD (updatePosition n t types') (tvType n) = Impl t.
    Proof.
      clear. unfold tvarD.
      induction n; simpl; destruct types'; eauto.
    Defined.

(*
    Lemma updatePosition_tvarD_neq : forall t n types' m,
      n <> m ->
      tvarD (updatePosition m t types') (tvType n) = tvarD types' (tvType n).
    Proof.
      clear.
      induction n; destruct types'; destruct m; simpl; intros; try solve [ exfalso; omega ]; auto.
      unfold tvarD in *. rewrite IHn; eauto. omega.      
    Defined.
*)


    Definition types := 
(*      updatePosition stateIndex stateType (updatePosition pcIndex pcType (
        *)
      updatePosition ptrIndex ptrType (updatePosition byteIndex byteType types').

    Lemma ptrType_get : tvarD types (tvType ptrIndex) = B.addr.
      unfold types. apply updatePosition_tvarD_eq.
    Qed.


    Definition exprD_ptr (funcs : functions types) (uvars vars : env types) (e : expr types) : 
      option B.addr :=
      match ptrType_get in _ = t return option t with
        | refl_equal => 
          @exprD types funcs uvars vars e (tvType ptrIndex)
      end.

    Lemma byteType_get : tvarD types (tvType byteIndex) = B.
      unfold types. 
    Admitted.


    Definition exprD_byte (funcs : functions types) (uvars vars : env types) (e : expr types) : 
      option B :=
      match byteType_get in _ = t return option t with
        | refl_equal =>
          @exprD types funcs uvars vars e (tvType byteIndex)
      end.

    Record SymEval_byte (Predicate : ssignature types (tvType pcIndex) (tvType stateIndex))
      : Type :=
    { sym_read_byte  : 
      forall (hyps args : list (expr types)) (p : expr types), option (expr types)
    ; sym_write_byte : 
      forall (hyps args : list (expr types)) (p v : expr types),
        option (list (expr types))
    ; sym_read_byte_correct : forall funcs args uvars vars cs hyps pe ve m stn P,
      sym_read_byte hyps args pe = Some ve ->
      AllProvable funcs uvars vars hyps ->
      match 
        applyD (@exprD _ funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate)
        with
        | None => False
        | Some p => ST.satisfies cs (ST.star p P) stn m
      end ->
      match exprD_ptr funcs uvars vars pe , exprD_byte funcs uvars vars ve with
        | Some p , Some v =>
          ST.HT.smem_get p m = Some v
        | _ , _ => False
      end
    ; sym_write_byte_correct : forall funcs args uvars vars P cs hyps pe ve v m stn args',
      sym_write_byte hyps args pe ve = Some args' ->
      AllProvable funcs uvars vars hyps ->
      exprD_byte funcs uvars vars ve = Some v ->
      match
        applyD (@exprD _ funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate)
        with
        | None => False
        | Some p => ST.satisfies cs (ST.star p P) stn m
      end ->
      match exprD_ptr funcs uvars vars pe with
        | Some p =>
          match 
            applyD (@exprD _ funcs uvars vars) (SDomain Predicate) args' _ (SDenotation Predicate)
            with
            | None => False
            | Some pr => 
              ST.satisfies cs (ST.star pr P) stn (ST.HT.smem_set p v m)
          end
        | _ => False
      end
    }.

    Definition defaultSymEval_byte (P : ssignature types (tvType pcIndex) (tvType stateIndex))
      : SymEval_byte P.
    refine (
      {| sym_read_byte          := fun _ _ _ => None
       ; sym_write_byte         := fun _ _ _ _ => None
       ; sym_read_byte_correct  := _
       ; sym_write_byte_correct := _
       |}); 
    abstract (simpl; intros; congruence).
    Defined.

    (** The full tactic **)
    Variable sfuncs : list (ssignature types (tvType pcIndex) (tvType stateIndex)).

    Section search_read.
      Variable T : Type.
      Variable F : forall s, SymEval_byte s -> list (expr types) -> option T.

      Section arg.
        Variable ss : ssignature types (tvType pcIndex) (tvType stateIndex).
        Variable se : SymEval_byte ss.
        
        Fixpoint fold_args (es : list (list (expr types))) : option T :=
          match es with 
            | nil => None
            | a :: b => 
              match F se a with
                | None => fold_args b
                | Some r => Some r
              end
          end.
        
        Theorem fold_args_correct : forall es v,
          fold_args es = Some v ->
          exists k, In k es /\ F se k = Some v.
        Proof.
          clear. induction es.
          simpl; congruence.
          simpl. case_eq (F se a); intros.
          inversion H0. subst. eauto.
          eapply IHes in H0. destruct H0.
          exists x. tauto.
        Qed.          
      End arg.

      Variable impures : FM.t (list (list (expr types))).

      Fixpoint fold_known (k : list nat) :
        hlist (fun n : nat => match nth_error sfuncs n with
                                | None => Empty_set 
                                | Some ss => SymEval_byte ss
                              end) k
        -> option T :=
        match k as k 
          return hlist (fun n : nat => match nth_error sfuncs n with
                                         | None => Empty_set 
                                         | Some ss => SymEval_byte ss
                                       end) k
                 -> option T
          with
          | nil => fun _ => None
          | a :: b => fun ss =>
            match FM.find a impures with
              | None => fold_known (hlist_tl ss)
              | Some argss =>
                match nth_error sfuncs a as ss
                  return match ss with
                           | None => Empty_set 
                           | Some ss => SymEval_byte ss
                         end -> option T
                  with
                  | Some _ => fun se =>
                    match fold_args se argss with
                      | None => fold_known (hlist_tl ss)
                      | Some r => Some r
                    end
                  | None => fun err => match err with end
                end (hlist_hd ss)
            end
        end.
      
      Theorem fold_known_correct : forall k
        (h : hlist (fun n : nat => match nth_error sfuncs n with
                                     | None => Empty_set 
                                     | Some ss => SymEval_byte ss
                                   end) k) v,
        @fold_known k h = Some v ->
        exists n, exists ss,
          exists se :  SymEval_byte ss, exists ls, exists args, 
               nth_error sfuncs n = Some ss 
            /\ FM.find n impures = Some ls 
            /\ In args ls 
            /\ F se args = Some v.
      Proof.
        induction k; simpl.
          congruence.
          intros h v. specialize (IHk (hlist_tl h) v).
          rewrite (hlist_eta _ h) in *.
          generalize dependent (hlist_hd h). simpl.
          case_eq (FM.find a impures); intros; eauto 10.

          assert (exists k, nth_error sfuncs a = Some k).
          generalize y. clear.
          destruct (nth_error sfuncs a); [ eauto | destruct 1 ]. 
          destruct H1.
          generalize dependent y.
          rewrite H1. intro.
          case_eq (fold_args y l); intros; eauto 10.
          inversion H2; subst.
          eapply fold_args_correct in H0. destruct H0; eauto 10.
      Qed.
    End search_read.

    Variable known : list nat. 
    Variable evals : hlist (fun n : nat => match nth_error sfuncs n with
                                             | None => Empty_set 
                                             | Some ss => SymEval_byte ss
                                           end) known.

    Definition symeval_read_byte (hyps : list (expr types)) (p : expr types) 
      (s : SHeap types (tvType pcIndex) (tvType stateIndex))
      : option (expr types) :=
      let hyps := hyps ++ pures s in
      let reader _ seb args := 
        sym_read_byte seb hyps args p
      in
      fold_known reader (impures s) evals.

    Theorem symeval_read_byte_correct : forall cs stn hyps funcs pe ve s uvars vars (m : B.mem),
      symeval_read_byte hyps pe s = Some ve ->
      AllProvable funcs uvars vars hyps ->
      (exists sm, 
           ST.satisfies cs (sexprD funcs sfuncs (sheapD s) uvars vars) stn sm
        /\ ST.HT.satisfies sm m) ->
      match exprD_ptr funcs uvars vars pe , exprD_byte funcs uvars vars ve with
        | Some p , Some v => 
          B.mem_get m p = Some v
        | _ , _ => False
      end.
    Proof.
      unfold symeval_read_byte. intros.
      eapply fold_known_correct in H.
      do 5 destruct H. destruct H1.
      intuition.

      generalize (sheapD_pures _ _ _ _ _ H); intros.

      eapply sheapD_pull_impure 
        with (funcs := funcs) (sfuncs := sfuncs) (a := uvars) (c := vars0) (cs := cs)
        in H1.
      eapply starred_In in H3.
      destruct H3. rewrite H3 in H1.

      eapply sym_read_byte_correct 
        with (funcs := funcs) (uvars := uvars) (vars := vars0) (cs := cs) (stn := stn) (m := x4)
        in H6.
      3: instantiate (1 := sexprD funcs sfuncs (Star
            (sheapD
               {|
               impures := FM.remove x (impures s);
               pures := pures s;
               other := other s |})
            (starred (Func x) x5 Emp)) uvars vars0).
      destruct (exprD_ptr funcs uvars vars0 pe); auto.
      destruct (exprD_byte funcs uvars vars0 ve); auto.
      erewrite ST.HT.satisfies_get; eauto.

      eapply AllProvable_app; auto.

      unfold heq in *.
      rewrite H1 in H. simpl in *. rewrite ST.heq_star_comm in H.
      rewrite H2 in *. rewrite ST.heq_star_assoc in H.
      rewrite ST.heq_star_comm in H. rewrite ST.heq_star_assoc in H.
      generalize H. clear.
      match goal with 
        | [ |- context [ applyD ?A ?B ?C ?D ?E ] ] =>
          destruct (applyD A B C D E)
      end; auto.
      clear. intros.
      eapply ST.satisfies_star in H. do 2 destruct H. intuition.
      eapply ST.satisfies_pure in H0. PropXTac.propxFo.
    Qed.

    Section search_write.
      Variable T : Type.
      Variable F : forall s, SymEval_byte s -> T -> option T.

      Section arg.
        Variable ss : ssignature types (tvType pcIndex) (tvType stateIndex).
        Variable se : SymEval_byte ss.
        
        Fixpoint fold_args_update (es : list T) : option (list T) :=
          match es with 
            | nil => None
            | a :: b => 
              match F se a with
                | None => match fold_args_update b with
                            | None => None
                            | Some b => Some (a :: b)
                          end
                | Some r => Some (r :: b)
              end
          end.
        
        Theorem fold_args_update_correct : forall es es',
          fold_args_update es = Some es' ->
          exists pre, exists post, exists k, exists k',
            es = pre ++ k :: post /\
            F se k = Some k' /\
            es' = pre ++ k' :: post.
        Proof.
          clear. induction es.
          simpl; congruence.
          simpl. case_eq (F se a); intros.
          inversion H0. subst. do 4 eexists; intuition eauto.
          instantiate (2 := nil). reflexivity. reflexivity.

          generalize dependent H0.
          case_eq (fold_args_update es); intros.
          inversion H1; subst. eapply IHes in H0.
          do 4 destruct H0. exists (a :: x). exists x0.
          eexists; eexists; intuition; subst; eauto. reflexivity.

          congruence.
        Qed.          
      End arg.

      Variable impures : FM.t (list T).

      Fixpoint fold_known_update (k : list nat) :
        hlist (fun n : nat => match nth_error sfuncs n with
                                | None => Empty_set 
                                | Some ss => SymEval_byte ss
                              end) k
        -> option (FM.t (list T)) :=
        match k as k 
          return hlist (fun n : nat => match nth_error sfuncs n with
                                         | None => Empty_set 
                                         | Some ss => SymEval_byte ss
                                       end) k
                 -> option (FM.t (list T))
          with
          | nil => fun _ => None
          | a :: b => fun ss =>
            match FM.find a impures with
              | None => fold_known_update (hlist_tl ss)
              | Some argss =>
                match nth_error sfuncs a as ss
                  return match ss with
                           | None => Empty_set 
                           | Some ss => SymEval_byte ss
                         end -> option (FM.t (list T))
                  with
                  | Some _ => fun se =>
                    match fold_args_update se argss with
                      | None => fold_known_update (hlist_tl ss)
                      | Some r => Some (FM.add a r impures) (* this is a replace *)
                    end
                  | None => fun err => match err with end
                end (hlist_hd ss)
            end
        end.
      
      Theorem fold_known_update_correct : forall k
        (h : hlist (fun n : nat => match nth_error sfuncs n with
                                     | None => Empty_set 
                                     | Some ss => SymEval_byte ss
                                   end) k) i',
        @fold_known_update k h = Some i' ->
        exists n, exists ss,
          exists se : SymEval_byte ss, exists ls, exists ls',
               nth_error sfuncs n = Some ss 
            /\ FM.find n impures = Some ls 
            /\ fold_args_update se ls = Some ls'
            /\ i' = FM.add n ls' impures.
      Proof.
        induction k; simpl.
          congruence.
          intros h v. specialize (IHk (hlist_tl h) v).
          rewrite (hlist_eta _ h) in *.
          generalize dependent (hlist_hd h). simpl.
          case_eq (FM.find a impures); intros; eauto 10.

          assert (exists k, nth_error sfuncs a = Some k).
          generalize y. clear.
          destruct (nth_error sfuncs a); [ eauto | destruct 1 ]. 
          destruct H1.
          generalize dependent y.
          rewrite H1. intro.
          case_eq (fold_args_update y l); intros; eauto 10.
          inversion H2; subst.
          eauto 10.
      Qed.
    End search_write.

    Definition symeval_write_byte (hyps : list (expr types)) (p v : expr types) 
      (s : SHeap types (tvType pcIndex) (tvType stateIndex))
      : option (SHeap types (tvType pcIndex) (tvType stateIndex)) :=
      let hyps := hyps ++ pures s in
      let writer _ seb args := 
        sym_write_byte seb hyps args p v
      in
      match fold_known_update writer (impures s) evals with
        | None => None
        | Some i' => Some {| impures := i' ; pures := pures s ; other := other s |}
      end.

    Theorem symeval_write_byte_correct : forall cs stn hyps funcs pe ve s s' uvars vars (m : B.mem),
      symeval_write_byte hyps pe ve s = Some s' ->
      AllProvable funcs uvars vars hyps ->
      (exists sm, 
           ST.satisfies cs (sexprD funcs sfuncs (sheapD s) uvars vars) stn sm
        /\ ST.HT.satisfies sm m) ->
      match exprD_ptr funcs uvars vars pe , exprD_byte funcs uvars vars ve with
        | Some p , Some v =>
          exists sm, 
             ST.satisfies cs (sexprD funcs sfuncs (sheapD s') uvars vars) stn sm
          /\ ST.HT.satisfies sm (B.mem_set m p v)
        | _ , _ => False
      end.
    Proof.
    Admitted.

  End typed.
End Evaluator.


(*
    Lemma wordType_get : tvarD types (tvType wordIndex) = W.
      unfold types. 
    Admitted.

    Definition exprD_word (funcs : functions types) (uvars vars : env types) (e : expr types) : 
      option W :=
      match wordType_get in _ = t return option t with
        | refl_equal =>
          @exprD types funcs uvars vars e (tvType wordIndex)
      end.




    Record SymEval (Predicate : ssignature types (tvType pcIndex) (tvType stateIndex)) : Type :=
    { sym_read_word  : 
      forall (hyps args : list (expr types)) (p : expr types), option (expr types)
    ; sym_write_word : 
      forall (hyps args : list (expr types)) (p v : expr types),
        option (list (expr types))
    ; sym_read_word_correct : forall funcs args uvars vars cs hyps pe ve m s,
      sym_read_word hyps args pe = Some ve ->
      AllProvable funcs nil nil  hyps ->
      match 
        applyD (@exprD _ funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate)
        with
        | None => False
        | Some p => ST.satisfies cs p s m
      end ->
      match exprD_ptr uvars vars pe , exprD_word uvars vars ve with
        | Some p , Some v =>
          smem_get p m = Some v
        | _ , _ => False
      end
(*
    ; sym_write_correct : forall funcs args uvars vars P cs hyps pe ve v m s args',
      sym_write hyps args pe ve = Some args' ->
      hlist (FalseDefault funcs) hyps ->
      exprD funcs uvars vars ve pcType = Some v ->
      match applyD (@exprD types funcs uvars vars) (SDomain Predicate) args _ (SDenotation Predicate) with
        | None => False
        | Some p => ST.satisfies (ST.star p P) cs s m
      end ->
      match exprD funcs uvars vars pe pcType with
        | Some p =>
          match applyD (@exprD types funcs uvars vars) (SDomain Predicate) args' _ (SDenotation Predicate) with
            | None => False
            | Some pr => ST.satisfies (ST.star pr P) cs s (WriteWord s m p v)
          end
        | _ => False
      end
*)
    }.

    Definition defaultSymEval (P : ssignature types pcType stateType) : SymEval.
    refine (
      {| Predicate             := P
       ; sym_read_word         := fun _ _ _ => None
       ; sym_write_word        := fun _ _ _ _ => None
       ; sym_read_word_correct := _
(*       ; sym_write_correct := _ *)
       |}); 
    abstract (simpl; intros; congruence).
    Defined.

    Section evaluator.
      Fixpoint matches (sfuncs : list (ssignature types pcType stateType)) (evals : list (option SymEval)) : Prop :=
        match evals with
          | nil => True
          | e :: es =>
            match sfuncs with
              | nil => False
              | s :: ss =>
                match e with
                  | None => True
                  | Some e => Predicate e = s 
                end /\ matches ss es
            end
        end.

      Variable evals : list (option SymEval).

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

        Variable D : nat -> T -> sexpr types pcType stateType.
        Variable P : nat -> T -> tvarD types stateType -> Prop.
        Variable funcs : functions types.
        Variable sfuncs : list (ssignature types pcType stateType).

        Hypothesis imp : forall cs uv vs k v m,
             ST.satisfies (sexprD funcs sfuncs (D k v) uv vs) cs (fst m) (Mem (snd m)) 
          -> P k v m.
        Hypothesis ext : forall cs uv vs k v m,
             ST.satisfies (sexprD funcs sfuncs (D k v) uv vs) cs (fst m) (Mem (snd m)) 
          -> forall p m',
               ST.satisfies (ST.star (sexprD funcs sfuncs (D k v) uv vs) p) cs (fst m') (Mem (snd m'))
               -> P k v m'.
        Hypothesis FD : forall k v u m,
          F k v = Some u -> P k v m.

(*
        Theorem fold_find_ind : forall m, 
          fold_find 
*)
      End fold_find.

      


      Definition symeval_read (hyps : list (expr types)) (p : expr types) (s : SHeap types pcType stateType) 
        : option (expr types) :=
        let hyps := hyps ++ pures s in
        let res := 
          fold_find (fun k v => 
            match nth_error evals k with
              | Some (Some ev) =>
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

      Definition symeval_read_correct : forall hyps pe s ve,
        symeval_read hyps pe s = Some ve ->
        hlist (FalseDefault funcs) hyps ->
        forall uvars vars cs stn m,
        ST.satisfies (@sexprD types funcs pcType stateType sfuncs (SEP.sheapD s) uvars vars) cs stn m -> 
        match exprD funcs uvars vars ve pcType , exprD funcs uvars vars pe pcType with
          | Some v , Some p => ReadWord stn m p = v 
          | _ , _ => False
        end.
      Proof.
        Opaque tvarD.
        unfold symeval_read. destruct s; simpl.
        induction impures0; simpl in *.
          intros; congruence.

          intros.
          cut (ST.satisfies (sexprD funcs sfuncs (sheapD {| impures := impures0_1 ; pures := pures0 ; other := other0 |}) uvars vars0) cs stn m).
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
              
  (*
End Evaluator.
*)



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
