Require Import Facade.
Require Import Memory.
Require Import Ensembles.

Inductive FacadeADT :=
  | List : list W -> FacadeADT
  | Junk : False -> FacadeADT
  | FEnsemble : Ensemble W -> FacadeADT.

Require Import List Program.

Definition SCAZero {t} := SCA t (Word.natToWord 32 0).
Definition SCAOne  {t} := SCA t (Word.natToWord 32 1).

Ltac crush_types :=
  unfold type_conforming, same_types, same_type; intros;
  repeat match goal with
           | [ H: exists t, _ |- _ ] => destruct H
         end; subst;
  intuition.

Section ListADTSpec.

  Definition List_new : AxiomaticSpec FacadeADT.
    refine {|
        PreCond := fun args => args = [];
        PostCond := fun args ret => args = [] /\ ret = ADT (List [])
      |}; crush_types.
  Defined.

  Definition List_delete : AxiomaticSpec FacadeADT.
    refine {|
        PreCond := fun args => exists l, args = [ADT (List l)];
        PostCond := fun args ret => exists l, args = [(ADT (List l), None)] /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition List_pop : AxiomaticSpec FacadeADT.
    refine {|
        PreCond := fun args =>
                     exists h t,
                       args = [ADT (List (h :: t))];
        PostCond := fun args ret =>
                      exists h t,
                        args = [ (ADT (List (h :: t)), Some (List t)) ] /\
                        ret = SCA FacadeADT h
      |}; crush_types.
  Defined.

  Definition List_empty : AxiomaticSpec FacadeADT.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (List l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [(ADT (List l), Some (List l))] /\
                        ((ret = SCAZero /\ l <> nil) \/ (ret = SCAOne /\ l = nil))
      |}; crush_types.
  Defined.

  Definition List_push : AxiomaticSpec FacadeADT.
    refine {|
        PreCond := fun args =>
                     exists l w,
                       args = [ADT (List l); SCA _ w];
        PostCond := fun args ret =>
                      exists l w,
                        args = [ (ADT (List l), Some (List (w :: l))); (SCA _ w, None) ] /\
                        ret = SCAZero
      |}; crush_types.
  Defined.

  Definition List_copy : AxiomaticSpec FacadeADT.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (List l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (List l), Some (List l)) ] /\
                        ret = ADT (List l)
      |}; crush_types.
  Defined.

End ListADTSpec.

Section FiniteSetADTSpec.

(* Def Constructor sEmpty (_ : unit) : rep := ret (Empty_set _), *)
  Definition FEnsemble_sEmpty : AxiomaticSpec FacadeADT.
    refine {|
        PreCond := fun args =>
                     args = [];
        PostCond := fun args ret =>
                      args = []
                      /\ ret = ADT (FEnsemble (Empty_set _))
      |}; crush_types.
  Defined.

  (* Def Method sAdd (s : rep , w : W) : unit :=
      ret (Add _ s w, tt) *)
  Definition FEnsemble_sAdd : AxiomaticSpec FacadeADT.
    refine {|
        PreCond := fun args =>
                     exists s w, args = [ADT (FEnsemble s); SCA _ w];
        PostCond := fun args ret =>
                      exists s w, args = [(ADT (FEnsemble s), Some (FEnsemble (Add _ s w)));
                                           (SCA _ w, None)]
                                  /\ ret = SCAZero
      |}; crush_types.
  Defined.

  (* Def Method sRemove (s : rep , w : W) : unit :=
      ret (Subtract _ s w, tt) *)
  Definition FEnsemble_sRemove : AxiomaticSpec FacadeADT.
    refine {|
        PreCond := fun args =>
                     exists s w, args = [ADT (FEnsemble s); SCA _ w];
        PostCond := fun args ret =>
                      exists s w, args = [(ADT (FEnsemble s), Some (FEnsemble (Subtract _ s w)));
                                           (SCA _ w, None)]
                                  /\ ret = SCAZero
      |}; crush_types.
  Defined.

  (* Def Method sIn (s : rep , w : W) : bool :=
        (b <- { b : bool | b = true <-> Ensembles.In _ s w };
         ret (s, b)) *)
  Definition FEnsemble_sIn : AxiomaticSpec FacadeADT.
    refine {|
        PreCond := fun args =>
                     exists s w, args = [ADT (FEnsemble s); SCA _ w];
        PostCond := fun args ret =>
                      exists s w, args = [(ADT (FEnsemble s), Some (FEnsemble s));
                                         (SCA _ w, None)]
                                  /\ (ret = SCAZero <-> Ensembles.In _ s w)
                                  /\ (ret = SCAOne <-> ~ Ensembles.In _ s w)
      |}; crush_types.
  Defined.

  (* These definitions should be imported *)
  Definition EnsembleListEquivalence
             {A}
             (ensemble : Ensemble A)
             (seq : list A) :=
    NoDup seq /\
    forall x, Ensembles.In _ ensemble x <-> List.In x seq.

  Definition cardinal U (A : Ensemble U) (n : nat) : Prop :=
    exists ls, EnsembleListEquivalence A ls /\ Datatypes.length ls = n.

  (* Def Method sSize (s : rep , _ : unit) : nat :=
          (n <- { n : nat | cardinal _ s n };
           ret (s, n)) *)
  Definition FEnsemble_sSize : AxiomaticSpec FacadeADT.
        refine {|
        PreCond := fun args =>
                     exists s, args = [ADT (FEnsemble s)];
        PostCond := fun args ret =>
                      exists s n, args = [(ADT (FEnsemble s), Some (FEnsemble s))]
                                  /\ cardinal _ s n
                                  /\ ret = SCA _ (Word.natToWord 32 n)
          |}; crush_types.
  Defined.

(* (* Specification of state after running sEmpty. *)
Lemma runsto_sEmpty
: forall (x_label : StringMap.key)
         (env : Env FacadeADT)
         (st st' : State FacadeADT)
         (sEmpty_pointer : W),
    Word2Spec env sEmpty_pointer = Some (Axiomatic FEnsemble_sEmpty) ->
    RunsTo env (Call x_label sEmpty_pointer nil) st st' ->
    StringMap.Equal st' (StringMap.add x_label (AxSpec.ADT (FEnsemble (Empty_set _))) st).
Proof.
  intros * sEmpty_Pointer_is_sEmpty runs_to.
  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  rewrite sEmpty_Pointer_is_sEmpty in *; autoinj.
  unfold FEnsemble_sEmpty in *; simpl in *; autodestruct; subst; eauto.
Qed.

(* Specification of state after running sAdd. *)
Lemma runsto_sAdd
: forall (s_model : Ensemble W)
         (w_label : StringMap.key)
         (w_value : W)
         (s_label : StringMap.key)
         (x_label : StringMap.key)
         (env : Env FacadeADT)
         (st st' : State FacadeADT)
         (sAdd_pointer : W),
    s_label <> x_label ->
    st [s_label >> AxSpec.ADT (FEnsemble s_model)] ->
    st [w_label >> SCA _ w_value] ->
    Word2Spec env sAdd_pointer  = Some (Axiomatic FEnsemble_sAdd) ->
    RunsTo env (Call x_label sAdd_pointer (s_label :: w_label :: nil)) st st' ->
    StringMap.Equal st'
                    (StringMap.add x_label SCAZero
                                   (StringMap.add s_label (AxSpec.ADT (FEnsemble (Add _ s_model w_value))) st)).
Proof.
  intros * label_neq s_init w_init sAdd_Pointer_is_sAdd runs_to.
  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  rewrite sAdd_Pointer_is_sAdd in *; autoinj.
  unfold FEnsemble_sAdd in *; clear sAdd_Pointer_is_sAdd; simpl in *;
  autodestruct; subst;
  rewrite StringMapFacts.find_mapsto_iff in * |- ;
  unfold sel in *.

  subst_find; simpl in *; setoid_rewrite w_init in H5; simpl in *; (* subst_find doesn't work on w_label *)
  autoinj.

  destruct output; [congruence|].
  destruct output; [congruence|].
  simpl in *; autoinj.
Qed.

(* Specification of state after running sRemove. *)
Lemma runsto_sRemove
: forall (s_model : Ensemble W)
         (w_label : StringMap.key)
         (w_value : W)
         (s_label : StringMap.key)
         (x_label : StringMap.key)
         (env : Env FacadeADT)
         (st st' : State FacadeADT)
         (sRemove_pointer : W),
    s_label <> x_label ->
    st [s_label >> AxSpec.ADT (FEnsemble s_model)] ->
    st [w_label >> SCA _ w_value] ->
    Word2Spec env sRemove_pointer  = Some (Axiomatic FEnsemble_sRemove) ->
    RunsTo env (Call x_label sRemove_pointer (s_label :: w_label :: nil)) st st' ->
    StringMap.Equal st'
                    (StringMap.add x_label SCAZero
                                   (StringMap.add s_label (AxSpec.ADT (FEnsemble (Subtract _ s_model w_value))) st)).
Proof.
  intros * label_neq s_init w_init sRemove_Pointer_is_sRemove runs_to.
  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  rewrite sRemove_Pointer_is_sRemove in *; autoinj.
  unfold FEnsemble_sRemove in *; clear sRemove_Pointer_is_sRemove; simpl in *;
  autodestruct; subst;
  rewrite StringMapFacts.find_mapsto_iff in * |- ;
  unfold sel in *.

  subst_find; simpl in *; setoid_rewrite w_init in H5; simpl in *; (* subst_find doesn't work on w_label *)
  autoinj.

  destruct output; [congruence|].
  destruct output; [congruence|].
  simpl in *; autoinj.
Qed.

(* Specification of state after running sIn. *)
Lemma runsto_sIn
: forall (s_model : Ensemble W)
         (w_label : StringMap.key)
         (w_value : W)
         (s_label : StringMap.key)
         (x_label : StringMap.key)
         (env : Env FacadeADT)
         (st st' : State FacadeADT)
         (sIn_pointer : W),
    s_label <> x_label ->
    st [s_label >> AxSpec.ADT (FEnsemble s_model)] ->
    st [w_label >> SCA _ w_value] ->
    Word2Spec env sIn_pointer  = Some (Axiomatic FEnsemble_sIn) ->
    RunsTo env (Call x_label sIn_pointer (s_label :: w_label :: nil)) st st' ->
    exists ret,
      (ret = SCAZero <-> Ensembles.In _ s_model w_value)
      /\ (ret = SCAOne <-> ~ Ensembles.In _ s_model w_value)
      /\ StringMap.Equal st'
                    (StringMap.add x_label ret
                                   (StringMap.add s_label (AxSpec.ADT (FEnsemble s_model)) st)).
Proof.
  intros * label_neq s_init w_init sIn_Pointer_is_sIn runs_to.
  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  rewrite sIn_Pointer_is_sIn in *; autoinj.
  unfold FEnsemble_sIn in *; clear sIn_Pointer_is_sIn; simpl in *;
  autodestruct; subst;
  rewrite StringMapFacts.find_mapsto_iff in * |- ;
  unfold sel in *.

  subst_find; simpl in *; setoid_rewrite w_init in H5; simpl in *; (* subst_find doesn't work on w_label *)
  autoinj.

  destruct output; [congruence|].
  destruct output; [congruence|].

  simpl in *; autoinj; eauto.
Qed.

Arguments natToWord : simpl never. (* simplifying natToWord causes crazy slowdown. *)

(* Specification of state after running sSize. *)
Lemma runsto_sSize
: forall (s_model : Ensemble W)
         (s_label : StringMap.key)
         (x_label : StringMap.key)
         (env : Env FacadeADT)
         (st st' : State FacadeADT)
         (sSize_pointer : W),
    s_label <> x_label ->
    st [s_label >> AxSpec.ADT (FEnsemble s_model)] ->
    Word2Spec env sSize_pointer  = Some (Axiomatic FEnsemble_sSize) ->
    RunsTo env (Call x_label sSize_pointer (s_label :: nil)) st st' ->
    exists ret n,
      cardinal _ s_model n
      /\ ret = SCA _ (Word.natToWord 32 n)
      /\ StringMap.Equal st'
                         (StringMap.add x_label ret
                                        (StringMap.add s_label (AxSpec.ADT (FEnsemble s_model)) st)).
Proof.
  intros * label_neq s_init sSize_Pointer_is_sSize runs_to.
  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  rewrite sSize_Pointer_is_sSize in *; autoinj.
  unfold FEnsemble_sSize in *; clear sSize_Pointer_is_sSize; simpl in *;
  autodestruct; subst;
  rewrite StringMapFacts.find_mapsto_iff in * |- ;
  unfold sel in *.

  subst_find; simpl in *; autoinj.

  destruct output; [congruence|].
  simpl in *; autoinj; eauto.
Qed.

Lemma compile_sAdd {retvar} u :
  forall (FiniteSetImpl : FullySharpened FiniteSetSpec),
  forall sAdd_Pointer tdummy thead ttail,
  forall env,
  forall (precond intercond postcond: State _ -> Prop),
    Word2Spec env sAdd_Pointer = Some (Axiomatic FEnsemble_sAdd) ->
    cond_respects_MapEq postcond ->
    cond_indep postcond tdummy ->
    refine {prog | forall init_state final_state impl_rep,
                     precond init_state ->
                     init_state[s_label >> AxSpec.ADT (Ensemble s_model)] ->
                     init_state[w_label >> st [w_label >> SCA _ w_value]] ->
                     AbsR (projT2 FiniteSetImpl) s_model impl_rep ->
                     RunsTo env prog init_state final_state ->
                     final_state[vret >> wrapper (List.fold_left f seq init)]
                     (CallMethod (projT1 impl) sAdd impl_rep u)
                     final_state[s_label >> AxSpec.ADT (AxSpec.ADT (FEnsemble (Add _ s_model w_value)))]
                     (StringMap.MapsTo retvar (wrapper (if test then truecase else falsecase)) final_state
                      /\ postcond final_state)}


                     final_state[ttail >> AxSpec.ADT (List (head :: tail))]
    /\ postcond final_state}
(s_exp <- {s_exp | forall init_state inter_state,
                       precond init_state ->
                       RunsTo env s_exp init_state inter_state ->
                       inter_state[s_label >> AxSpec.SCA _ s_model] /\
                       intercond inter_state};
 (w_exp <- {w_exp | forall inter_state final_state,
                      intercond init_state ->
                      RunsTo env s_exp inter_state final_state ->
                      final_state[w_label >> AxSpec.SCA _ w_value] /\
                      postcond final_state};
 (Seq s_exp (Seq w_exp (Call tdummy sAdd_Pointer (s_label :: w_label :: nil)))).

(CallMethod (projT1 impl) sSize)
*)

End FiniteSetADTSpec.
