Set Implicit Arguments.

Require Import Facade.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Option.

  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation Value := (@Value ADTValue).
  Notation Sca := (@SCA ADTValue).

  Lemma is_true_is_false : forall (st : State) e, is_true st e -> is_false st e -> False.
  Proof.
    intros.
    unfold is_true, is_false in *.
    rewrite H in *; discriminate.
  Qed.

  Lemma safe_if_true : forall (env : Env) e t f st, Safe env (If e t f) st -> is_true st e -> Safe env t st.
  Proof.
    intros.
    inversion H; subst.
    eauto.
    exfalso; eapply is_true_is_false; eauto.
  Qed.

  Definition is_bool (st : State) e := eval_bool st e <> None.

  Definition value_dec (v : Value) : {w | v = SCA _ w} + {a | v = ADT a}.
    destruct v.
    left; exists w; eauto.
    right; exists a; eauto.
  Defined.

  Definition option_value_dec (v : option Value) : {w | v = Some (SCA _ w)} + {a | v = Some (ADT a)} + {v = None}.
    destruct (option_dec v).
    destruct s; subst.
    destruct (value_dec  x).
    destruct s; subst.
    left; left; eexists; eauto.
    destruct s; subst.
    left; right; eexists; eauto.
    subst.
    right; eauto.
  Qed.

  Lemma is_true_is_bool : forall st e, is_true st e -> is_bool st e.
  Proof.
    intros.
    unfold is_true, is_bool in *.
    rewrite H in *.
    discriminate.
  Qed.

  Lemma is_false_is_bool : forall st e, is_false st e -> is_bool st e.
  Proof.
    intros.
    unfold is_false, is_bool in *.
    rewrite H in *.
    discriminate.
  Qed.

  Lemma safe_if_is_bool : forall (env : Env) e t f st, Safe env (If e t f) st -> is_bool st e.
  Proof.
    intros.
    inversion H; subst.
    eapply is_true_is_bool; eauto.
    eapply is_false_is_bool; eauto.
  Qed.

  Lemma safe_if_false : forall (env : Env) e t f st, Safe env (If e t f) st -> is_false st e -> Safe env f st.
  Proof.
    intros.
    inversion H; subst.
    exfalso; eapply is_true_is_false; eauto.
    eauto.
  Qed.

  Require Import SyntaxExpr.

  (* test boolean deciders *)
  Open Scope string_scope.
  Require Import List.
  Import ListNotations.
  Goal is_no_dup ["aa"; "ab"; "cc"] = true. Proof. exact eq_refl. Qed.
  Goal is_no_dup ["aa"; "aa"; "cc"] = false. Proof. exact eq_refl. Qed.
  Goal is_in "bb" ["aa"; "bb"; "cc"] = true. Proof. exact eq_refl. Qed.
  Goal is_in "dd" ["aa"; "bb"; "cc"] = false. Proof. exact eq_refl. Qed.
  Goal is_disjoint ["aa"; "bb"; "cc"] ["dd"; "ee"] = true. Proof. exact eq_refl. Qed.
  Goal is_disjoint ["aa"; "bb"; "cc"] ["dd"; "ee"; "cc"] = false. Proof. exact eq_refl. Qed.
  Goal assigned (Seq (Assign "x" (Var "a")) (Label "y" ("a", "b"))) = ["x"; "y"]. Proof. exact eq_refl. Qed.
  Goal is_disjoint (assigned (Seq (Assign "x" (Var "a")) (Label "y" ("a", "b")))) ["aa"; "bb"] = true. Proof. exact eq_refl. Qed.
  Goal is_disjoint (assigned (Seq (Assign "x" (Var "a")) (Label "y" ("a", "b")))) ["aa"; "bb"; "x"] = false. Proof. exact eq_refl. Qed.

  Import StringSetFacts.
  Import StringSet.

  Lemma is_disjoint_sound ls1 ls2 : is_disjoint ls1 ls2 = true -> ListFacts1.Disjoint ls1 ls2.
  Proof.
    intros Hdisj.
    eapply inter_is_empty_iff in Hdisj.
    eapply set_disjoint_list_disjoint; eauto.
  Qed.

  Definition not_reachable key (k : key) ks ins := forall i, nth_error ks i = Some k -> exists w, nth_error ins i = Some (Sca w).

  Require Import StringMap.
  Import StringMap.
  Require Import ListFacts4.

  Lemma find_Some_add_remove_many ks : 
    forall ins outs h k v, 
      NoDup ks -> 
      length ks = length ins -> 
      length ks = length outs -> 
      (StringMap.find k (add_remove_many ks ins outs h) = Some v <-> 
       ((not_reachable k ks ins /\ StringMap.find k h = Some v) \/ 
        exists i a, 
          nth_error ks i = Some k /\ 
          nth_error ins i = Some (ADT a) /\ 
          nth_error outs i = Some (Some v))).
  Proof.
    induction ks; destruct ins; destruct outs; simpl in *; try solve [intros; discriminate].
    intros h k v Hnd Hlkin Hlkout.
    split.
    intros Hf.
    left.
    split.
    Lemma no_reachable_nil key (k : key) : not_reachable k [] [].
    Proof.
      unfold not_reachable; intros; rewrite nth_error_nil in *; discriminate.
    Qed.
    eapply no_reachable_nil.
    eauto.
    intros H.
    openhyp.
    eauto.
    rewrite nth_error_nil in *; discriminate.    

    Lemma not_reachable_cons_sca key (k : key) ks ins k' w : not_reachable k' ks ins -> not_reachable k' (k :: ks) (SCA ADTValue w :: ins).
    Proof.
      unfold not_reachable; intros Hnr.
      intros i Hk'.
      destruct i as [|i]; simpl in *.
      inject Hk'.
      exists w; eauto.
      eapply Hnr in Hk'.
      eauto.
    Qed.

    Lemma not_reachable_cons_neq key (k : key) ks ins k' v : not_reachable k' ks ins -> k' <> k -> not_reachable k' (k :: ks) (v :: ins).
    Proof.
      unfold not_reachable; intros Hnr Hne.
      intros i Hk'.
      destruct i as [|i]; simpl in *.
      inject Hk'.
      intuition.
      eapply Hnr in Hk'.
      eauto.
    Qed.

    rename a into k.
    intros h k' v' Hnd Hlkin Hlkout.
    inject Hlkin.
    inject Hlkout.
    inversion Hnd; subst.
    split.
    intros Hf.
    destruct v as [w | a].
    eapply IHks in Hf; eauto.
    destruct Hf as [[Hnr Hfk'] | [i [a [Hk' [Hin Hout]]]]].
    left.
    split.
    solve [eapply not_reachable_cons_sca; eauto].
    eauto.
    right.
    solve [exists (S i), a; eauto].

    destruct o as [ao |].
    eapply IHks in Hf; eauto.
    destruct Hf as [[Hnr Hfk'] | [i [a' [Hk' [Hin Hout]]]]].
    destruct (string_dec k' k) as [Heq | Hne].
    subst.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    inject Hfk'.
    right.
    solve [exists 0, a; eauto].
    rewrite StringMapFacts.add_neq_o in * by eauto.
    left.
    split.
    solve [eapply not_reachable_cons_neq; eauto].
    eauto.
    right.
    solve [exists (S i), a'; eauto].

    eapply IHks in Hf; eauto.
    destruct Hf as [[Hnr Hfk'] | [i [a' [Hk' [Hin Hout]]]]].
    destruct (string_dec k' k) as [Heq | Hne].
    subst.
    rewrite StringMapFacts.remove_eq_o in * by eauto.
    discriminate.
    rewrite StringMapFacts.remove_neq_o in * by eauto.
    left.
    split.
    solve [eapply not_reachable_cons_neq; eauto].
    eauto.
    right.
    solve [exists (S i), a'; eauto].

    Lemma not_reachable_cons_elim key (k : key) ks v vs k' : not_reachable k' (k :: ks) (v :: vs) -> not_reachable k' ks vs.
    Proof.
      unfold not_reachable; intros Hnr.
      intros i Hk'.
      specialize (Hnr (S i)); simpl in *.
      eauto.
    Qed.
    Lemma not_not_reachable key (k : key) ks a ins : ~ not_reachable k (k :: ks) (ADT a :: ins).
    Proof.
      unfold not_reachable.
      nintro.
      specialize (H 0); simpl in *.
      edestruct H; eauto.
      discriminate.
    Qed.

    intros Hor.
    destruct Hor as [[Hnr Hfk'] | [i [a [Hk' [Hin Hout]]]]].
    destruct v as [w | a].
    eapply IHks; eauto.
    left.
    split.
    solve [eapply not_reachable_cons_elim; eauto].
    eauto.
    destruct o as [ao|].
    eapply IHks; eauto.
    destruct (string_dec k' k) as [Heq | Hne].
    subst.
    solve [contradict Hnr; eapply not_not_reachable].
    rewrite StringMapFacts.add_neq_o in * by eauto.
    left.
    split.
    solve [eapply not_reachable_cons_elim; eauto].
    eauto.
    eapply IHks; eauto.
    destruct (string_dec k' k) as [Heq | Hne].
    subst.
    solve [contradict Hnr; eapply not_not_reachable].
    rewrite StringMapFacts.remove_neq_o in * by eauto.
    left.
    split.
    solve [eapply not_reachable_cons_elim; eauto].
    eauto.

    eapply IHks; eauto.
    destruct i as [|i]; simpl in *.
    inject Hk'.
    inject Hin.
    inject Hout.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    left.
    split.
    Lemma not_in_not_reachable key (k : key) ks ins : ~ List.In k ks -> not_reachable k ks ins.
    Proof.
      unfold not_reachable; intros Hni.
      intros i Hk.
      contradict Hni.
      eapply Locals.nth_error_In; eauto.
    Qed.
    solve [eapply not_in_not_reachable; eauto].
    eauto.
    solve [right; exists i, a; eauto].
  Qed.


End ADTValue.  
