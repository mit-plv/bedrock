Require Import AutoSep Wrap Arith.
Require Import GeneralTactics.
Set Implicit Arguments. 

(* Some inequalitites *)

Lemma max_le_Sr: forall a b, (b <= max a (S b))%nat.
  intros.
  assert (S b <= max a (S b))%nat by (eapply Max.le_max_r).
  omega.
Qed.
Lemma max_le_l: forall a b, (a <= max a (S b))%nat.
  intros.
  eapply Max.le_max_l.
Qed.
Lemma max_le_3r: forall a b c , (c + b <= c + max a (S b))%nat.
  intros.
  assert (b <= max a (S b))%nat by (eapply max_le_Sr).
  omega.
Qed.
Lemma max_le_3l: forall a b c, (c + a <= c + max a (S b))%nat.
  intros.
  assert (a <= max a (S b))%nat by (eapply max_le_l).
  omega.
Qed.
Lemma plus_max_ge: forall a b c, (a + max b (S c) > a)%nat.
  intros.
  assert ( S c <= max b (S c) )%nat by (eapply Max.le_max_r).
  omega.
Qed.
Lemma convoluted_max: forall a b c,
  (S (a + c) <= a + max b (S c))%nat.
  intros.
  assert (S c <= max b (S c))%nat by (eapply Max.le_max_r).
  omega.
Qed.

Ltac variables_ineq :=
  match goal with
    | _ => apply max_le_Sr
    | _ => apply max_le_l
    | _ => apply max_le_3r
    | _ => apply max_le_3l
    | _ => apply plus_max_ge
    | _ => apply convoluted_max
    | _ => solve [omega]
  end.

(* Probably not going to be used*)
Ltac not_trivial_eq:= 
  match goal with
    | [H: forall _, _ |- _ = _] => eapply H; eauto
  end.




Definition changedVariables vs1 vs2 vars :=
  forall x, sel vs2 x <> sel vs1 x -> In x vars.

Notation "'changed_in'" := changedVariables.

  (* Disj *)
Definition disj A l1 l2:= forall a: A, In a l1 -> ~ In a l2. 

  (*Disjoint Not used anymore. Changed to Disj*)

Notation "'disjoint'" := disj.

Section variables.
  
  (*Make a temporal variable, of length n, with n consecutive '!' and  a "."*)
  Fixpoint tempOf n:= 
    match n with
      | O => "."
      | S n' => ("!" ++ (tempOf n'))%string
    end.

  Lemma tempOf_inj: (forall n m: nat, tempOf n = tempOf m -> n = m)%nat.
    induction n; induction m; simpl; intuition.
  Qed.

  Local Hint Resolve tempOf_inj.
  
  Lemma stringGen_inj: (forall n m: nat, n > m -> tempOf n <> tempOf m)%nat.
    intuition; apply tempOf_inj in H0; omega.
  Qed.

  (* Generate list with temporal variables. Range: [offSet, offSet+length) *)
  Fixpoint tempChunk offSet length:=
    match length with
      | O => nil
      | S n' => tempChunk offSet n' ++ ((tempOf (offSet + n')) :: nil)
    end.
  
  Definition tempVars length := tempChunk 0 length.

  (* test *)
  Goal tempVars 4 = "." :: "!." :: "!!." :: "!!!." :: nil.
    auto.
  Qed.




  (* Lemmas about In. In_lemmas*) 
  (*Formerly temp_in_array_offset'*)
  Lemma temp_in_chunk' : forall n length offset, (n < length)%nat -> In (tempOf (offset + n)) (tempChunk offset length).
    induction n; induction length; simpl; intuition.
    destruct length; eapply in_or_app; intuition.
    
    destruct (le_gt_dec length (S n)); eapply in_or_app;
      [replace length with (S n) by omega | ]; intuition.
  Qed.
  (*Formerly temp_in_array_offset*)
  Lemma temp_in_chunk : forall n length offset, (offset <= n -> n < offset + length -> In (tempOf n) (tempChunk offset length))%nat.
    intros;
      replace n with (offset + (n - offset)) by omega;
        eapply temp_in_chunk';
          omega.
  Qed.
  (*Same as temp_in_chunk but a different proof*)
  Lemma temp_in_chunk_2: forall off len n, (n >= off)%nat -> (n < off + len)%nat -> In (tempOf n) (tempChunk off len).
    
    Lemma split_int: forall n m, ( n >= m)%nat -> exists l, n =m + l.
      induction m; simpl; intuition.
      exists n; auto.
      assert (n >= m)%nat by omega.
      generalize H0; intro H1.
      eapply IHm in H0; destruct H0.
      destruct x; intuition.
      exists x; omega.
    Qed.
    intros.
    eapply split_int in H; destruct H.
    rewrite H in *.
    assert (x < len)%nat by omega.
    eapply temp_in_chunk'; eauto.
  Qed.
  Lemma temp_in_array: forall m n, (n > m)%nat -> In (tempOf m) (tempVars n).
    intros. eapply temp_in_chunk; auto.
  Qed.
  

  Lemma temp_in_chunk_offset : forall length offset a, In a (tempChunk offset length) -> exists n, (n < length)%nat /\ a = tempOf (offset + n).
    induction length; simpl; intuition.
    destruct (string_dec a (tempOf (offset + length))).
    exists length; intuition.
    destruct (IHlength offset a).
    eapply in_app_or in H.
    destruct H.
    eauto.
    destruct H.
    intuition.
    intuition.
    exists x; intuition.
  Qed.
  (*Formerly tempChunk_in_array_back*)
  Lemma temp_in_chunk_back: forall l m a, In a (tempChunk m l) ->  exists n, (m <= n)%nat /\ (n < m + l)%nat /\ a = tempOf n.
    intros.
    eapply temp_in_chunk_offset in H.
    destruct H; intuition.
    exists (m + x); intuition.
  Qed.

  Lemma temp_in_array_back: forall n a, In a (tempVars n) ->  exists m, (n > m)%nat /\ a = tempOf m.
    intros.
    eapply temp_in_chunk_back in H.
    destruct H; intuition.
    exists x; intuition.
  Qed.

  Lemma In_tempVars_tran: forall s n m, (m <= n)%nat -> In s (tempVars m) -> In s (tempVars n).
    intros. eapply temp_in_array_back in H0; destruct H0; destruct H0.
    rewrite H1.
    eapply temp_in_array; omega.
  Qed.

  (** Not In. not_In_lemmmas**)
  (*Formerly temps_in_array*)
  Lemma temps_not_in_array: forall n m length, (n > m)%nat -> ~ In (tempOf m) (tempChunk n length).
    intuition.
    eapply temp_in_chunk_back in H0.
    destruct H0; intuition.
    apply tempOf_inj in H3.
    omega.
  Qed.
  
  Lemma in_tran_not: forall A (s: A) l1 l2, incl l1 l2 -> ~ In s l2 -> ~ In s l1.    intuition.
  Qed.


  Lemma tempVars_incl_chunkVars: forall s l m n, In s (tempChunk m l) -> (m + l <= n)%nat -> In s (tempVars n).
    intros. eapply temp_in_chunk_back in H. 
    destruct H. destruct H. destruct H1.
    rewrite H2.
    eapply temp_in_array. omega.
  Qed.
  Lemma chunk_union:  forall m n b s,
    In s (tempChunk (S b) m) \/
    In s (tempChunk b n) ->
    In s (tempChunk b (max n (S m))).
    intros.
    destruct H.
    eapply temp_in_chunk_back in H.
    destruct H; intuition.
    rewrite H2.
    eapply temp_in_chunk.
    omega.
    replace (S b + x) with (b + S x).
    assert (x < b + S m)%nat by omega.
    assert (S m <= max n (S m))%nat by (eapply Max.le_max_r).
    omega.
    omega.
    eapply temp_in_chunk_back in H.
    destruct H; intuition.
    rewrite H2.
    eapply temp_in_chunk.
    omega.
    assert (n <= max n (S m))%nat by (eapply Max.le_max_l).
    omega.
  Qed.

  (* End In*)

  (* Lemmas about incl. incl_lemmas*)
  
  Lemma nothingInNil: forall A (a: list A), incl a nil -> a = nil.
    unfold incl. intros; destruct a; intuition.
    assert (In a nil).
    eapply H; simpl; intuition.
    unfold In in H0; intuition.
  Qed.
  Lemma incl_app_backl: forall A (l m n: list A), incl (n ++ m) l -> incl n l.
    unfold incl; intuition.
  Qed.
  Lemma incl_app_backr: forall A (l m n: list A), incl (n ++ m) l -> incl m l.
    unfold incl;intuition.
  Qed.
  Lemma cons_app : forall A ls (a : A), a :: ls = (a :: nil) ++ ls.
    induction ls; simpl; intuition.
  Qed.
  Lemma incl_cons_back : forall A (a : A) ls1 ls2, incl (a :: ls1) ls2 -> incl ls1 ls2.
    intros; rewrite cons_app in *; eapply incl_app_backr; eauto.
  Qed.
  Lemma incl_cons_l : forall A vars (e : A), incl (e :: nil) (e :: vars).
    unfold incl; simpl; intuition.
  Qed.
  Lemma incl_cons_r : forall A vars (e : A), incl vars (e :: vars).
    induction vars; simpl; intuition.
  Qed.
  Lemma incl_app_left: forall A (l1 l2: list A), incl l1 (l1++l2).
    induction l1; induction l2; simpl; intuition.
  Qed.
  Lemma incl_tempChunk: forall b n m, (m >= b +n)%nat -> incl (tempChunk n b) (tempVars m).
    unfold incl; intros.
    eapply tempVars_incl_chunkVars; eauto.
  Qed.
  Lemma incl_app_right: forall A (l1 l2: list A), incl l2 (l1++l2).
    induction l1; induction l2; simpl; intuition.
  Qed.
  Lemma incl_nil : forall A a, incl (@nil A) a.
    unfold incl; intuition.
  Qed.
  Lemma incl_tran2: forall A (v1 v2 v3: list A), 
    incl v1 v3 -> incl v2 v1 -> incl v2 v3.
    unfold incl. intros.
    eapply H; eapply H0; eauto.
  Qed.
  Lemma incl_chunk: forall k l m n, (m <= k)%nat -> (k + l <= m + n )%nat ->
    incl (tempChunk k l) (tempChunk m n).
    unfold incl; intuition.
    eapply temp_in_chunk_offset in H1; repeat openHyp.
    rewriter'.
    eapply temp_in_chunk; omega.
  Qed. 
  Lemma incl_array: forall n m, (m <= n)%nat -> incl (tempVars m) (tempVars n).
    unfold incl; intros. eapply In_tempVars_tran; eauto.
  Qed.

  
  Lemma incl_tempChunk': forall n m a b, (a >= b)%nat-> (b + m >= a + n)%nat -> incl (tempChunk a n) (tempChunk b m).
    unfold incl; intros.
    eapply temp_in_chunk_back in H1. 
    destruct H1. destruct H1. destruct H2.
    rewrite H3 in *.
    apply temp_in_chunk; try omega.
  Qed.

  Lemma incl_tvc_l: forall d1 d2 b, incl (tempChunk b d1)
    (tempChunk b (max d1 (S d2))).
    unfold incl; intros.
    eapply temp_in_chunk_back in H.
    destruct H. destruct H. destruct H0.
    rewrite H1 in *; clear H1.
    assert (d1 <= max d1 (S d2))%nat by (apply Max.le_max_l).
    apply temp_in_chunk; try omega. 
  Qed.

  Lemma tvc_S_shift: forall a b, incl (tempChunk (S b) a) (tempChunk b (S a)).
    unfold incl; intros.
    eapply temp_in_chunk_back in H.
    destruct H. destruct H. destruct H0.
    rewrite H1 in *; clear H1.
    apply temp_in_chunk; try omega.
  Qed.
  Lemma incl_tvc_r: forall d1 d2 b, incl (tempChunk b (S d2))
    (tempChunk b (max d1 (S d2))).
    unfold incl; intros.
    eapply temp_in_chunk_back in H.
    destruct H. destruct H. destruct H0.
    rewrite H1 in *; clear H1.
    assert (S d2 <= max d1 (S d2))%nat by (apply Max.le_max_r).
    apply temp_in_chunk; try omega. 
  Qed.


  (*End incl*)

  
  (* Lemmas about sel. sel_lemmas*)

  Lemma changed_in_inv: forall vs1 vs2 vars, 
    changedVariables vs1 vs2 vars -> forall s, ~ In s vars -> sel vs2 s = sel vs1 s.
    intros.
    destruct (weq  (sel vs2 s) (sel vs1 s)); intuition.
  Qed.

  Hint Resolve changed_in_inv.

  Lemma eval_changed_vars: forall vs1 vs2 s vars, 
    changedVariables vs1 vs2 vars -> ~ In s vars -> sel vs2 s = sel vs1 s.  
    eauto.
  Qed.
  

  Lemma merge_unfold : forall ns' nm vs vs', merge vs vs' (nm :: ns') = upd (merge vs vs' ns') nm (sel vs nm).
    auto.
  Qed.
  
  Lemma sel_merge_outside : forall domain vs vs' s, ~ In s domain -> sel (merge vs vs' domain) s = sel vs' s.
    induction domain; simpl; intuition.
    rewrite merge_unfold.
    rewrite sel_upd_ne; eauto.
  Qed.
  (* End sel*)


  (* Lemmas about Change. changed_lemmas*)
  Lemma nillChange: forall vs, changedVariables vs vs nil.
    unfold changedVariables; intros; tauto.
  Qed.
  Lemma noChange: forall vs vars, changedVariables vs vs vars.
    unfold changedVariables; intros; tauto.
  Qed.

  
  Lemma changedVariables_symm : forall vs1 vs2 vars,
    changedVariables vs1 vs2 vars ->
    changedVariables vs2 vs1 vars.
    unfold changedVariables; eauto.
  Qed.

  Lemma changedVariables_upd_fwd : forall vs var value, 
    changedVariables vs (upd vs var value) (var :: nil).
    unfold changedVariables; intros.
    destruct (string_dec x var).
    simpl; intuition.
    rewrite sel_upd_ne in H; eauto.
    simpl; intuition.
  Qed.

  Lemma changedVariables_upd_bwd : forall vs var value, 
    changedVariables (upd vs var value) vs (var :: nil).
    unfold changedVariables; intros.
    destruct (string_dec x var).
    simpl; intuition.
    rewrite sel_upd_ne in H; eauto.
    simpl; intuition.
  Qed.
  Lemma changedVariables_trans : forall vs1 vs2 vs3 a b c, 
    changedVariables vs1 vs2 a -> 
    changedVariables vs2 vs3 b ->
    incl a c ->
    incl b c ->
    changedVariables vs1 vs3 c.
    unfold changedVariables; intros.
    destruct (weq (sel vs2 x) (sel vs1 x)); eauto.
    destruct (weq (sel vs3 x) (sel vs2 x)); eauto.
    contradict H3.
    congruence.
  Qed.

  Lemma changedVariables_incl : forall vs vs' vars vars', 
    changedVariables vs vs' vars -> 
    incl vars vars' -> 
    changedVariables vs vs' vars'.
    unfold changedVariables; intros.
    intuition.
  Qed.

  Lemma changedVariables_upd : forall vs1 vs2 changed s value, 
    changedVariables vs1 vs2 changed -> 
    changedVariables vs1 (upd vs2 s value) (s :: changed).
    intros.
    eapply changedVariables_trans.
    eauto.
    eapply changedVariables_upd_fwd.
    intuition.
    eapply incl_cons_l.
  Qed.

  Lemma changedVariables_upd' : forall vs1 vs2 changed s value, 
    changedVariables vs1 vs2 changed -> 
    In s changed ->
    changedVariables vs1 (upd vs2 s value) (changed).
    intros.
    eapply changedVariables_trans.
    eauto.
    eapply changedVariables_upd_fwd.
    intuition.
    unfold incl; intros.
    unfold In in H1.
    intuition.
  Qed.

  Lemma ChangeVar_tran': forall v1 v2 v3 l1 l2 l3 v v', 
    changedVariables v1 (upd v2 v v') l1 ->
    changedVariables v2 v3 l2 ->
    incl l1 l3 ->
    incl l2 l3 ->
    In v l3 ->
    changedVariables v1 v3 l3.
    intros.
    eapply changedVariables_trans.
    eauto.
    instantiate (1 := l3).
    eapply changedVariables_trans.
    eapply changedVariables_upd_bwd.
    eauto.
    eapply List.incl_cons; eauto.
    eapply incl_nil.
    eauto.
    eauto.
    eapply incl_refl.
  Qed.

  Lemma ChangeVar_tran: forall v1 v2 v3 l1 l2 l3 v v', 
    changedVariables v1 (upd v2 v v') l1 ->
    changedVariables v2 v3 l2 ->
    (forall s, s = v \/ In s l1 \/ In s l2 -> In s l3) ->
    changedVariables v1 v3 l3.
    intros.
    eapply ChangeVar_tran'.
    eauto.
    eauto.
    unfold incl; intuition.
    unfold incl; intuition.
    intuition.
  Qed.
  
  Lemma upd_changeVariables: forall vs1 vs2 var val l1 l2, In var l2 -> incl l1 l2-> changedVariables (upd vs1 var val) vs2 l1 -> changedVariables vs1 vs2 l2.
    intros.
    unfold changedVariables; unfold incl; intros.
    destruct (string_dec x var).
    rewrite e; auto.
    apply H0.
    apply H1.
    unfold not.
    unfold sel.
    unfold upd.
    rewrite string_eq_false; auto.
  Qed.
  Lemma cv_tran: forall vs1 vs2 vs3 ls1 ls2 ls3, changedVariables vs1 vs2 ls1 -> changedVariables vs2 vs3 ls2 -> incl ls1 ls3 -> incl ls2 ls3 -> changedVariables vs1 vs3 ls3.
    unfold changedVariables; unfold incl; intros.
    destruct (weq (sel vs2 x) (sel vs1 x)) as [ e | e ];
      try rewrite e in *;
        intuition.
  Qed.

  Hint Resolve changedVariables_trans changedVariables_incl changedVariables_upd.
  Hint Resolve List.incl_cons incl_cons_l incl_cons_r incl_app incl_appl incl_appr incl_refl incl_array incl_tran incl_nil incl_tl.
  Lemma changed_trans : forall vs1 vs2 vs3 c, 
    changedVariables vs1 vs2 c -> 
    changedVariables vs2 vs3 c ->
    changedVariables vs1 vs3 c.
    eauto.
  Qed.

  Lemma changed_merge : forall vs1 vs2 a b,
    changed_in vs1 vs2 (a ++ b) ->
    changed_in (merge vs2 vs1 a) vs2 b.
    unfold changedVariables; intros.
    destruct (in_dec string_dec x a).
    rewrite sel_merge in H0 by eauto.
    contradict H0; eauto.
    rewrite sel_merge_outside in H0 by eauto.
    apply H in H0.
    apply in_app_or in H0.
    intuition.
  Qed.

  Lemma changed_merge_fwd : forall vs1 vs2 vars,
    changed_in vs1 (merge vs2 vs1 vars) vars.
    unfold changedVariables; intros.
    destruct (in_dec string_dec x vars).
    eauto.
    rewrite sel_merge_outside in H by eauto.
    intuition.
  Qed.

  Hint Resolve changed_merge_fwd.
  Hint Resolve changedVariables_symm.
  
  Lemma changed_merge_bwd : forall vs1 vs2 vars,
    changed_in (merge vs2 vs1 vars) vs1 vars.
    eauto.
  Qed.

  Lemma changed_in_upd_same : forall vs1 vs2 vars s val,
    changed_in vs1 vs2 vars ->
    changed_in (upd vs1 s val) (upd vs2 s val) vars.
    unfold changedVariables; intros.
    destruct (string_dec s x).
    contradict H0.
    repeat rewrite sel_upd_eq; eauto.
    apply H.
    do 2 rewrite sel_upd_ne in H0; eauto.
  Qed.
  Lemma ChangeVar_tran_: forall v1 v2 v3 l , 
    changedVariables v1 v2 l ->
    changedVariables v2 v3 l ->
    changedVariables v1 v3 l.
    unfold changedVariables; intros.
    destruct (weq (sel v3 x) (sel v2 x)); intuition.
  Qed.
  Lemma changedVariables_upd_back : forall vs1 vs2 changed s value, 
    changedVariables (upd vs1 s value) vs2 changed -> 
    In s changed ->
    changedVariables vs1 vs2 (changed).
    unfold changedVariables; intros.
    destruct (string_dec x s). rewriter'; eauto. 
    eapply H; rewrite sel_upd_ne; eauto.
  Qed.
  (*End change*)

  Lemma disjoint_symm : forall A (a : list A) b, disjoint a b -> disjoint b a.
    unfold disj; eauto.
  Qed.

  (* Lemmas about disjoint. disjoint_lemmas*)

  
  Lemma disjoint_trans_r : forall A (a : list A) b c, disjoint a b -> incl c b -> disjoint a c.
    unfold disj; eauto.
  Qed.

  Lemma disjoint_trans_lr : forall A (a : list A) b c d, disjoint a b -> incl c a -> incl d b -> disjoint c d.
    unfold disj; eauto.
  Qed.

  Lemma disjoint_nil_r : forall A (a : list A), disjoint a nil.
    firstorder.
  Qed.
  (*End Disjoint*)

  (*Lemmas about Disj *)
  Lemma disj_app_l: forall A (l1 l2 l3: list A), disj (l1 ++ l2) l3 -> disj l1 l3.
    unfold disj; intros.
    apply H.
    apply in_or_app; left; auto.
  Qed.
  Lemma disj_app_r: forall A (l1 l2 l3: list A), disj (l1 ++ l2) l3 -> disj l2 l3.
    unfold disj; intros.
    apply H.
    apply in_or_app; right; auto.
  Qed.
  Lemma disj_tran: forall A (l1 l2 l3 l4: list A), disj l1 l2 -> incl l3 l1 -> incl l4 l2 -> disj l3 l4.
    unfold disj; unfold incl; intros;
      repeat match goal with
               | [H: forall _, In _ ?ls -> _, H0: In _ ?ls |- _ ] => apply H in H0
               | [H: ~ In _ _ |- ~ In _ _] => contradict H
             end; auto.
  Qed.
  Lemma disj_cons: forall A l1 l2 (var:A), disj l1 l2 -> ~ In var l1 -> disj l1 (var::l2).
    unfold disj; intros.
    contradict H0.
    destruct H0.
    rewrite H0 in *; auto.
    apply H in H0; intuition.
  Qed.
  Lemma disj_notIn: forall A ls l1 l2 (v: A), disj l1 l2 -> In v l2 -> incl ls l1 -> ~ In v ls.
    unfold disj; unfold incl; intros.
    contradict H0.
    repeat match goal with
             | [H: forall _, In _ ?ls -> _, H0: In _ ?ls |- _ ] => apply H in H0
             | [H: ~ In _ _ |- ~ In _ _] => contradict H
           end; auto.
  Qed.
  (* End Disj *)

  (* unchanged in except *)

  Definition unchanged_in_except v v' within except :=
    forall x, In x within -> ~ In x except -> sel v' x = sel v x.

  
  Lemma unchanged_in_except_disjoint : forall vs1 vs2 within except other, 
    changedVariables vs1 vs2 (other ++ except) -> 
    disjoint within other -> 
    unchanged_in_except vs1 vs2 within except. 
    unfold unchanged_in_except; intros.
    eapply changed_in_inv in H; eauto.
    intuition.
    eapply in_app_or in H3.
    firstorder.
  Qed.

  Lemma unchanged_in_except_upd : forall vs1 vs2 changed vars s value, 
    changedVariables vs1 vs2 changed -> 
    disjoint vars changed -> 
    unchanged_in_except vs1 (upd vs2 s value) vars (s :: nil).
    unfold unchanged_in_except, disj, changedVariables; intros.
    destruct (string_dec s x).
    rewrite e in *.
    intuition.
    rewrite sel_upd_ne by eauto.
    eapply H0 in H1.
    eapply changed_in_inv in H; eauto.
  Qed.

  Lemma unchanged_in_except_shrink : forall vs1 vs2 within1 within2 except,
    unchanged_in_except vs1 vs2 within1 except ->
    incl within2 within1 ->
    unchanged_in_except vs1 vs2 within2 except.
    unfold unchanged_in_except; intros; eauto.
  Qed.

  Lemma unchanged_in_except_trans : forall vs1 vs2 vs3 within except1 except2 except3,
    unchanged_in_except vs1 vs2 within except1 ->
    unchanged_in_except vs2 vs3 within except2 ->
    incl except1 except3 ->
    incl except2 except3 ->
    unchanged_in_except vs1 vs3 within except3.
    unfold unchanged_in_except; intros; firstorder.
  Qed.
  
  Definition unchanged_in (vs1 vs2 : vals) vars := forall x, In x vars -> sel vs2 x = sel vs1 x.

  (* Lemmas about unchanged. unchanged_lemmas *)

  Lemma unchanged_in_symm : forall a b vars,
    unchanged_in a b vars ->
    unchanged_in b a vars.
    unfold unchanged_in; intros; symmetry; eauto.
  Qed.

  Lemma unchanged_incl : forall vs1 vs2 a b,
    unchanged_in vs1 vs2 a ->
    incl b a ->
    unchanged_in vs1 vs2 b.
    unfold unchanged_in; intros; eauto.
  Qed.

  Lemma unchanged_in_upd_same : forall vs1 vs2 vars s val,
    unchanged_in vs1 vs2 vars ->
    unchanged_in (upd vs1 s val) (upd vs2 s val) vars.
    unfold unchanged_in; intros.
    destruct (string_dec s x).
    repeat rewrite sel_upd_eq; eauto.
    repeat rewrite sel_upd_ne; eauto.
  Qed.

  Lemma changed_unchanged : forall vs1 vs2 changed unchanged,
    changed_in vs1 vs2 changed ->
    disjoint unchanged changed ->
    unchanged_in vs1 vs2 unchanged.
    unfold changedVariables, unchanged_in, disj; intros.
    destruct (weq (sel vs2 x) (sel vs1 x)).
    auto.
    firstorder.
  Qed.

  
  Lemma unchanged_trans : forall a b c vars,
    unchanged_in a b vars ->
    unchanged_in b c vars ->
    unchanged_in a c vars.
    unfold unchanged_in; intros; firstorder.
  Qed.


  Hint Resolve disjoint_nil_r.


  Hint Resolve unchanged_in_symm.
  Hint Resolve changedVariables_upd_bwd.
  Hint Resolve unchanged_incl. 


  Lemma unchanged_in_except_refl : forall vs within ex,
    unchanged_in_except vs vs within ex.
    unfold unchanged_in_except; eauto.
  Qed.

  Hint Resolve unchanged_in_except_refl.

  Lemma unchanged_in_except_symm : forall a b within except,
    unchanged_in_except a b within except ->
    unchanged_in_except b a within except.
    unfold unchanged_in_except; intros; firstorder.
  Qed.          

  Hint Resolve unchanged_in_except_symm. 

  Lemma unchanged_in_unchanged_except : forall vs1 vs2 vs3 within except,
    unchanged_in_except vs1 vs2 within except ->
    unchanged_in vs1 vs3 within ->
    unchanged_in_except vs3 vs2 within except.
    unfold unchanged_in_except, unchanged_in; intros; firstorder.
  Qed.

  Hint Resolve unchanged_in_symm.

  Lemma unchanged_in_unchanged_in_except : forall vs1 vs2 within ex,
    unchanged_in vs1 vs2 within ->
    unchanged_in_except vs1 vs2 within ex.
    intros; eapply unchanged_in_unchanged_except; eauto.
  Qed.
  
  Lemma changed_in_unchanged_in_except' : forall a b c within ex,
    unchanged_in_except a b within ex ->
    changed_in c b ex ->
    unchanged_in_except a c within ex.
    unfold unchanged_in_except; intros.
    eapply changed_in_inv in H0.
    2 : eauto.
    firstorder.
  Qed.

  Hint Resolve changed_in_unchanged_in_except'.

  Definition equiv vs1 vs2 := changedVariables vs1 vs2 nil.

  Notation "a ~ b" := (equiv a b) (at level 80).

  Lemma unchanged_in_except_equiv : forall a b c within ex,
    unchanged_in_except a b within ex ->
    equiv c b ->
    unchanged_in_except a c within ex.
    eauto.
  Qed.

  Lemma changed_in_unchanged_in_except : forall vs1 vs2 within ex,
    changed_in vs1 vs2 ex ->
    unchanged_in_except vs1 vs2 within ex.
    eauto.
  Qed.

  Lemma changed_back : forall vs1 vs2 within except,
    unchanged_in_except vs1 vs2 within except ->
    unchanged_in (merge vs1 vs2 except) vs1 within.
    unfold unchanged_in_except, unchanged_in; intros.
    destruct (in_dec string_dec x except).
    rewrite sel_merge; eauto.
    rewrite sel_merge_outside; try symmetry; eauto.
  Qed.

  
  Hint Resolve changed_unchanged.

  Lemma unchanged_in_equiv : forall a b c vars,
    equiv c b ->
    unchanged_in a b vars ->
    unchanged_in a c vars.
    intros; eapply unchanged_trans; eauto.
  Qed.
  (* End unchanged*)


  (**************************************)
  (*    I have cleaned until here       *)
  (*            June 4 2013             *)
  (**************************************)



  (*The follwoing ltac is unused. Delete? june 4 2013*)
  Ltac dec_sel :=
    match goal with
      | H : context [sel ?A ?B = sel ?C ?D] |- _ => destruct (weq (sel A B) (sel C D))
      | |- context [sel ?A ?B = sel ?C ?D] => destruct (weq (sel A B) (sel C D))
    end.


  



  (*
  Hint Resolve in_or_app in_eq In_incl.
  Hint Resolve List.incl_cons incl_cons_l incl_cons_r incl_app incl_appl incl_appr incl_refl incl_array incl_tran incl_nil incl_tl.
  Hint Immediate incl_cons_back.
  Hint Resolve disjoint_trans_lr.
  Hint Resolve unchanged_in_except_disjoint unchanged_in_except_upd unchanged_in_except_shrink.
  Hint Constructors or.
  Hint Resolve sel_upd_eq.*)

  Lemma equiv_symm : forall a b,
    equiv a b ->
    equiv b a.
    unfold equiv; eauto.
  Qed.

  Lemma equiv_trans : forall a b c, equiv a b -> equiv b c -> equiv a c.
    unfold equiv; eauto.
  Qed.

  Lemma equiv_merge : forall vs1 vs2 vs3 vars,
    unchanged_in vs1 vs2 vars ->
    changed_in vs1 vs3 vars ->
    equiv vs1 (merge vs2 vs3 vars).
    unfold equiv, changedVariables, unchanged_in; intros.
    destruct (in_dec string_dec x vars).
    rewrite sel_merge in H1 by eauto; firstorder.
    rewrite sel_merge_outside in H1 by eauto; firstorder.
  Qed.

  Lemma two_merge_equiv : forall a b c vars1 vars2,
    changed_in a b vars1 ->
    incl vars1 vars2 ->
    equiv (merge c a vars2) (merge c b vars2).
    unfold equiv, changedVariables; intros.
    destruct (in_dec string_dec x vars1).
    do 2 rewrite sel_merge in H1; intuition.
    destruct (in_dec string_dec x vars2).
    do 2 rewrite sel_merge in H1; intuition.
    do 2 rewrite sel_merge_outside in H1; intuition.
  Qed.



  Lemma equiv_eval : forall a b v v' v'' vars1 vars2,
    equiv a (merge v' v vars1) ->
    equiv b (merge v'' a vars2) ->
    unchanged_in_except v v' (vars1 ++ vars2) vars1 ->
    unchanged_in_except v' v'' (vars1 ++ vars2) vars2 ->
    equiv b (merge v'' v (vars1 ++ vars2)).
    intros.
    eapply equiv_trans; eauto.
    eapply equiv_merge.
    eapply changed_back.
    eapply unchanged_in_except_equiv.
    2 : eauto.
    eapply unchanged_in_except_symm.
    eapply unchanged_in_unchanged_except.
    Focus 2.
    eapply unchanged_in_symm.
    eapply changed_back.
    eauto.
    eauto.
    eapply changedVariables_trans.
    eapply changed_merge_bwd.
    eapply changedVariables_trans.
    eauto.
    eapply changed_merge_bwd.
    eauto.
    eauto.
    eauto.
    eauto.
  Qed.

  Lemma S_minus_S : forall n m, (S m <= n)%nat -> n - m = S (n - S m).
    induction n; induction m; simpl; intuition; destruct m; simpl; intuition.
  Qed.

  Lemma plus_n_Sn : forall n m : nat, S (n + m) = S n + m.
    induction n; induction m; simpl; intuition.
  Qed.

  Lemma split_tmps : forall m n, (m <= n)%nat -> tempVars n = tempVars m ++ tempChunk m (n - m) .
    Transparent tempVars tempChunk.
    induction m; induction n; unfold tempVars in *; try solve [simpl; intuition].
    intros.
    simpl.
    intuition.
    destruct (le_lt_dec (S m) n).
    erewrite IHn by eauto.
    simpl.
    rewrite app_assoc_reverse.
    f_equal.
    rewrite (@S_minus_S n m) by eauto.
    Opaque tempOf.
    simpl.
    f_equal.
    f_equal.
    f_equal.
    rewrite plus_n_Sn by eauto.
    rewrite le_plus_minus_r by eauto.
    eauto.
    replace n with m.
    rewrite minus_diag.
    simpl.
    rewrite app_assoc_reverse.
    rewrite app_nil_r.
    eauto.
    omega.
  Qed.

End variables.

(** Tacticas **)

Ltac in_tac:=
  match goal with 
    | [ |- In (tempOf _) (tempVars _) ] => eapply temp_in_array
    | [ |- In (tempOf _) (tempChunk _ _) ] => eapply temp_in_chunk
    | [ |- In (tempOf _) _ ] => eapply In_incl
    | [H: In _ (tempVars _) |- In _ (tempVars _)] => eapply In_tempVars_tran; [ | eapply H]
    | _ =>  solve [eapply chunk_union]
    | [H: In ?s (tempChunk _ _)|- In ?s (tempVars _)] =>
      eapply tempVars_incl_chunkVars; eauto
    | _ => eapply incl_tempChunk
  end.

Ltac notIn_tac:=
  match goal with
    | [ H: forall _, _ -> _ -> False |- ~ In ?s' _ ] => unfold not; intros; eapply H with (s:=s')
    | [ H: forall _, _ -> ~ In _ _ |- ~ In ?s' _ ] => unfold not; intros; eapply H with (s:=s')
    | [ H: disj _ _ |- ~ In ?s' _ ] => eapply disj_notIn; [eapply H | eapply temp_in_array | eapply incl_app_right]
    | [ |- ~In (tempOf _) _ ] => eapply temps_not_in_array
  end.

Ltac incl_tac:=
  match goal with
    | _ => solve[apply incl_refl]
    | _ => solve[eapply incl_app_backl; eauto]
    | _ => solve[eapply incl_app_backr; eauto]
    | [ |- incl (tempVars _) (tempVars _) ] => solve[ eapply incl_array; variables_ineq]
    | [ |- incl (tempChunk _ _) (tempChunk _ _) ] => solve[ eapply incl_chunk; variables_ineq] 
    | [ _ :  incl (tempChunk _ _) ?vars |- incl (tempChunk _ _) ?vars ] => solve[ eapply incl_tran2; eauto; eapply incl_chunk; variables_ineq] 
    | _ => solve[ eapply incl_tran; [eapply incl_array | eauto ] ; variables_ineq ] (*This should solve*)
  end.

Ltac simpl_vars:=
  match goal with
    | [ |- context[ sel (upd _ ?nm _ ) ?nm ] ] => rewrite sel_upd_eq; [ | reflexivity ]
    | [ |- context[ sel (upd _ _ _ ) _ ] ] => rewrite sel_upd_ne
  end.

Ltac sel_tac:=
  match goal with
    | [ H: forall _, _ -> sel _ _ = sel ?varVals _ |- sel _ ?s = sel ?varVals ?s] => rewrite <- H; [ | auto]
    | [ |- sel _ ?s = sel _ ?s] => eapply eval_changed_vars
  end.

Ltac changed_ltac:=
  match goal with
    | _ => solve[ eapply nillChange]
    | _ => solve[ eapply noChange]
    | [H: changedVariables ?v1 ?v2 _, H0: changedVariables (upd ?v2 _ _) ?v3 _ |- changedVariables ?v1 ?v3 _] => eapply (ChangeVar_tran_(v2:=v2))
    | [H: changedVariables ?v1 ?v2 _ |- changedVariables ?v1 ?v2 _ ] => eapply (changedVariables_incl H)
    | [H: changedVariables (upd ?v1 ?s ?value ) ?v2 _ |- changedVariables ?v1 ?v2 _ ] => eapply (changedVariables_upd_back(s:=s)(value:=value))
    | [H: changedVariables ?v1 ?v2 _ |- changedVariables ?v1 (upd ?v2 ?s ?value ) _ ] => eapply (changedVariables_upd')
    (*| [H: changedVariables ?v1 (upd ?v2 _ _) _, H0: changedVariables ?v2 ?v3 _ |- changedVariables ?v1 ?v3 _] => eapply ChangeVar_tran
    | [H1: changedVariables (upd _ _ _) _ _, H2: changedVariables _ _ _ |- changedVariables _ _ _ ] => eapply upd_changeVariables in H1; [   eapply cv_tran; eauto; [ eapply incl_tvc_l | eapply incl_tvc_r ] | apply temp_in_chunk' | apply tvc_S_shift]*)
  end.

Ltac variables_light :=
  match goal with
    | _ => simpl_vars
    | [ |- incl _ _ ] => incl_tac 
    | [ |- _ ] => in_tac
  end.

Ltac variables_ltac :=
  match goal with
    | |- interp _ _ => fail 1
    | _ => simpl_vars
    | [ |- incl _ _ ] => incl_tac 
    | [ |- In _ _ ] => in_tac
    | [ |- sel _ _ = sel _ _] => sel_tac
    | [ |- ~In _ _] => notIn_tac
    | [ |- changedVariables _ _ _] => changed_ltac
    | [H: forall _, _ -> _ -> False , H0: In ?s _, H1: In ?s _ |- False ] => eapply (H s)
    | [  H: forall _, _ -> not _ |- not (eq _ ?s') ]=> unfold not in H
    | [  H: forall _, _ -> _ -> False |- not (eq _ ?s') ]=> unfold not; intro eq1; eapply H with (s:= s'); [ | rewrite <- eq1]
    | [ |- disj _ _ ]=> eapply disj_tran; eauto; try (eapply incl_app_left); try (eapply incl_app_right); try (eapply incl_array)
    | [ |- _ -> _ ] => intros
  end.

(*A copy for comparison
   Ltac variables_ltac :=
  match goal with
    | _ => simpl_vars
    | [ |- incl _ _ ] => incl_tac 
    | [ |- In _ _ ] => in_tac
    | [ |- sel _ _ = sel _ _] => sel_tac
    | [ |- ~In _ _] => notIn_tac
    | [H: forall _, _ -> _ -> False , H0: In ?s _, H1: In ?s _ |- False ] => eapply (H s)
    | [  H: forall _, _ -> not _ |- not (eq _ ?s') ]=> unfold not in H
    | [  H: forall _, _ -> _ -> False |- not (eq _ ?s') ]=> unfold not; intro eq1; eapply H with (s:= s'); [ | rewrite <- eq1]
    | [ |- disj _ _ ]=> eapply disj_tran; eauto; try (eapply incl_app_left); try (eapply incl_app_right); try (eapply incl_array)
    (*| [ |- exprDenote _ _ = exprDenote _ _] => apply_sameDenote; [eapply changedVariables_upd; eauto | eapply disj_cons ]*)
    | [ |- _ -> _ ] => intros
  end.

*)

Ltac variables_tran :=
  match goal with
    | [ |- ~ In _ _ ] => eapply in_tran_not
    | _ => idtac
  end.

(* Main result *)

Ltac variables:= (*variables_tran; *)
  eauto; repeat (variables_ltac; eauto); try variables_ineq.
