Require Import Setoid.
Require Import Env.
Require Import Word.

Definition B := word 8.

Require Import List.

Module Type Heap.
  
  Parameter addr : Type.

  Parameter mem : Type.

  Parameter mem_get : mem -> addr -> option B.
  Parameter mem_set : mem -> addr -> B -> mem.

  Parameter mem_get_set_eq : forall m p v v', 
    mem_get m p = Some v ->
    mem_get (mem_set m p v') p = Some v'.

  Parameter mem_get_set_neq : forall m p p' v v', 
    p <> p' ->
    mem_get m p = Some v ->
    mem_get (mem_set m p' v') p = Some v.

  Parameter addr_dec : forall a b : addr, {a = b} + {a <> b}.

  Parameter all_addr : list addr.

  (** TODO: I didn't need this **)
  Parameter NoDup_all_addr : NoDup all_addr.

End Heap.

Module HeapTheory (B : Heap).
  Import B.

  Definition smem' dom : Type := hlist (fun _ : addr => option B) dom.

  Fixpoint smem_emp' (ls : list addr) : smem' ls :=
    match ls with
      | nil => HNil
      | a :: b => HCons None (smem_emp' b)
    end.
  Fixpoint disjoint' dom : smem' dom -> smem' dom -> Prop :=
    match dom with
      | nil => fun _ _ => True
      | a :: b => fun m1 m2 => 
           (hlist_hd m1 = None \/ hlist_hd m2 = None) 
        /\ disjoint' _ (hlist_tl m1) (hlist_tl m2)
    end.
  Fixpoint join' dom : smem' dom -> smem' dom -> smem' dom :=
    match dom with
      | nil => fun _ _ => HNil
      | a :: b => fun m1 m2 => 
        HCons 
        match hlist_hd m1 with
          | None => hlist_hd m2
          | Some x => Some x
        end
        (join' _ (hlist_tl m1) (hlist_tl m2))
    end.
  
  Fixpoint smem_get' dom : addr -> smem' dom -> option B :=
    match dom as dom return addr -> smem' dom -> option B with 
      | nil => fun _ _ => None
      | a :: b => fun a' m =>
        if addr_dec a a' then 
          hlist_hd m
        else
          smem_get' b a' (hlist_tl m)
    end.

  Fixpoint smem_set' dom : addr -> B -> smem' dom -> smem' dom :=
    match dom as dom return addr -> B -> smem' dom -> smem' dom with 
      | nil => fun _ _ _ => HNil
      | a :: b => fun p v m =>
        if addr_dec a p then
          HCons (Some v) (hlist_tl m)
        else
          HCons (hlist_hd m) (smem_set' b p v (hlist_tl m))
    end.


  Fixpoint satisfies' dom (m : smem' dom) (m' : B.mem) : Prop :=
    match m with
      | HNil => True
      | HCons p _ a b =>
        match a with
          | None => True
          | Some x => B.mem_get m' p = Some x 
        end /\ satisfies' _ b m'
    end.

  Definition smem : Type := smem' all_addr.

  Definition smem_emp : smem := smem_emp' all_addr.

  Definition smem_get := @smem_get' all_addr.

  Definition smem_set := @smem_set' all_addr.

(*
  Section MultiByte.
    Fixpoint tuple (T : Type) (n : nat) : Type :=
      match n with
        | 0 => unit
        | S n => T * tuple T n
      end%type.

    Record MultiByte (T : Type) :=
    { size  : nat
    ; footprint : addr -> tuple addr size
    ; implode : tuple B size -> T
    ; explode : T -> tuple B size
    }.

    Fixpoint getAll (m : smem) (n : nat) {struct n} : tuple addr n -> option (tuple B n) :=
      match n with
        | 0 => fun _ => Some tt
        | S n => fun (p : addr * tuple addr n) =>
          match smem_get (fst p) m with
            | None => None
            | Some v =>
              match getAll m n (snd p) with
                | Some v' => Some (v,v')
                | _ => None
              end
          end
      end.

    Fixpoint setAll (m : smem) (n : nat) {struct n} : tuple addr n -> tuple B n -> smem :=
      match n as n return tuple addr n -> tuple B n -> smem with
        | 0 => fun _ _ => m
        | S n => fun (p : addr * tuple addr n) (v : B * tuple B n) =>
          let m := smem_set (fst p) (fst v) m in
          setAll m n (snd p) (snd v)
      end.

    Definition smem_get_mb T (mb : MultiByte T) (p : addr) (m : smem)
      : option T :=
      match @getAll m (size _ mb) (footprint _ mb p) with
        | None => None
        | Some v => Some (implode _ mb v)
      end.

    Definition smem_set_mb T (mb : MultiByte T) (p : addr) (v : T) (m : smem)
      : smem :=
      setAll m (size _ mb) (footprint _ mb p) (explode _ mb v).
  End MultiByte.
*)

  Definition disjoint (m1 m2 : smem) : Prop :=
    disjoint' _ m1 m2.

  Definition join (m1 m2 : smem) : smem := 
    join' _ m1 m2.

  Definition split (m ml mr : smem) : Prop :=
    disjoint ml mr /\ m = join ml mr.

  Definition semp (m : smem) : Prop :=
    m = smem_emp.

  Definition satisfies (m : smem) (m' : B.mem) : Prop :=
    satisfies' _ m m'.

  Global Instance EqDec_addr : EquivDec.EqDec addr (@eq addr) := addr_dec.

  Theorem satisfies_get : forall m m',
    satisfies m m' ->
    forall p v, 
      smem_get p m = Some v ->
      mem_get m' p = Some v.
  Proof.
    unfold satisfies, smem_get, smem.
    induction all_addr; simpl; intros.
      congruence.
      rewrite (hlist_eta _ m) in H. simpl in *.
      destruct (addr_dec a p); subst; simpl in *; auto.
      rewrite H0 in *; intuition.
      destruct H.
      eapply IHl; eauto.
  Qed.

  Theorem satisfies_set : forall m m',
    satisfies m m' ->
    forall p v,
      satisfies (smem_set p v m) (mem_set m' p v).
  Proof.
    unfold satisfies, smem_set, smem.
    induction all_addr; simpl; intros.
      auto.
      destruct (addr_dec a p).
      rewrite (hlist_eta _ m) in H.
      subst; simpl in *.
  Admitted. (** TODO : need to think more about this **)

  Theorem satisfies_split : forall m m',
    satisfies m m' ->
    forall m0 m1, 
      split m m0 m1 ->
      satisfies m0 m' /\ satisfies m1 m'.
  Proof.
    unfold satisfies, split, disjoint, join, smem.
    induction all_addr. intros.
    rewrite (hlist_nil_only _ m0) in *.
    rewrite (hlist_nil_only _ m1) in *. simpl. auto.    
    
    intro. rewrite (hlist_eta _ m). do 4 intro.
    rewrite (hlist_eta _ m0). rewrite (hlist_eta _ m1). simpl in *.
    intros.
    repeat match goal with
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : HCons _ _ = HCons _ _ |- _ ] => inversion H; clear H
           end.
    specialize (IHl _ _ H3).
    eapply EqdepClass.inj_pair2 in H6.
    intros. specialize (IHl _ _ (conj H2 H6)).
    destruct (hlist_hd m0); destruct (hlist_hd m1); eauto; 
    intuition (try congruence);
    rewrite H5 in *; eauto.
  Qed.

  Ltac unfold_all :=
    unfold smem, split, join, disjoint, smem_emp, semp; 
    unfold smem, split, join, disjoint, smem_emp, semp.
  Ltac break :=
    simpl; intros; try reflexivity;
      repeat (simpl in *; match goal with
                            | [ H : HCons _ _ = HCons _ _ |- _ ] =>
                              inversion H; clear H
                            | [ H : _ /\ _ |- _ ] => destruct H
                            | [ H : @existT _ _ _ _ = @existT _ _ _ _ |- _ ] => 
                              eapply (@Eqdep_dec.inj_pair2_eq_dec _ (list_eq_dec B.addr_dec)) in H
                            | [ H : @existT _ _ _ _ = @existT _ _ _ _ |- _ ] => 
                              eapply (@Eqdep_dec.inj_pair2_eq_dec _ B.addr_dec) in H
                            | [ H : _ = _ |- _ ] => rewrite H in *
                          end).
  
  Lemma disjoint_join : forall a b, disjoint a b -> join a b = join b a.
  Proof.
    unfold_all; induction a; break; f_equal; intuition; subst.
      destruct (hlist_hd b0); reflexivity.
      rewrite H1. destruct b; reflexivity.
  Qed.
    
  Lemma disjoint_comm : forall ml mr, disjoint ml mr -> disjoint mr ml.
  Proof.
    unfold_all; induction ml; break; intuition.
  Qed.

  Hint Resolve disjoint_join disjoint_comm : disjoint.

  Lemma split_assoc : forall b a c d e, split a b c -> split c d e ->
    split a (join d b) e.
  Proof.
    unfold_all; induction b; break; eauto.
    edestruct IHb. split; try eassumption. reflexivity. split; try eassumption.
    reflexivity.
    intuition; break; auto. destruct (hlist_hd d); auto.
    destruct (hlist_hd d); try congruence.
  Qed.

  Lemma split_comm : forall ml m mr, split m ml mr -> split m mr ml.
  Proof.
    unfold_all. induction ml; break; eauto. edestruct IHml.
    split; try eassumption. reflexivity. 
    intuition; subst. rewrite H3. destruct (hlist_hd mr); auto.
    rewrite H4. rewrite H3. destruct b; auto.
  Qed.

  Lemma disjoint_split_join : forall a b, disjoint a b -> split (join a b) a b.
  Proof.
    unfold split, disjoint; intros; intuition.
  Qed.

  Lemma split_split_disjoint : forall b a c d e,
    split a b c -> split b d e -> disjoint c d.
  Proof.
    unfold_all. induction b; break. subst. split.
    intuition; destruct (hlist_hd c); eauto. destruct (hlist_hd d); auto.
    eapply IHb. split; auto. split; auto. auto.
  Qed.

  Lemma hlist_destruct : forall T (F : T -> Type) a b (m : hlist F (a :: b)),
    exists A, exists B, m = HCons A B.
  Proof.
    intros.
    refine (match m as m in hlist _ ls return
              match ls as ls return hlist _ ls -> Type with
                | nil => fun _ => unit
                | a :: b => fun m => exists A : F a, exists B : hlist F b, m = HCons A B
              end m
              with
              | HNil => tt
              | HCons _ _ _ _ => _
            end).
    do 2 eexists; reflexivity.
  Qed.
  Lemma hlist_nil : forall T (F : T -> Type) (m : hlist F nil), m = HNil.
  Proof.
    intros. 
    refine (match m as m in hlist _ ls return
              match ls as ls return hlist _ ls -> Type with
                | nil => fun m => m = HNil
                | _ :: _ => fun _ => unit
              end m
              with
              | HNil => _ 
              | _ => tt
            end). reflexivity.
  Qed.

  Lemma split_semp : forall b a c, 
    split a b c -> semp b -> a = c.
  Proof.
    unfold_all. unfold semp, smem_emp. unfold_all.
    induction b; simpl; intros; subst; auto.
    rewrite hlist_nil. rewrite (hlist_nil _ _ a). reflexivity.
    destruct (hlist_destruct _ _ _ _ a).
    destruct (hlist_destruct _ _ _ _ c).
    destruct H1. destruct H2. subst. specialize (IHb x2 x3).
    rewrite IHb; break; intuition; auto.
  Qed.

  Lemma semp_smem_emp : semp smem_emp.
  Proof.
    unfold semp, smem_emp; auto.
  Qed.

  Lemma split_a_semp_a : forall a, 
    split a smem_emp a.
  Proof.
    unfold_all. induction a; simpl; intuition. rewrite <- H0. reflexivity.
  Qed.

End HeapTheory.
