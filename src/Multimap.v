Require Import HintlessFMapInterface HintlessFMapFacts.
Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

Module Make (FM : S).
  Module FM := FM.
  Module FACTS := HintlessFMapFacts.WFacts_fun FM.E FM.
  Module PROPS := HintlessFMapFacts.WProperties_fun FM.E FM.
  
  Lemma find_Empty : forall T (m : FM.t T) x,
    FM.Empty m -> FM.find x m = None.
  Proof.
    intros.
    apply PROPS.F.not_find_in_iff. 
    unfold FM.In, FM.Empty in *. specialize (H x).
    intro. destruct H0. eapply H. eauto.
  Qed.

  Section typed.
    Variable T : Type.
  
    Definition mmap := FM.t (list T).

    Definition empty : mmap := FM.empty _.

    Definition mmap_add (k : FM.key) (v : T) (m : mmap) : mmap :=
      match FM.find k m with
        | None => FM.add k (v :: nil) m
        | Some v' => FM.add k (v :: v') m
      end.

    Definition mmap_extend (k : FM.key) (v : list T) (m : mmap) : mmap :=
      match FM.find k m with
        | None => FM.add k v m
        | Some v' => FM.add k (v ++ v') m
      end.

    Lemma Proper_mmap_extend : Proper (FM.E.eq ==> eq ==> FM.Equal ==> FM.Equal) mmap_extend.
    Proof.
      unfold mmap_extend.
      repeat (red; intros; subst). rewrite H; rewrite H0. destruct (FM.find (elt:=list T) y y1); rewrite H; rewrite H0; auto.
    Qed.
      
    Lemma transpose_neqkey_mmap_extend : PROPS.transpose_neqkey FM.Equal mmap_extend.
    Proof.
      unfold mmap_extend. repeat (red; intros; subst).
      (repeat match goal with
                | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                | [ H : _ = _ |- _ ] => rewrite H 
                | [ H : _ = _ |- _ ] => rewrite H in *
                | [ H : FM.E.eq _ _ |- _ ] => rewrite H 
                | [ H : FM.E.eq _ _ |- _ ] => rewrite H in *
                | [ H : context [ FM.find _ _ ] |- _ ] => 
                  rewrite FACTS.add_o in H
                | [ |- context [ FM.find ?k ?a ] ] =>
                  match a with
                    | match _ with 
                        | Some _ => _
                        | None => _
                      end => fail 1
                    | _ => case_eq (FM.find k a); intros
                  end
              end);
      repeat match goal with
               | [ H : ~ FM.E.eq ?X ?X |- _ ] => exfalso; apply H; reflexivity
               | [ H : FM.E.eq _ _ |- _ ] => rewrite H 
               | [ H : FM.E.eq _ _ |- _ ] => rewrite H in *
               | [ H : Some _ = Some _ |- _ ] => inversion H ; clear H; subst
               | [ H : context [ FM.E.eq_dec ?A ?B ] |- _ ] =>
                 destruct (FM.E.eq_dec A B); try congruence
             end.
    Qed.
    Existing Instance Proper_mmap_extend.
    Existing Class PROPS.transpose_neqkey.
    Existing Instance transpose_neqkey_mmap_extend.

    Definition mmap_join : mmap -> mmap -> mmap :=
      FM.fold mmap_extend.

    Lemma mmap_join_o : forall (a b : mmap) x,
      FM.find x (mmap_join a b) = 
      match FM.find x a with
        | Some a => 
          match FM.find x b with
            | Some b => Some (a ++ b)
            | None => Some a
          end
        | None => FM.find x b 
      end.
    Proof.
      clear. unfold mmap_join.
      do 2 intro. apply PROPS.map_induction with (m := a); intros.
      rewrite PROPS.fold_Empty; eauto with typeclass_instances.
      symmetry.
      repeat rewrite find_Empty by assumption; auto. 
      
      rewrite PROPS.fold_Add; try solve [ clear; eauto with typeclass_instances ]. 
      unfold mmap_extend at 1. rewrite H.
      apply PROPS.F.not_find_in_iff in H0. rewrite H0.

      specialize (H1 x0). rewrite H1.
      case_eq (FM.find x b); intros; rewrite FACTS.add_o; destruct (FM.E.eq_dec x x0); 
        try rewrite H;
          repeat match goal with
                   | [ H : FM.E.eq _ _ |- _ ] => rewrite H in *; clear H
                   | [ H : ~FM.E.eq ?X ?X |- _ ] => exfalso; apply H; reflexivity
                   | [ H : _ = _ |- _ ] => rewrite H
                   | [ |- context [ FM.E.eq_dec ?X ?Y ] ] =>
                     destruct (FM.E.eq_dec X Y); try congruence
                   | _ => rewrite FACTS.add_o in *
                 end.
    Qed.

    Lemma mmap_join_remove_acc : forall k (a b : mmap),
      ~FM.In k a ->
      FM.Equal (FM.remove k (mmap_join a b)) (mmap_join a (FM.remove k b)).
    Proof.
      unfold FM.Equal. intros.
      repeat (rewrite FACTS.remove_o || rewrite mmap_join_o).
      destruct (FM.E.eq_dec k y); try reflexivity.
      apply PROPS.F.not_find_in_iff in H.
      rewrite e in *.
      rewrite H. reflexivity. 
    Qed.
     
  End typed.

  Definition mmap_map T U (F : T -> U) : mmap T -> mmap U :=
    FM.map (map F).

  Definition mmap_mapi T U (F : FM.key -> T -> U) : mmap T -> mmap U :=
    FM.mapi (fun k => map (F k)).


End Make.