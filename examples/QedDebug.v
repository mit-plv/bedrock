Require Import AutoSep.

Set Implicit Arguments.


(** The king of the abstract predicates *)

Module Type SINGLY_LINKED_LIST.
  Parameter sll : list W -> W -> HProp.

  Axiom sll_extensional : forall ls p, HProp_extensional (sll ls p).

  Axiom nil_fwd : forall ls (p : W), p = 0
    -> sll ls p ===> [| ls = nil |].

  Axiom nil_bwd : forall ls (p : W), p = 0
    -> [| ls = nil |] ===> sll ls p.

  Axiom cons_fwd : forall ls (p : W), p <> 0
    -> sll ls p ===> Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p'.

  Axiom cons_bwd : forall ls (p : W), p <> 0
    -> (Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p') ===> sll ls p.
End SINGLY_LINKED_LIST.

Module SinglyLinkedList : SINGLY_LINKED_LIST.
  Open Scope Sep_scope.

  Fixpoint sll (ls : list W) (p : W) : HProp :=
    match ls with
      | nil => [| p = 0 |]
      | x :: ls' => [| p <> 0 |] * Ex p', (p ==*> x, p') * sll ls' p'
    end.

  Theorem sll_extensional : forall ls (p : W), HProp_extensional (sll ls p).
    destruct ls; reflexivity.
  Qed.

  Theorem nil_fwd : forall ls (p : W), p = 0
    -> sll ls p ===> [| ls = nil |].
    destruct ls; sepLemma.
  Qed.

  Theorem nil_bwd : forall ls (p : W), p = 0
    -> [| ls = nil |] ===> sll ls p.
    destruct ls; sepLemma.
  Qed.

  Theorem cons_fwd : forall ls (p : W), p <> 0
    -> sll ls p ===> Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p'.
    destruct ls; sepLemma.
  Qed.

  Theorem cons_bwd : forall ls (p : W), p <> 0
    -> (Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p') ===> sll ls p.
    destruct ls; sepLemma;
      match goal with
        | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; intros; subst; reflexivity
      end.
  Qed.
End SinglyLinkedList.

Import SinglyLinkedList.
Hint Immediate sll_extensional.

Definition hints_sll' : TacPackage.
  prepare1 (nil_fwd, cons_fwd) (nil_bwd, cons_bwd).
Defined.

Definition hints_sll : TacPackage.
  prepare2 hints_sll'.
Defined.

Lemma natToW_S : forall n, natToW (S n) = $1 ^+ natToW n.
  unfold natToW.
  intros.
  rewrite wplus_alt.
  unfold wplusN, wordBinN.
  simpl.
  rewrite roundTrip_1.
  destruct (wordToNat_natToWord 32 n); intuition.
  rewrite H0.
  replace (1 + (n - x * pow2 32)) with (1 + n - x * pow2 32) by omega.
  rewrite drop_sub; auto; omega.
Qed.

Ltac notConst x :=
  match x with
    | O => fail 1
    | S ?x' => notConst x'
    | _ => idtac
  end.


Ltac finish := repeat match goal with
                        | [ H : _ = _ |- _ ] => rewrite H
                      end; simpl;
               repeat match goal with
                        | [ |- context[natToW (S ?x)] ] =>
                          notConst x; rewrite (natToW_S x)
                      end; try rewrite <- rev_alt;
               congruence || W_eq || reflexivity || eauto.

Goal forall (a : settings) (b : state) (specs : codeSpec W (settings * state))
     (x : state),
   evalInstrs a x
     (Assign $[ Sp + 4]%SP $[ Rv + 4]%SP
      :: Assign $[ Rv + 4]%SP $[ Sp]%SP
         :: Assign $[ Sp]%SP Rv :: Assign Rv $[ Sp + 4]%SP :: @nil instr) =
   @Some state b ->
   forall (x0 : ST.settings * smem -> PropX W (settings * state)) 
     (x1 x2 : W) (x3 x4 : list W),
   evalCond Rv Ne 0 a x = @Some bool true ->
   @interp W (settings * state) specs
     (![@star W (ST.settings * state) (@nil Type)
          (@star W (ST.settings * state) (@nil Type)
             (@star W (ST.settings * state) (@nil Type)
                (@star W (ST.settings * state) (@nil Type) 
                   (Regs x Sp =*> x1) ((Regs x Sp ^+ $ (4)) =*> x2))
                (sll x3 (Regs x Rv))) (sll x4 x1))
          (fun (stn : ST.settings) (sm : smem) => x0 (stn, sm))] 
        (a, x)) ->
   forall x5 : ST.settings * state -> PropX W (settings * state),
   specs (Regs x Rp) =
   @Some (settings * state -> PropX W (settings * state))
     (fun x6 : settings * state => x5 x6) ->
   (forall x6 : settings * state,
    @interp W (settings * state) specs
      ((Ex x7 : W,
        (Ex x8 : W,
         (Ex x9 : list W,
          [|x9 = @rev_append W x3 x4|] /\
          @subst W (settings * state) (((settings * state)%type :Type) :: @nil Type)
            (@subst W (settings * state)
               (((settings * state)%type : Type)
                :: (ST.settings * smem)%type :: @nil Type)
               (![@star W (ST.settings * state)
                    (((settings * state)%type : Type)
                     :: (ST.settings * smem)%type :: @nil Type)
                    (@star W (ST.settings * state)
                       (((settings * state)%type : Type)
                        :: (ST.settings * smem)%type :: @nil Type)
                       (@star W (ST.settings * state)
                          (((settings * state)%type : Type)
                           :: (ST.settings * smem)%type :: @nil Type)
                          (Regs x Sp =*> x7) ((Regs x Sp ^+ $ (4)) =*> x8))
                       ^[sll x9 (x6) # (Rv)])
                    (fun (stn : ST.settings) (sm : smem) =>
                     @Lift W (ST.settings * state)
                       ((ST.settings * smem)%type :: @nil Type)
                       (settings * state)
                       (@Var0 W (ST.settings * state) 
                          (@nil Type) (ST.settings * smem) 
                          (stn, sm)))] x6) x0) x5)))%PropX ---> 
       x5 x6)) ->
   exists
     (a0 : ST.settings * smem -> PropX W (settings * state))
   (x6 x7 : W)(x8 x9 : list W),
     @simplify W (settings * state) specs
       ((ST.settings * smem)%type :: @nil Type)
       (![@star W (ST.settings * state)
            ((ST.settings * smem)%type :: @nil Type)
            (@star W (ST.settings * state)
               ((ST.settings * smem)%type :: @nil Type)
               (@star W (ST.settings * state)
                  ((ST.settings * smem)%type :: @nil Type)
                  (@star W (ST.settings * state)
                     ((ST.settings * smem)%type :: @nil Type)
                     (Regs b Sp =*> x6) ((Regs b Sp ^+ $ (4)) =*> x7))
                  ^[sll x8 (Regs b Rv)]) ^[sll x9 x6])
            (fun (stn : ST.settings) (sm : smem) =>
             @Var0 W (ST.settings * state) (@nil Type) 
               (ST.settings * smem) (stn, sm))] (a, b))
       (@SCons W (settings * state) (ST.settings * smem) 
          (@nil Type) a0 (SNil W (settings * state))) /\
     (exists a1 : ST.settings * state -> PropX W (settings * state),
        specs (Regs b Rp) =
        @Some (settings * state -> PropX W (settings * state))
          (fun x10 : settings * state => a1 x10) /\
        (forall x10 : settings * state,
         @interp W (settings * state) specs
           ((Ex x11 : W,
             (Ex x12 : W,
              (Ex x13 : list W,
               [|x13 = @rev_append W x8 x9|] /\
               @subst W (settings * state)
                 (((settings * state)%type : Type) :: @nil Type)
                 (@subst W (settings * state)
                    (((settings * state)%type : Type)
                     :: (ST.settings * smem)%type :: @nil Type)
                    (![@star W (ST.settings * state)
                         (((settings * state)%type : Type)
                          :: (ST.settings * smem)%type :: @nil Type)
                         (@star W (ST.settings * state)
                            (((settings * state)%type : Type)
                             :: (ST.settings * smem)%type :: @nil Type)
                            (@star W (ST.settings * state)
                               (((settings * state)%type : Type)
                                :: (ST.settings * smem)%type :: @nil Type)
                               (Regs b Sp =*> x11)
                               ((Regs b Sp ^+ $ (4)) =*> x12))
                            ^[sll x13 (x10) # (Rv)])
                         (fun (stn : ST.settings) (sm : smem) =>
                          @Lift W (ST.settings * state)
                            ((ST.settings * smem)%type :: @nil Type)
                            (settings * state)
                            (@Var0 W (ST.settings * state) 
                               (@nil Type) (ST.settings * smem) 
                               (stn, sm)))] x10) a0) a1)))%PropX ---> 
            a1 x10))).
Proof.
  intros.
  evaluate hints_sll.
  Show Proof.
  admit.
  descend.
  admit. admit. admit.
  repeat step hints_sll.
  repeat step hints_sll.
  repeat step hints_sll.
  finish.
(*Qed.*)
