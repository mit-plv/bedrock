(** A simple instantiation of cancellation, for testing purposes *)

Require Import AutoSep.

Require Import Depl.Logic Depl.Cancel.


Notation "|^ fE , e |" := (Lift (fun fE => e)) (fE at level 0) : expr_scope.
Delimit Scope expr_scope with expr.
Bind Scope expr_scope with expr.

Inductive ppred :=
| PtsTo (address value : expr)
| PPure (P : fo_env -> Prop)
| PStar (p1 p2 : ppred)
| PExists (x : fo_var) (p1 : ppred).

Infix "=*>" := PtsTo : ppred_scope.

Delimit Scope ppred_scope with ppred.
Bind Scope ppred_scope with ppred.

Notation "|^ fE , P |" := (PPure (fun fE => P%type)) (fE at level 0) : ppred_scope.
Infix "*" := PStar : ppred_scope.
Notation "'EX' x , p" := (PExists x p%ppred) (at level 89) : ppred_scope.
Notation "'Emp'" := (PPure (fun _ => True)) : ppred_scope.

Fixpoint ppredD (p : ppred) (fE : fo_env) : HProp :=
  match p with
    | PtsTo a v => Ex a', Ex v', [| exprD a fE = Dyn a' /\ exprD v fE = Dyn v' |] * a' =*> v'
    | PPure P => [| P fE |]
    | PStar p1 p2 => ppredD p1 fE * ppredD p2 fE
    | PExists x p1 => Ex y : W, ppredD p1 (fo_set fE x (Dyn y))
  end%Sep.

Definition pimpl (p1 p2 : ppred) :=
  ppredD p1 fo_empty ===> ppredD p2 fo_empty.

Fixpoint ppredX (p : ppred) : pred :=
  match p with
    | PtsTo a v => Named "ptsTo" (a :: v :: nil)
    | PPure P => Pure P
    | PStar p1 p2 => Star (ppredX p1) (ppredX p2)
    | PExists x p1 => Exists x (Star (Pure (fun fE => Ty (fE x) = W)) (ppredX p1))
  end.

Definition G : list Type := (W * W * settings * smem : Type)%type :: nil.

Definition hE : ho_env G :=
  fun _ es => match es return hpropB G with
                | a :: v :: nil => Ex a' : W, Ex v' : W, [| a = Dyn a' /\ v = Dyn v' |]
                  * (fun stn sm => Var0 (a', v', stn, sm))
                | _ => Emp
              end%Sep.

Definition S : subs W (settings * state) G :=
  SCons _ nil (fun p => let '(a, v, stn, sm) := p in ptsto32 _ a v stn sm) (SNil _ _).

Local Hint Immediate SubstsH_inj_fwd SubstsH_inj_bwd.

Theorem ppredX_forward : forall p fE, ppredD p fE ===> SubstsH S (predD (ppredX p) hE fE).
Proof.
  induction p; simpl; intuition.

  apply Himp'_ex; intro a'.
  apply Himp'_ex; intro v'.
  apply Himp_star_pure_c; intro.
  eapply Himp_trans; [ | apply SubstsH_ex_bwd ].
  apply Himp_ex_c; exists a'.
  eapply Himp_trans; [ | apply SubstsH_ex_bwd ].
  apply Himp_ex_c; exists v'.
  eapply Himp_trans; [ | apply SubstsH_star_bwd ].
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply SubstsH_inj_bwd | apply Himp_refl ] ].
  apply Himp_star_pure_cc; auto.
  apply Himp_refl.

  eapply Himp_trans; [ | apply SubstsH_star_bwd ].
  apply Himp_star_frame; auto.

  eapply Himp_trans; [ | apply SubstsH_ex_bwd ]; simpl.
  apply Himp'_ex; intro w.
  apply Himp_ex_c; exists (Dyn w).
  eapply Himp_trans; [ | apply SubstsH_star_bwd ].
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply SubstsH_inj_bwd | apply Himp_refl ]  ].
  apply Himp_star_pure_cc; auto.
  autorewrite with core; reflexivity.
Qed.

Theorem ppredX_backward : forall p fE, SubstsH S (predD (ppredX p) hE fE) ===> ppredD p fE.
Proof.
  induction p; simpl; intuition.

  eapply Himp_trans; [ apply SubstsH_ex_fwd | ].
  apply Himp'_ex; intro a'.
  eapply Himp_trans; [ apply SubstsH_ex_fwd | ].
  apply Himp'_ex; intro v'.
  eapply Himp_trans; [ apply SubstsH_star_fwd | ].
  eapply Himp_trans; [ apply Himp_star_frame; [ apply SubstsH_inj_fwd | apply Himp_refl ] | ].
  apply Himp_star_pure_c; intro.
  apply Himp_ex_c; exists a'.
  apply Himp_ex_c; exists v'.
  apply Himp_star_pure_cc; auto.
  apply Himp_refl.
  
  eapply Himp_trans; [ apply SubstsH_star_fwd | ].
  apply Himp_star_frame; auto.

  eapply Himp_trans; [ apply SubstsH_ex_fwd | ]; simpl.
  apply Himp'_ex; intro d.
  eapply Himp_trans; [ apply SubstsH_star_fwd | ].
  eapply Himp_trans; [ apply Himp_star_frame; [ apply SubstsH_inj_fwd | apply Himp_refl ] | ].
  apply Himp_star_pure_c; intros.
  autorewrite with core in *.
  destruct d; simpl in *; subst.
  apply Himp_ex_c; eauto.
Qed.

Fixpoint pwellScoped (xs : list fo_var) (p : ppred) : Prop :=
  match p with
    | PPure f => forall fE fE', (forall x, In x xs -> fE x = fE' x) -> f fE = f fE'
    | PStar p1 p2 => pwellScoped xs p1 /\ pwellScoped xs p2
    | PExists x p1 => pwellScoped (x :: xs) p1
    | PtsTo e1 e2 => forall fE fE', (forall x, In x xs -> fE x = fE' x)
      -> exprD e1 fE = exprD e1 fE' /\ exprD e2 fE = exprD e2 fE'
  end.

Theorem pwellScoped_forward : forall p xs, pwellScoped xs p -> wellScoped xs (ppredX p).
Proof.
  induction p; simpl; firstorder.
  rewrite H0; auto.
Qed.

Local Hint Immediate pwellScoped_forward.

Fixpoint pboundVars (p : ppred) : option (list fo_var) :=
  match p with
    | PPure _ => Some nil
    | PStar p1 p2 =>
      match pboundVars p1, pboundVars p2 with
        | Some xs1, Some xs2 =>
          if notsInList xs1 xs2 then Some (xs1 ++ xs2) else None
        | _, _ => None
      end
    | PExists x p1 =>
      match pboundVars p1 with
        | None => None
        | Some xs => if notInList x xs then Some (x :: xs) else None
      end
    | PtsTo _ _ => Some nil
  end.

Theorem pboundVars_boundVars : forall p, pboundVars p = boundVars (ppredX p).
Proof.
  induction p; simpl; intuition idtac;
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H
           end; auto.
  destruct (boundVars (ppredX p)); auto.
Qed.

Hint Rewrite pboundVars_boundVars.


(** * The (partial) decision procedure *)

Inductive result :=
| ProveThis (P : Prop)
| Failed (P : Prop).

Inductive lhs_remains (p : list pred) := .

Definition entail (lhs rhs : ppred) :=
  let lhs' := normalize (ppredX lhs) in
  let rhs' := normalize (ppredX rhs) in
    match cancel nil nil lhs' rhs' with
      | Success _ lhs'' P =>
        match lhs'' with
          | nil => ProveThis P
          | _ => Failed (lhs_remains lhs'')
        end
      | Failure P => Failed P
    end.

Local Hint Resolve normalize_wellScoped_NImpure.

Lemma addQuants_Emp_fwd : forall G (S : subs W (settings * state) G) qs fE,
  SubstsH S (addQuants qs (fun _ => Emp) fE) ===> Emp.
Proof.
  induction qs; simpl; intuition.

  apply SubstsH_emp_fwd.

  eapply Himp_trans; [ apply SubstsH_ex_fwd | ].
  apply Himp'_ex; auto.
Qed.

Theorem entail_correct : forall lhs rhs bl br P,
  entail lhs rhs = ProveThis P
  -> P
  -> pwellScoped nil lhs
  -> pwellScoped nil rhs
  -> pboundVars lhs = Some bl
  -> pboundVars rhs = Some br
  -> pimpl lhs rhs.
Proof.
  unfold entail; intros.
  case_eq (cancel nil nil (normalize (ppredX lhs)) (normalize (ppredX rhs))); intros.
  Focus 2.
  rewrite H5 in *; discriminate.
  rewrite H5 in *.
  destruct NewLhs; try discriminate.
  injection H; clear H; intros; subst.
  assert (Hfe : forall x, In x (@nil string) -> ~In x nil)
    by (simpl; tauto).
  specialize (cancel_sound nil nil fo_empty _ hE S _ _ _ _ _ Hfe H5); intuition.
  rewrite <- app_nil_end in *.
  match type of H6 with
    | ?P -> _ => assert P by eauto; intuition
  end.
  red.
  autorewrite with core in *.
  eapply Himp_trans; [ apply ppredX_forward | ].
  eapply Himp_trans; [ eapply normalize_sound_fwd; eauto | ].
  eapply Himp_trans; [ | apply ppredX_backward ].
  eapply Himp_trans; [ | eapply normalize_sound_bwd; eauto ].
  eapply Himp_trans; [ apply H7 | ].
  simpl; intuition.
  unfold normalD at 2; simpl.
  eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply addQuants_Emp_fwd ] | ].
  eapply Himp_trans; [ apply Himp_star_comm | ].
  apply Himp_star_Emp.
Qed.

Ltac entail'' := simpl; intuition (try subst; autorewrite with core in *; eauto; try congruence).

Ltac entail' := entail'';
  repeat (match goal with
            | [ H : forall x : fo_var, _ |- _ ] => rewrite H by entail''
          end; entail'').

Ltac entail := eapply entail_correct; [ reflexivity | .. ]; cbv beta; unfold hide_sub in *; entail'.


(** * Test cases *)

Definition null := |^_, Dyn (natToW 0)|%expr.

Definition Var' : string -> expr := Var.
Coercion Var' : string >-> expr.

Example test1 : pimpl (PtsTo null null) (PtsTo null null).
Proof.
  entail.
Qed.

Example test2 : pimpl (PtsTo null null) (EX "p", PtsTo "p" "p").
Proof.
  entail.
Qed.

Example test3 : pimpl (EX "p", PtsTo "p" "p") (EX "p", PtsTo "p" "p").
Proof.
  entail.
Qed.

Example test4 : pimpl (EX "p", PtsTo "p" "p") (EX "q", PtsTo "q" "q").
Proof.
  entail.
Qed.

Example test5 : pimpl (EX "p", PtsTo "p" null) (EX "q", EX "r", PtsTo "r" "q").
Proof.
  entail.
Qed.

Example test6 : pimpl (EX "a", EX "b", EX "c", PtsTo "a" "b" * PtsTo "c" null)
  (EX "a", EX "b", EX "c", PtsTo "c" null * PtsTo "a" "b").
Proof.
  entail.
Qed.

Example test7 : pimpl (EX "a", EX "b", PtsTo "a" "b" * PtsTo "b" null)
  (EX "a", EX "b", PtsTo "b" null * PtsTo "a" "b").
Proof.
  entail.
Qed.

Example test8 : pimpl Emp |^_, True|.
Proof.
  entail.
Qed.

Example test9 : pimpl |^_, False| Emp.
Proof.
  entail.
Qed.

Example test10 : pimpl (EX "x", null =*> "x" * |^E, E "x" <> E "x"|)
  (EX "x", null =*> "x" * |^E, E "x" = Dyn (natToW 0)|).
Proof.
  entail.
Qed.
 
Example test11 : pimpl (EX "x", EX "y", "x" =*> "y"
  * |^E, exists y : W, E "y" = Dyn y /\ E "x" = Dyn (y ^+ $1)|)
(EX "x", EX "y", "x" =*> "y"
  * |^E, exists x : W, E "x" = Dyn x /\ E "y" = Dyn (x ^- $1)|).
Proof.
  entail.
  firstorder.
  repeat esplit; eauto.
  rewrite H1.
  f_equal.
  words.
Qed.
