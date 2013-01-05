Require Import AutoSep DepList.

Set Implicit Arguments.


Fixpoint memoryOut' ls (m : smem' ls) : IL.mem :=
  match m with
    | HNil => fun _ => None
    | HCons a _ v m' => fun a' => if weq a' a then v else memoryOut' m' a'
  end.

Definition memoryOut (m : smem) : IL.mem := memoryOut' m.

Definition stateOut (p : settings * smem) (sc : W) : settings * state :=
  (fst p, {| Regs := fun _ => sc; Mem := memoryOut (snd p) |}).

Notation "##1" := (fun sc => ![ fun x : settings * smem => Lift (Var0 (stateOut x sc)) ])%Sep : Sep_scope.
Notation "##2" := (fun sc => ![ fun x : settings * smem => Lift (Lift (Var0 (stateOut x sc))) ])%Sep : Sep_scope.

Definition predIn (P : settings * state -> PropX W (settings * state)) (sc : W) : HProp :=
  fun stn sm => P (stateOut (stn, sm) sc).

Ltac make_Himp := match goal with
                    | [ |- interp _ (![?P] _ ---> ![?Q] _)%PropX ] =>
                      let H := fresh in assert (P ===> Q); [ | rewrite sepFormula_eq in *; apply H ]
                  end.

Notation "'badt' name p 'end'" :=
  {| FName := name;
    FPrecondition := (fun s => ![ p s#Rp ] s)%PropX;
    FBody := Diverge;
    FVars := nil;
    FReserved := 0 |}
  (no associativity, at level 95, name at level 0, p at level 0, only parsing) : SPfuncs_scope.

Lemma memoryIn'_irrel : forall ls m m',
  List.Forall (fun a => m a = m' a) ls
  -> memoryIn' m ls = memoryIn' m' ls.
  induction ls; inversion 1; subst; simpl; intuition.
  f_equal; auto.
Qed.

Lemma memoryIn'_memoryOut' : forall ls (m : smem' ls),
  NoDup ls
  -> memoryIn' (memoryOut' m) ls = m.
  induction m; inversion 1; subst; simpl; intuition.
  f_equal.
  unfold H.mem_get, ReadByte.
  destruct (weq x x); tauto.
  erewrite memoryIn'_irrel.
  eauto.
  apply Forall_forall; intros.
  destruct (weq x0 x).
  subst x; tauto.
  auto.
Qed.

Theorem memoryIn_memoryOut : forall m, memoryIn (memoryOut m) = m.
  intros; apply memoryIn'_memoryOut'; apply H.NoDup_all_addr.
Qed.
