Require Import Arith AutoSep Bags Malloc Queue.

Set Implicit Arguments.


Require Import DepList.

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

(* What does it mean for a program counter to be valid for a suspended thread? *)

Definition susp (sc pc sp : W) : HProp := fun s m =>
  (Ex pc_sched : W, [| s.(Labels) ("scheduler"!"ADT")%SP = Some pc_sched |]
    /\ ExX (* sched *) : settings * state, Cptr pc_sched #0
    /\ ExX (* pre *) : settings * state, Cptr pc #0
    /\ ExX (* inv *) : settings * smem, #0 (s, m)
    /\ Al st : settings * state,
    ![ #0 * ##2 sc * ^[mallocHeap 0] ] st
    /\ [| st#Sp = sp |]
    ---> #1 st)%PropX.

Definition predIn (P : settings * state -> PropX W (settings * state)) (sc : W) : HProp :=
  fun stn sm => P (stateOut (stn, sm) sc).

Lemma susp_intro : forall specs sc pc sp P stn st,
  (exists pc_sched, stn.(Labels) ("scheduler"!"ADT")%SP = Some pc_sched
    /\ exists sched, specs pc_sched = Some (fun x => sched x)
      /\ exists pre, specs pc = Some (fun x => pre x)
        /\ exists inv, interp specs (![ inv * P ] (stn, st))
          /\ forall stn_st, interp specs (![ inv * predIn sched sc * mallocHeap 0 ] stn_st
            /\ [| stn_st#Sp = sp |]
            ---> pre stn_st)%PropX)
  -> interp specs (![ susp sc pc sp * P ] (stn, st)).
  cptr.
Qed.

Local Hint Resolve split_a_semp_a semp_smem_emp.

Ltac make_Himp := match goal with
                    | [ |- interp _ (![?P] _ ---> ![?Q] _)%PropX ] =>
                      let H := fresh in assert (P ===> Q); [ | rewrite sepFormula_eq; apply H ]
                  end.

Lemma susp_elim : forall specs sc pc sp P stn st,
  interp specs (![ susp sc pc sp * P ] (stn, st))
  -> (exists pc_sched, stn.(Labels) ("scheduler"!"ADT")%SP = Some pc_sched
    /\ exists sched, specs pc_sched = Some (fun x => sched x)
      /\ exists pre, specs pc = Some (fun x => pre x)
        /\ exists inv, interp specs (![ inv * P ] (stn, st))
          /\ forall stn_st, interp specs (![ inv * predIn sched sc * mallocHeap 0 ] stn_st
            /\ [| stn_st#Sp = sp |]
            ---> pre stn_st)%PropX).
  cptr.
  propxFo; eauto.
  descend; eauto.
  rewrite <- sepFormula_eq; descend.
  step auto_ext.
  make_Himp.
  apply Himp_refl.
Qed.



Inductive mergeSusp : Prop := MS.
Inductive splitSusp : Prop := SS.

Hint Constructors mergeSusp splitSusp.

Module Type SCHED.
  Parameter susps : bag -> W -> HProp.
  Parameter sched : W -> HProp.

  Axiom sched_extensional : forall sc, HProp_extensional (sched sc).

  Axiom susps_empty_bwd : forall sc, Emp ===> susps empty sc.
  Axiom susps_add_bwd : forall sc b pc sp, pc = pc -> mergeSusp -> susp sc pc sp * susps b sc ===> susps (b %+ (pc, sp)) sc.
  Axiom susps_del_fwd : forall sc b pc sp, (pc, sp) %in b -> susps b sc ===> susp sc pc sp * susps (b %- (pc, sp)) sc.

  (* Below, the extra [locals] is a temporary stack for the scheduler to use during sensitive
   * stack manipulations when the threads' own stacks may not be safe to touch. *)

  Axiom sched_fwd : forall sc, sched sc ===> Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
    * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
    * queue b p * susps b sc * any.

  Axiom sched_bwd : forall sc, (Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
    * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
    * queue b p * susps b sc * any) ===> sched sc.
End SCHED.

Module Sched : SCHED.
  Open Scope Sep_scope.

  Definition susps (b : bag) (sc : W) : HProp :=
    starB (fun p => susp sc (fst p) (snd p)) b.

  Theorem susps_empty_bwd : forall sc, Emp ===> susps empty sc.
    intros; apply starB_empty_bwd.
  Qed.

  Theorem susps_add_bwd : forall sc b pc sp, pc = pc -> mergeSusp -> susp sc pc sp * susps b sc ===> susps (b %+ (pc, sp)) sc.
    intros; eapply Himp_trans; [ | apply starB_add_bwd ].
    unfold susps; simpl.
    apply Himp_star_comm.
  Qed.

  Theorem susps_del_fwd : forall sc b pc sp, (pc, sp) %in b -> susps b sc ===> susp sc pc sp * susps (b %- (pc, sp)) sc.
    intros; eapply Himp_trans; [ apply starB_del_fwd; eauto | apply Himp_refl ].
  Qed.

  Definition sched (sc : W) : HProp :=
    Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
      * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
      * queue b p * susps b sc * any.

  Theorem sched_extensional : forall sc, HProp_extensional (sched sc).
    reflexivity.
  Qed.

  Theorem sched_fwd : forall sc, sched sc ===> Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
    * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
    * queue b p * susps b sc * any.
    unfold sched; sepLemma.
  Qed.

  Theorem sched_bwd : forall sc, (Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
    * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
    * queue b p * susps b sc * any) ===> sched sc.
    unfold sched; sepLemma.
  Qed.
End Sched.

Import Sched.
Export Sched.
Hint Immediate sched_extensional.

Definition hints : TacPackage.
  prepare (sched_fwd, create_stack) (sched_bwd, susps_empty_bwd, susps_add_bwd).
Defined.

(* What is a valid initial code pointer for a thread, given the requested stack size? *)

Definition starting (sc pc : W) (ss : nat) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ [| semp m |]
    /\ Al st : settings * state, Al vs,
      ![ ^[locals ("rp" :: "sc" :: nil) vs ss st#Sp * sched sc * mallocHeap 0] ] st
      /\ [| sel vs "sc" = sc |]
      ---> #0 st)%PropX.

Lemma starting_intro : forall specs sc pc ss P stn st,
  (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs, interp specs (![ locals ("rp" :: "sc" :: nil) vs ss stn_st#Sp
      * sched sc * mallocHeap 0 ] stn_st
    /\ [| sel vs "sc" = sc |]
    ---> pre stn_st)%PropX)
  -> interp specs (![ starting sc pc ss * P ] (stn, st)).
  cptr.
Qed.

Lemma starting_elim : forall specs sc pc ss P stn st,
  interp specs (![ starting sc pc ss * P ] (stn, st))
  -> (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs, interp specs (![ locals ("rp" :: "sc" :: nil) vs ss stn_st#Sp
      * sched sc * mallocHeap 0 ] stn_st
    /\ [| sel vs "sc" = sc |]
    ---> pre stn_st)%PropX).
  cptr.
  generalize (split_semp _ _ _ H0 H); intros; subst; auto.
  rewrite <- sepFormula_eq; descend; step auto_ext.
  make_Himp.
  apply Himp_refl.
  assumption.
Qed.


Notation "'badt' name p 'end'" :=
  {| FName := name;
    FPrecondition := (fun s => ![ p s#Rp ] s)%PropX;
    FBody := Diverge;
    FVars := nil;
    FReserved := 0 |}
  (no associativity, at level 95, name at level 0, p at level 0, only parsing) : SPfuncs_scope.

Definition initS : spec := SPEC reserving 12
  PRE[_] mallocHeap 0
  POST[R] sched R * mallocHeap 0.

Definition spawnWithStackS : spec := SPEC("sc", "pc", "sp") reserving 14
  PRE[V] sched (V "sc") * susp (V "sc") (V "pc") (V "sp") * mallocHeap 0
  POST[_] sched (V "sc") * mallocHeap 0.

Definition spawnS : spec := SPEC("sc", "pc", "ss") reserving 18
  PRE[V] [| V "ss" >= $2 |] * sched (V "sc") * starting (V "sc") (V "pc") (wordToNat (V "ss") - 2) * mallocHeap 0
  POST[_] sched (V "sc") * mallocHeap 0.

Definition exitS : spec := SPEC("sc") reserving 12
  PREonly[V] sched (V "sc") * mallocHeap 0.

Definition yieldS : spec := SPEC("sc") reserving 19
  PRE[V] sched (V "sc") * mallocHeap 0
  POST[_] sched (V "sc") * mallocHeap 0.

(* Next, some hijinks to prevent unnecessary unfolding of distinct memory cells for the scheduler's stack. *)

Definition stackSize := 21.

Lemma stackSize_bound : natToW stackSize >= natToW 2.
  unfold stackSize; auto.
Qed.

Hint Immediate stackSize_bound.

Lemma stackSize_split : stackSize = length ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) + 14.
  reflexivity.
Qed.

Opaque stackSize.

Definition yieldInvariantCont (pre : vals -> W -> qspec) (rpStashed : bool) (adjustSp : W -> W)
  (ns : list string) (res : nat) : assert :=
  st ~> let sp := adjustSp st#Sp in
    Ex vs, qspecOut (pre (sel vs) st#Rv) (fun pre =>
      ![ ^[locals ("rp" :: ns) vs res sp * pre] ] st).

Notation "'PREy' [ vs ] pre" := (yieldInvariantCont (fun vs _ => pre%qspec%Sep))
  (at level 89).

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS],
    "queue"!"init" @ [Queue.initS], "queue"!"isEmpty" @ [isEmptyS],
    "queue"!"enqueue" @ [enqueueS], "queue"!"dequeue" @ [dequeueS] ]]
  bmodule "scheduler" {{
    badt "ADT"
      sched
    end with bfunction "init"("q", "sp", "r") [initS]
      "q" <-- Call "queue"!"init"()
      [PRE[_, R] mallocHeap 0
       POST[R'] Ex sp, Ex vs, (R' ==*> R, sp) * (R' ^+ $8) =?> 2
         * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
         * mallocHeap 0];;

      "sp" <-- Call "malloc"!"malloc"(0, stackSize)
      [PRE[V, R] R =?> stackSize * mallocHeap 0
        POST[R'] Ex vs, (R' ==*> V "q", R) * (R' ^+ $8) =?> 2 * mallocHeap 0
         * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 R];;

      Assert [PRE[V] mallocHeap 0
        POST[R] (R ==*> V "q", V "sp") * (R ^+ $8) =?> 2 * mallocHeap 0];;

      "r" <-- Call "malloc"!"malloc"(0, 4)
      [PRE[V, R] R =?> 4
       POST[R'] [| R' = R |] * (R ==*> V "q", V "sp") * (R ^+ $8) =?> 2 ];;
      "r" *<- "q";;
      "r" + 4 *<- "sp";;
      Return "r"
    end with bfunction "spawnWithStack"("sc", "pc", "sp") [spawnWithStackS]
      "sc" <-* "sc";;
      Note [mergeSusp];;
      Call "queue"!"enqueue"("sc", "pc", "sp")
      [Al b, Al sc,
        PRE[V] susps (b %+ (V "pc", V "sp")) sc
         POST[_] susps (b %+ (V "pc", V "sp")) sc];;
      Return 0
    end with bfunction "spawn"("sc", "pc", "ss") [spawnS]
      "ss" <-- Call "malloc"!"malloc"(0, "ss")
      [Al ss,
        PRE[V, R] sched (V "sc") * starting (V "sc") (V "pc") (ss - 2) * mallocHeap 0
          * R =?> ss * [| (ss >= 2)%nat |]
        POST[_] sched (V "sc") * mallocHeap 0];;

      Assert [Al ss, Al vs,
        PRE[V] sched (V "sc") * starting (V "sc") (V "pc") ss * mallocHeap 0
          * locals ("rp" :: "sc" :: nil) vs ss (V "ss")
        POST[_] sched (V "sc") * mallocHeap 0];;

      (* Save pointer to scheduler data structure in new thread's stack. *)
      "ss" + 4 *<- "sc";;

      Call "scheduler"!"spawnWithStack"("sc", "pc", "ss")
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
    end with bfunctionNoRet "exit"("sc", "q", "r") [exitS]
      "q" <-* "sc";;
      "r" <-- Call "queue"!"isEmpty"("q")
      [Al q, Al tsp, Al vs,
        PREonly[V, R] [| (q %= empty) \is R |]
          * queue q (V "q") * (V "sc" ==*> V "q", tsp)
          * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 tsp          
          * (V "sc" ^+ $8) =?> 2 * susps q (V "sc") * mallocHeap 0];;

      If ("r" = 1) {
        (* No threads left to run.  Let's loop forever! *)
        Diverge
      } else {
        (* Pick a thread to switch to. *)

        "r" <- "sc" + 8;;
        Call "queue"!"dequeue"("q", "r")
        [Al q, Al tsp, Al pc, Al sp, Al vs,
          PREonly[V] [| (pc, sp) %in q |] * queue (q %- (pc, sp)) (V "q")
            * susps (q %- (pc, sp)) (V "sc") * susp (V "sc") pc sp
            * (V "sc" ==*> V "q", tsp, pc, sp) * mallocHeap 0
            * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 tsp];;

        Rp <-* "sc" + 8;;
        Sp <-* "sc" + 12;;
        IGoto* [("scheduler","ADT")] Rp
      }
    end with bfunction "yield"("sc", "q", "curPc", "curSp", "newPc", "newSp") [yieldS]
      "q" <-* "sc";;
      (* Using "curPc" as a temporary before getting to its primary use... *)
      "curPc" <-- Call "queue"!"isEmpty"("q")
      [Al q, Al tsp, Al vs,
        PRE[V, R] [| (q %= empty) \is R |]
          * queue q (V "q") * (V "sc" ==*> V "q", tsp) * (V "sc" ^+ $8) =?> 2 * susps q (V "sc") * mallocHeap 0
          * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 tsp * any
        POST[_] sched (V "sc") * mallocHeap 0];;

      If ("curPc" = 1) {
        (* No other threads to run.  Simply returning to caller acts like a yield. *)
        Rp <- $[Sp+0];;
        IGoto* [("scheduler","ADT")] Rp
      } else {
        (* Pick a thread to switch to. *)
        "curPc" <- "sc" + 8;;
        Call "queue"!"dequeue"("q", "curPc")
        [Al q, Al tsp, Al vs, Al pc, Al sp,
          PRE[V] [| (pc, sp) %in q |] * queue (q %- (pc, sp)) (V "q")
            * susps (q %- (pc, sp)) (V "sc") * susp (V "sc") pc sp
            * (V "sc" ==*> V "q", tsp, pc, sp) * mallocHeap 0
            * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 tsp * any
          POST[_] sched (V "sc") * mallocHeap 0];;
        "newPc" <-* "sc" + 8;;
        "newSp" <-* "sc" + 12;;

        Assert [PRE[V] susp (V "sc") (V "newPc") (V "newSp") * sched (V "sc") * mallocHeap 0
          POST[_] sched (V "sc") * mallocHeap 0];;

        (* Initialize the temporary stack with data we will need, then switch to using it as our stack. *)
        "curPc" <-* "sc" + 4;;
        "q" <-* "sc";;
        "curPc" + 4 *<- "sc";;
        "curPc" + 8 *<- "q";;
        "curPc" + 12 *<- $[Sp+0];;
        "curPc" + 16 *<- Sp;;
        "curPc" + 20 *<- "newPc";;
        "curPc" + 24 *<- "newSp";;
        Sp <- "curPc";;

        Assert [PREy[V] Ex sp, Ex b, (V "sc" ==*> V "q", sp) * (V "sc" ^+ $8) =?> 2
          * queue b (V "q") * susps b (V "sc") * any * mallocHeap 0
          * susp (V "sc") (V "newPc") (V "newSp") * susp (V "sc") (V "curPc") (V "curSp")];;

        Note [mergeSusp];;

        (* Enqueue current thread; note that variable references below resolve in the temporary stack. *)
        Call "queue"!"enqueue"("q", "curPc", "curSp")
        [PREy[V] Ex b, Ex p, Ex sp, (V "sc" ==*> p, sp) * (V "sc" ^+ $8) =?> 2
          * queue b p * susps b (V "sc") * any
          * mallocHeap 0 * susp (V "sc") (V "newPc") (V "newSp")];;

        (* Jump to dequeued thread. *)
        "sc" + 4 *<- Sp;;
        Rp <- "newPc";;
        Sp <- "newSp";;
        IGoto* [("scheduler","ADT")] Rp
      }
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Ltac t := solve [ sep hints; try apply any_easy;
  try (apply himp_star_frame; [ reflexivity | apply susps_del_fwd; assumption ]);
    eauto ].

(*Ltac t := abstract (sep hints; try apply any_easy;
  try (apply himp_star_frame; [ reflexivity | apply susps_del_fwd; assumption ]);
    eauto).*)

Lemma wordBound : forall w : W,
  natToW 2 <= w
  -> (wordToNat w >= 2)%nat.
  intros; pre_nomega;
    rewrite wordToNat_natToWord_idempotent in * by reflexivity; assumption.
Qed.

Local Hint Immediate wordBound.
  
Hint Rewrite <- minus_n_O : sepFormula.

Lemma Labels_cong : forall stn stn' l pc,
  Labels stn l = Some pc
  -> Labels stn' = Labels stn
  -> Labels stn' l = Some pc.
  intros; rewrite H0; auto.
Qed.

Hint Immediate Labels_cong.

Lemma memoryIn'_irrel : forall ls m m',
  List.Forall (fun a => m a = m' a) ls
  -> memoryIn' m ls = memoryIn' m' ls.
  induction ls; inversion 1; subst; simpl; intuition.
  f_equal; auto.
Qed.

Lemma memoryIn'_memoryOut' : forall ls (m : smem' ls),
  NoDup ls
  -> memoryIn' (memoryOut' m) ls = m.
  induction m0; inversion 1; subst; simpl; intuition.
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

Theorem ok : moduleOk m.
  vcgen.

  t.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.

  post.
  rewrite stackSize_split in H0.
  assert (NoDup ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)) by NoDup.
  evaluate hints; descend; repeat (step hints; descend); auto.

  t.
  t.
  t.
  t.
  t.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.

  t.
  t.
  t.
  t.
  t.
  t.

  post.
  match goal with
    | [ H : context[?X - 2] |- _ ] =>
      replace X with (length ("rp" :: "sc" :: nil) + (X - length ("rp" :: "sc" :: nil))) in H
  end.
  assert (NoDup ("rp" :: "sc" :: nil)) by NoDup.
  evaluate hints; sep hints; auto.
  evaluate hints; simpl; omega.

  t.

  (* This case ("starting -> susp") will need some more Structured magic. *)
  admit.
  (*post; evaluate auto_ext.
  match goal with
    | [ H : interp _ _ |- _ ] =>
      toFront ltac:(fun P => match P with
                               | starting _ _ _ => idtac
                             end) H;
      apply starting_elim in H; post; descend
  end.
  toFront_conc ltac:(fun P => match P with
                                | susp _ _ _ => idtac
                              end);
  apply susp_intro; descend.
  4: instantiate (4 := locals ("rp" :: "sc" :: nil) (upd x1 "sc" (sel x3 "sc")) x0 (sel x3 "ss")); sep_auto.
  eauto.
  eauto.
  eauto.
  eapply Imply_trans; [ | apply H12 ]; clear H12.
  step auto_ext.
  step auto_ext.
  match goal with
    | [ H : Regs _ Sp = sel _ "ss" |- _ ] => rewrite H
  end; make_Himp; apply Himp_refl.
  auto.
  step auto_ext.
  sep_auto; auto.*)

  t.
  t.
  t.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  
  post; evaluate hints.
  match goal with
    | [ H : interp _ _ |- _ ] =>
      toFront ltac:(fun P => match P with
                               | susp _ _ _ => idtac
                             end) H;
      apply susp_elim in H; post
  end.
  descend.
  step auto_ext.
  match goal with
    | [ H : _ |- _ ] => eapply (Imply_sound (H _)); clear H; eauto
  end.
  propxFo.
  unfold labl in H7; rewrite H1 in H7; injection H7; clear H1 H7; intros; subst.
  rewrite H9 in H2; injection H2; clear H2 H9; intros; subst.
  assert (interp specs (![x12 * sched (sel x8 "sc") * mallocHeap 0] (stn, st)
    ---> ![x12 * predIn x10 (sel x8 "sc") * mallocHeap 0] (stn, st))%PropX).
  make_Himp; repeat apply Himp_star_frame; try apply Himp_refl.
  unfold Himp, himp; intros.
  unfold predIn.
  change x10 with (fun x => x10 x).
  rewrite H.
  rewrite sepFormula_eq; unfold sepFormula_def; simpl.

  rewrite memoryIn_memoryOut.
  apply Imply_refl.
  apply (Imply_sound H0); clear H0 H.
  step hints; apply any_easy.

  t.
  t.
  t.
  t.

  post.
  evaluate hints.
  descend.
  step hints.
  step hints.
  step hints.
  descend; step hints.
  instantiate (2 := x7).
  instantiate (3 := upd x1 "q" x8).
  descend; cancel hints.
  sep hints.
  sep hints.
  sep hints; auto.

  t.
  t.
  t.
  t.
  t.

  post; evaluate hints; descend.
  step hints.
  2: step hints.
  eauto.
  step hints.
  descend; step hints.
  instantiate (2 := x2).
  instantiate (4 := upd (upd x5 "curPc" (Regs x0 Rv)) "curPc" (sel x5 "sc" ^+ $8)).
  descend; cancel hints.
  step hints.
  apply himp_star_frame; [ reflexivity | apply susps_del_fwd; assumption ].
  step hints.
  sep hints; auto.

  t.
  t.
  t.
  t.

  (* Needs more Structured magic to get ahold of a fact about ADT *)
  admit.
  (*post.
  evaluate hints.
  descend.
  instantiate (2 := upd (upd (upd (upd (upd (upd x5 "sc" (sel x1 "sc")) "q" x7) "curPc"
    (sel x1 "rp")) "curSp" (Regs x Sp)) "newPc" (sel x1 "newPc")) "newSp" (sel x1 "newSp")); descend.
  toFront_conc ltac:(fun P => match P with
                                | susp _ (sel _ "rp") _ => idtac
                              end).
  apply susp_intro; descend; eauto.
  match goal with
    | [ _ : context[locals ?ns ?v ?a (Regs ?st Sp)] |- interp specs (![?P * _] _) ] =>
      equate P (locals ns v a (Regs st Sp) * (fun x y => x0 (x, y)))%Sep
  end.
  step hints.
  big_imp.
  repeat (apply andL; (apply injL || apply cptrL); intro).
  apply andL; apply swap; apply andL; apply injL; intro.
  apply unandL.
  simpl; repeat apply andR; try ((apply injR || apply cptrR); simpl; eauto).
  apply andL; apply swap; apply implyR.
  rewrite H7; instantiate (1 := fun p => sched_ (fst p) (snd p)); refl.
  apply andL; apply implyR.
  descend.
  rewrite substH_in3; descend.
  instantiate (1 := upd (upd x1 "curPc" x6) "q" x7).
  clear.
  step auto_ext.*)

  t.
  t.

  post; evaluate hints; descend.
  instantiate (3 := x2).
  step hints.
  step hints.
  step hints.
  unfold yieldInvariantCont; descend; step hints.
  instantiate (5 := x2 %+ (sel x0 "curPc", sel x0 "curSp")).
  descend; step hints.

  t.
  t.

  post; evaluate hints.
  match goal with
    | [ H : interp _ _ |- _ ] =>
      toFront ltac:(fun P => match P with
                               | susp _ _ _ => idtac
                             end) H;
      apply susp_elim in H; post
  end.
  descend.
  step auto_ext.
  match goal with
    | [ H : _ |- _ ] => eapply (Imply_sound (H _)); eauto
  end.
  unfold labl in H7; rewrite H1 in H7; injection H7; clear H1 H7; intros; subst.
  rewrite H8 in H2; injection H2; clear H2 H8; intros; subst.
  assert (interp specs (![x10 * sched (sel x2 "sc") * mallocHeap 0] (stn, st)
    ---> ![x10 * predIn x8 (sel x2 "sc") * mallocHeap 0] (stn, st))%PropX).
  make_Himp; repeat apply Himp_star_frame; try apply Himp_refl.
  unfold Himp, himp; intros.
  unfold predIn.
  change x8 with (fun x => x8 x).
  rewrite H1.
  rewrite sepFormula_eq; unfold sepFormula_def; simpl.
  rewrite memoryIn_memoryOut.
  apply Imply_refl.
  propxFo.
  apply (Imply_sound H2); clear H2 H1.
  step hints.
Qed.

Transparent stackSize.
