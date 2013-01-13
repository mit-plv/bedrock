Require Import Arith AutoSep Bags Malloc Queue RecPred.
Import W_W_Bag.

Set Implicit Arguments.


Module Type S.
  Variable globalInv : W -> hpropB ((settings * state : Type)%type :: nil).
End S.

Module Make(M : S).
Import M.

(* What does it mean for a program counter to be valid for a suspended thread? *)

Definition susp (sc pc sp : W) : HProp := fun s m =>
  (Ex pc_tq : W, [| s.(Labels) ("threadq"!"ADT")%SP = Some pc_tq |]
    /\ ExX (* tq *) : settings * state, Cptr pc_tq #0
    /\ ExX (* pre *) : settings * state, Cptr pc #0
    /\ ExX (* inv *) : settings * smem, #0 (s, m)
    /\ Al st : settings * state,
    ![ #0 * ##2 sc * (fun x y => Lift (Lift (globalInv sc x y))) * ^[mallocHeap 0] ] st
    /\ [| st#Sp = sp |]
    ---> #1 st)%PropX.

Lemma susp_intro : forall specs sc pc sp P stn st,
  (exists pc_tq, stn.(Labels) ("threadq"!"ADT")%SP = Some pc_tq
    /\ exists tq, specs pc_tq = Some (fun x => tq x)
      /\ exists pre, specs pc = Some (fun x => pre x)
        /\ exists inv, interp specs (![ inv * P ] (stn, st))
          /\ forall stn_st, interp specs (![ inv * predIn tq sc * substH (globalInv sc) tq * mallocHeap 0 ] stn_st
            /\ [| stn_st#Sp = sp |]
            ---> pre stn_st)%PropX)
  -> interp specs (![ susp sc pc sp * P ] (stn, st)).
  cptr.
Qed.

Lemma susp_elim : forall specs sc pc sp P stn st,
  interp specs (![ susp sc pc sp * P ] (stn, st))
  -> (exists pc_tq, stn.(Labels) ("threadq"!"ADT")%SP = Some pc_tq
    /\ exists tq, specs pc_tq = Some (fun x => tq x)
      /\ exists pre, specs pc = Some (fun x => pre x)
        /\ exists inv, interp specs (![ inv * P ] (stn, st))
          /\ forall stn_st, interp specs (![ inv * predIn tq sc * substH (globalInv sc) tq * mallocHeap 0 ] stn_st
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

Module Type TQ.
  Parameter susps : bag -> W -> HProp.
  Parameter tq : W -> HProp.

  Axiom tq_extensional : forall sc, HProp_extensional (tq sc).

  Axiom susps_empty_bwd : forall sc, Emp ===> susps empty sc.
  Axiom susps_add_bwd : forall sc b pc sp, pc = pc -> mergeSusp -> susp sc pc sp * susps b sc ===> susps (b %+ (pc, sp)) sc.
  Axiom susps_del_fwd : forall sc b pc sp, (pc, sp) %in b -> susps b sc ===> susp sc pc sp * susps (b %- (pc, sp)) sc.

  (* Below, the extra [locals] is a temporary stack for the threadq to use during sensitive
   * stack manipulations when the threads' own stacks may not be safe to touch. *)

  Axiom tq_fwd : forall sc, tq sc ===> Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
    * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
    * queue b p * susps b sc * any.

  Axiom tq_bwd : forall sc, (Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
    * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
    * queue b p * susps b sc * any) ===> tq sc.
End TQ.

Module Tq : TQ.
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

  Definition tq (sc : W) : HProp :=
    Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
      * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
      * queue b p * susps b sc * any.

  Theorem tq_extensional : forall sc, HProp_extensional (tq sc).
    reflexivity.
  Qed.

  Theorem tq_fwd : forall sc, tq sc ===> Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
    * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
    * queue b p * susps b sc * any.
    unfold tq; sepLemma.
  Qed.

  Theorem tq_bwd : forall sc, (Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
    * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
    * queue b p * susps b sc * any) ===> tq sc.
    unfold tq; sepLemma.
  Qed.
End Tq.

Import Tq.
Export Tq.
Hint Immediate tq_extensional.

Definition hints : TacPackage.
  prepare (tq_fwd, create_stack) (tq_bwd, susps_empty_bwd, susps_add_bwd).
Defined.

(* What is a valid initial code pointer for a thread, given the requested stack size? *)

Definition ginv sc := substH (globalInv sc) (predOut tq).

Definition starting (sc pc : W) (ss : nat) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ [| semp m |]
    /\ Al st : settings * state, Al vs,
      ![ ^[locals ("rp" :: "sc" :: nil) vs ss st#Sp * tq sc * ginv sc * mallocHeap 0] ] st
      /\ [| sel vs "sc" = sc |]
      ---> #0 st)%PropX.

Local Hint Resolve split_a_semp_a semp_smem_emp.

Lemma starting_intro : forall specs sc pc ss P stn st,
  (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs, interp specs (![ locals ("rp" :: "sc" :: nil) vs ss stn_st#Sp
      * tq sc * ginv sc * mallocHeap 0 ] stn_st
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
      * tq sc * ginv sc * mallocHeap 0 ] stn_st
    /\ [| sel vs "sc" = sc |]
    ---> pre stn_st)%PropX).
  cptr.
  generalize (split_semp _ _ _ H0 H); intros; subst; auto.
  rewrite <- sepFormula_eq; descend; step auto_ext.
  make_Himp.
  apply Himp_refl.
  assumption.
Qed.


Definition initS : spec := SPEC reserving 12
  PRE[_] mallocHeap 0
  POST[R] tq R * mallocHeap 0.

Definition spawnWithStackS : spec := SPEC("sc", "pc", "sp") reserving 14
  PRE[V] tq (V "sc") * susp (V "sc") (V "pc") (V "sp") * mallocHeap 0
  POST[_] tq (V "sc") * mallocHeap 0.

Definition spawnS : spec := SPEC("sc", "pc", "ss") reserving 18
  PRE[V] [| V "ss" >= $2 |] * tq (V "sc") * starting (V "sc") (V "pc") (wordToNat (V "ss") - 2) * mallocHeap 0
  POST[_] tq (V "sc") * mallocHeap 0.

Definition exitS : spec := SPEC("sc") reserving 12
  PREonly[V] tq (V "sc") * ginv (V "sc") * mallocHeap 0.

Definition yieldS : spec := SPEC("sc") reserving 19
  PRE[V] tq (V "sc") * ginv (V "sc") * mallocHeap 0
  POST[_] tq (V "sc") * ginv (V "sc") * mallocHeap 0.

(* Next, some hijinks to prevent unnecessary unfolding of distinct memory cells for the threadq's stack. *)

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

Local Notation "'PREy' [ vs ] pre" := (yieldInvariantCont (fun vs _ => pre%qspec%Sep))
  (at level 89).

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS],
    "queue"!"init" @ [Queue.initS], "queue"!"isEmpty" @ [isEmptyS],
    "queue"!"enqueue" @ [enqueueS], "queue"!"dequeue" @ [dequeueS] ]]
  bmodule "threadq" {{
    badt "ADT"
      tq
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
        PRE[V, R] tq (V "sc") * starting (V "sc") (V "pc") (ss - 2) * mallocHeap 0
          * R =?> ss * [| (ss >= 2)%nat |]
        POST[_] tq (V "sc") * mallocHeap 0];;

      Assert [Al ss, Al vs,
        PRE[V] tq (V "sc") * starting (V "sc") (V "pc") ss * mallocHeap 0
          * locals ("rp" :: "sc" :: nil) vs ss (V "ss")
        POST[_] tq (V "sc") * mallocHeap 0];;

      (* Save pointer to threadq data structure in new thread's stack. *)
      "ss" + 4 *<- "sc";;

      Assert* [("threadq","ADT")]
      [PRE[V] tq (V "sc") * susp (V "sc") (V "pc") (V "ss") * mallocHeap 0
       POST[_] tq (V "sc") * mallocHeap 0];;

      Call "threadq"!"spawnWithStack"("sc", "pc", "ss")
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
          * (V "sc" ^+ $8) =?> 2 * susps q (V "sc") * ginv (V "sc") * mallocHeap 0];;

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
            * (V "sc" ==*> V "q", tsp, pc, sp) * ginv (V "sc") * mallocHeap 0
            * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 tsp];;

        Rp <-* "sc" + 8;;
        Sp <-* "sc" + 12;;
        IGoto* [("threadq","ADT")] Rp
      }
    end with bfunction "yield"("sc", "q", "curPc", "curSp", "newPc", "newSp") [yieldS]
      "q" <-* "sc";;
      (* Using "curPc" as a temporary before getting to its primary use... *)
      "curPc" <-- Call "queue"!"isEmpty"("q")
      [Al q, Al tsp, Al vs,
        PRE[V, R] [| (q %= empty) \is R |]
          * queue q (V "q") * (V "sc" ==*> V "q", tsp) * (V "sc" ^+ $8) =?> 2 * susps q (V "sc")
          * ginv (V "sc") * mallocHeap 0
          * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 tsp * any
        POST[_] tq (V "sc") * ginv (V "sc") * mallocHeap 0];;

      If ("curPc" = 1) {
        (* No other threads to run.  Simply returning to caller acts like a yield. *)
        Rp <- $[Sp+0];;
        IGoto* [("threadq","ADT")] Rp
      } else {
        (* Pick a thread to switch to. *)
        "curPc" <- "sc" + 8;;
        Call "queue"!"dequeue"("q", "curPc")
        [Al q, Al tsp, Al vs, Al pc, Al sp,
          PRE[V] [| (pc, sp) %in q |] * queue (q %- (pc, sp)) (V "q")
            * susps (q %- (pc, sp)) (V "sc") * susp (V "sc") pc sp
            * (V "sc" ==*> V "q", tsp, pc, sp) * ginv (V "sc") * mallocHeap 0
            * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 tsp * any
          POST[_] tq (V "sc") * ginv (V "sc") * mallocHeap 0];;
        "newPc" <-* "sc" + 8;;
        "newSp" <-* "sc" + 12;;

        Assert [PRE[V] susp (V "sc") (V "newPc") (V "newSp") * tq (V "sc") * ginv (V "sc") * mallocHeap 0
          POST[_] tq (V "sc") * ginv (V "sc") * mallocHeap 0];;

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

        Assert* [("threadq","ADT")]
        [PREy[V] Ex sp, Ex b, (V "sc" ==*> V "q", sp) * (V "sc" ^+ $8) =?> 2
          * queue b (V "q") * susps b (V "sc") * any * ginv (V "sc") * mallocHeap 0
          * susp (V "sc") (V "newPc") (V "newSp") * susp (V "sc") (V "curPc") (V "curSp")];;

        Note [mergeSusp];;

        (* Enqueue current thread; note that variable references below resolve in the temporary stack. *)
        Call "queue"!"enqueue"("q", "curPc", "curSp")
        [PREy[V] Ex b, Ex p, Ex sp, (V "sc" ==*> p, sp) * (V "sc" ^+ $8) =?> 2
          * queue b p * susps b (V "sc") * any * ginv (V "sc")
          * mallocHeap 0 * susp (V "sc") (V "newPc") (V "newSp")];;

        (* Jump to dequeued thread. *)
        "sc" + 4 *<- Sp;;
        Rp <- "newPc";;
        Sp <- "newSp";;
        IGoto* [("threadq","ADT")] Rp
      }
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Ltac t := abstract (sep hints; try apply any_easy;
  try (apply himp_star_frame; [ reflexivity | apply susps_del_fwd; assumption ]);
    eauto).

Lemma wordBound : forall w : W,
  natToW 2 <= w
  -> (wordToNat w >= 2)%nat.
  intros; pre_nomega;
    rewrite wordToNat_natToWord_idempotent in * by reflexivity; assumption.
Qed.

Local Hint Immediate wordBound.
  
Hint Rewrite <- minus_n_O : sepFormula.

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

  post; evaluate auto_ext.
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
  4: instantiate (4 := locals ("rp" :: "sc" :: nil) (upd x2 "sc" (sel x4 "sc")) x1 (sel x4 "ss")); sep_auto.
  eauto.
  eauto.
  eauto.
  eapply Imply_trans; [ | apply H10 ]; clear H10.
  step auto_ext.
  step auto_ext.
  make_Himp.
  rewrite H9.
  repeat (apply Himp_star_frame; try apply Himp_refl).
  do 3 intro; rewrite sepFormula_eq; unfold predIn, sepFormula_def; simpl.
  rewrite memoryIn_memoryOut; apply Imply_refl.
  rewrite sepFormula_eq; apply Himp_refl.
  auto.
  step auto_ext.
  sep_auto.

  t.
  sep_auto; auto.
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
  change (fun st m => subst (globalInv (sel x8 "sc") st m) x10)
    with (substH (globalInv (sel x8 "sc")) x10).
  assert (interp specs (![x12 * tq (sel x8 "sc") * ginv (sel x8 "sc") * mallocHeap 0] (stn, st)
    ---> ![x12 * predIn x10 (sel x8 "sc") * substH (globalInv (sel x8 "sc")) x10 * mallocHeap 0] (stn, st))%PropX).
  make_Himp; repeat apply Himp_star_frame; try apply Himp_refl.
  unfold Himp, himp; intros.
  unfold predIn.
  change x10 with (fun x => x10 x).
  rewrite H.
  rewrite sepFormula_eq; unfold sepFormula_def; simpl.
  rewrite memoryIn_memoryOut.
  apply Imply_refl.
  unfold substH.
  replace x10 with (predOut tq).
  apply Himp_refl.
  symmetry; rewrite sepFormula_eq in H; assumption.
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
  instantiate (3 := upd (upd x5 "curPc" (Regs x0 Rv)) "curPc" (sel x5 "sc" ^+ $8)).
  descend; cancel hints.
  step hints.
  apply himp_star_frame; [ reflexivity | apply susps_del_fwd; assumption ].
  step hints.
  sep hints; auto.

  t.
  t.
  t.
  t.

  post; evaluate hints.
  descend.
  instantiate (1 := upd (upd (upd (upd (upd (upd x6 "sc" (sel x2 "sc")) "q" x8) "curPc"
    (sel x2 "rp")) "curSp" (Regs x0 Sp)) "newPc" (sel x2 "newPc")) "newSp" (sel x2 "newSp")); descend.
  toFront_conc ltac:(fun P => match P with
                                | susp _ (sel _ "rp") _ => idtac
                              end).
  apply susp_intro; descend; eauto.
  match goal with
    | [ _ : context[locals ?ns ?v ?a (Regs ?st Sp)] |- interp specs (![?P * _] _) ] =>
      equate P (locals ns v a (Regs st Sp) * (fun x y => x1 (x, y)))%Sep
  end.
  step hints.
  step auto_ext.
  step auto_ext.
  match goal with
    | [ |- interp _ (![?P * ?Q * ?R * ?S * ?T] _ ---> _)%PropX ] =>
      let H := fresh in assert (H : P * Q * R * S * T ===> P * Q * tq (sel x2 "sc") * ginv (sel x2 "sc") * T); [
        | eapply Imply_trans; [ rewrite sepFormula_eq in *; apply H | ] ]
  end.
  repeat apply Himp_star_frame; try apply Himp_refl.
  do 3 intro; rewrite sepFormula_eq; unfold sepFormula_def, predIn; simpl.
  rewrite memoryIn_memoryOut; apply Imply_refl.
  rewrite sepFormula_eq; apply Himp_refl.
  match goal with
    | [ |- interp _ (?P ?x ?y ---> _) ] => change (P x y) with (sepFormula_def P (s, s0))
  end; rewrite <- sepFormula_eq.
  instantiate (1 := upd (upd x2 "curPc" x7) "q" x8); clear.
  step auto_ext.

  t.
  t.

  post; evaluate hints; descend.
  instantiate (3 := x2).
  step hints.
  step hints.
  step hints.
  unfold yieldInvariantCont; descend; step hints.
  instantiate (6 := x2 %+ (sel x0 "curPc", sel x0 "curSp")).
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
  change (fun (st0 : ST.settings) (m0 : smem) => subst (globalInv (sel x2 "sc") st0 m0) x8)
    with (substH (globalInv (sel x2 "sc")) x8).
  assert (interp specs (![x10 * tq (sel x2 "sc") * ginv (sel x2 "sc") * mallocHeap 0] (stn, st)
    ---> ![x10 * predIn x8 (sel x2 "sc") * substH (globalInv (sel x2 "sc")) x8 * mallocHeap 0] (stn, st))%PropX).
  make_Himp; repeat apply Himp_star_frame; try apply Himp_refl.
  unfold Himp, himp; intros.
  unfold predIn.
  change x8 with (fun x => x8 x).
  rewrite H1.
  rewrite sepFormula_eq; unfold sepFormula_def; simpl.
  rewrite memoryIn_memoryOut.
  apply Imply_refl.
  unfold ginv.
  replace (predOut tq) with x8.
  apply Himp_refl.
  rewrite sepFormula_eq in *; assumption.
  propxFo.
  apply (Imply_sound H2); clear H2 H1.
  step hints.
Qed.

Transparent stackSize.

End Make.
