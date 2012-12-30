Require Import Arith AutoSep Bags Malloc Queue.

Set Implicit Arguments.


(* What does it mean for a program counter to be valid for a suspended thread? *)

Definition susp (sc pc sp : W) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ ExX (* inv *) : settings * smem, #0 (s, m)
    /\ AlX (* sched *) : settings * smem, AlX (* pre_exit *) : settings * state,
      Al pc_exit : W, Al st : settings * state,
      [| s.(Labels) ("scheduler"!"exit")%SP = Some pc_exit |]
      /\ [| (fst st).(Labels) = s.(Labels) |]
      /\ Cptr pc_exit #0
      /\ (AlX (* fr_exit *) : settings * smem, Al st', Al vs,
        ![^[locals ("rp" :: "sc" :: nil) vs 12 st'#Sp]
          * (#2 * #0 * ^[mallocHeap 0])] st'
        /\ [| sel vs "sc" = sc |]
        /\ [| (fst st').(Labels) = s.(Labels) |]
        ---> #1 st')
      /\ [| st#Sp = sp |]
      /\ ![ #2 * #1 * ^[mallocHeap 0] ] st
      ---> #3 st)%PropX.

(* What is a valid initial code pointer for a thread, given the requested stack size? *)

Definition starting (sc pc : W) (ss : nat) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ [| semp m |]
    /\ AlX (* sched *) : settings * smem, AlX (* pre_exit *) : settings * state,
      Al pc_exit : W, Al st : settings * state, Al vs : vals,
      [| s.(Labels) ("scheduler"!"exit")%SP = Some pc_exit |]
      /\ [| (fst st).(Labels) = s.(Labels) |]
      /\ Cptr pc_exit #0
      /\ (AlX (* fr_exit *) : settings * smem, Al st', Al vs',
        ![^[locals ("rp" :: "sc" :: nil) vs' 12 st'#Sp]
          * (#2 * #0 * ^[mallocHeap 0])] st'
        /\ [| sel vs' "sc" = sc |]
        /\ [| (fst st').(Labels) = s.(Labels) |]
        ---> #1 st')
      /\ ![ ^[locals ("rp" :: "sc" :: nil) vs ss st#Sp] * #1 * ^[mallocHeap 0] ] st
      /\ [| sel vs "sc" = sc |]
      ---> #2 st)%PropX.

Lemma susp_intro : forall specs sc pc sp P stn st,
  (exists pre, specs pc = Some (fun x => pre x)
    /\ exists inv, interp specs (![ inv * P ] (stn, st))
      /\ forall sched_ pre_exit pc_exit stn_st',
        interp specs ([| stn.(Labels) ("scheduler"!"exit")%SP = Some pc_exit |]
          /\ [| (fst stn_st').(Labels) = stn.(Labels) |]
          /\ Cptr pc_exit (fun x => pre_exit x)
          /\ (AlX, Al stn_st'', Al vs : vals,
            ![^[locals ("rp" :: "sc" :: nil) vs 12 stn_st''#Sp]
              * (^[sched_] * #0 * ^[mallocHeap 0])] stn_st''
            /\ [| sel vs "sc" = sc |]
            /\ [| (fst stn_st'').(Labels) = stn.(Labels) |]
            ---> Lift (pre_exit stn_st''))
          /\ [| stn_st'#Sp = sp |]
          /\ ![ inv * sched_ * mallocHeap 0 ] stn_st'
          ---> pre stn_st')%PropX)
  -> interp specs (![ susp sc pc sp * P ] (stn, st)).
  cptr.
  instantiate (1 := fun x y => a (x, y)).
  imp; propxFo; eauto.
Qed.

Local Hint Resolve split_a_semp_a semp_smem_emp.

Lemma starting_intro : forall specs sc pc ss P stn st,
  (exists pre, specs pc = Some pre
    /\ interp specs (![ P ] (stn, st))
    /\ forall sched_ pre_exit pc_exit stn_st' vs,
      interp specs ([| stn.(Labels) ("scheduler"!"exit")%SP = Some pc_exit |]
        /\ [| (fst stn_st').(Labels) = stn.(Labels) |]
        /\ Cptr pc_exit (fun x => pre_exit x)
        /\ [| sel vs "sc" = sc |]
        /\ ![ locals ("rp" :: "sc" :: nil) vs ss stn_st'#Sp * sched_ * mallocHeap 0] stn_st'
        /\ (AlX , Al stn_st'', Al vs' : vals,
          ![^[locals ("rp" :: "sc" :: nil) vs' 12 stn_st''#Sp]
            * (^[sched_] * #0 * ^[mallocHeap 0])] stn_st''
          /\ [| sel vs' "sc" = sc |]
          /\ [| (fst stn_st'').(Labels) = stn.(Labels) |]
          ---> Lift (pre_exit stn_st''))
        ---> pre stn_st')%PropX)
  -> interp specs (![ starting sc pc ss * P ] (stn, st)).
  cptr.
  instantiate (2 := fun x y => a (x, y)).
  imp; propxFo; eauto.
Qed.

Lemma susp_elim : forall specs sc pc sp P stn st,
  interp specs (![ susp sc pc sp * P ] (stn, st))
  -> exists pre, specs pc = Some pre
    /\ exists inv, interp specs (![ inv * P ] (stn, st))
      /\ forall sched_ pre_exit pc_exit stn_st',
        stn.(Labels) ("scheduler"!"exit")%SP = Some pc_exit
        -> (fst stn_st').(Labels) = stn.(Labels)
        -> specs pc_exit = Some (fun x => pre_exit x)
        -> (forall fr_exit stn_st'' vs, interp specs (![^[locals ("rp" :: "sc" :: nil) vs 12 stn_st''#Sp]
          * (sched_ * (fun s m => fr_exit s m) * ^[mallocHeap 0])] stn_st''
        /\ [| sel vs "sc" = sc |]
        /\ [| (fst stn_st'').(Labels) = stn.(Labels) |]
        ---> pre_exit stn_st'')%PropX)
        -> stn_st'#Sp = sp
        -> interp specs (![ inv * sched_ * mallocHeap 0 ] stn_st')
        -> interp specs (pre stn_st').
  cptr.
  propxFo; eauto.
  post; eauto.
  big_imp.
  instantiate (1 := x3).
  instantiate (1 := fun x y => a (x, y)).
  instantiate (1 := fun p => sched_ (fst p) (snd p)).
  refl.
  post; rewrite sepFormula_eq; propxFo; eauto 10.
Qed.

Lemma starting_elim : forall specs sc pc ss P stn st,
  interp specs (![ starting sc pc ss * P ] (stn, st))
  -> exists pre, specs pc = Some pre
    /\ interp specs (![ P ] (stn, st))
    /\ forall sched_ pre_exit pc_exit stn_st' vs,
      interp specs ([| stn.(Labels) ("scheduler"!"exit")%SP = Some pc_exit |]
        /\ [| (fst stn_st').(Labels) = stn.(Labels) |]
        /\ Cptr pc_exit (fun x => pre_exit x)
        /\ [| sel vs "sc" = sc |]
        /\ ![ locals ("rp" :: "sc" :: nil) vs ss stn_st'#Sp * sched_ * mallocHeap 0 ] stn_st'
        /\ (AlX, Al stn_st'', Al vs',
          ![^[locals ("rp" :: "sc" :: nil) vs' 12 stn_st''#Sp]
            * (^[sched_] * #0 * ^[mallocHeap 0])] stn_st''
          /\ [| sel vs' "sc" = sc |]
          /\ [| (fst stn_st'').(Labels) = stn.(Labels) |]
        ---> Lift (pre_exit stn_st''))
        ---> pre stn_st')%PropX.
  cptr.
  generalize (split_semp _ _ _ H0 H); intros; subst; auto.
  post.
  instantiate (3 := fun p => sched_ (fst p) (snd p)).
  imp; propxFo; eauto.
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

Definition yieldInvariant (pre : vals -> W -> qspec) (post : vals -> W -> W -> qspec) (rpStashed : bool) (adjustSp : W -> W)
  (ns : list string) (res : nat) : assert :=
  st ~> let sp := adjustSp st#Sp in
    ExX (* fr *), Ex vs, qspecOut (pre (sel vs) st#Rv) (fun _PRE =>
      ![ ^[locals ("rp" :: ns) vs res sp * _PRE] * #0 ] st
      /\ ExX (* ret *) : settings * state, Cptr (if rpStashed then sel vs "rp" else st#Rp) #0
      /\ AlX (* sched *) : settings * smem, AlX (* pre_exit *) : settings * state,
      Al pc_exit : W, Al st' : settings * state, Al vs' : vals,
        [| (fst st').(Labels) ("scheduler"!"exit")%SP = Some pc_exit |]
        /\ Cptr pc_exit #0
        /\ (AlX (* fr_exit *) : settings * smem, Al st'', Al vs',
          ![^[locals ("rp" :: "sc" :: nil) vs' 12 st''#Sp]
            * (#2 * #0 * ^[mallocHeap 0])] st''
          /\ [| sel vs' "sc" = sel vs "sc" |]
          /\ [| (fst st'').(Labels) = (fst st').(Labels) |]
          ---> #1 st'')
        /\ [| st'#Sp = sp |]
        /\ qspecOut (post (sel vs) st#Rv st'#Rv) (fun _POST =>
          ![ ^[locals ("rp" :: ns) vs' res sp * _POST] * #3 * #1 ] st')
        ---> #2 st')%PropX.

Notation "'PREy' [ vs ] pre 'POST' [ rv ] post" := (yieldInvariant (fun vs _ => pre%qspec%Sep) (fun vs _ rv => post%qspec%Sep))
  (at level 89).

Notation "'PREy' [ vs , rv ] pre 'POST' [ rv' ] post" := (yieldInvariant (fun vs rv => pre%qspec%Sep) (fun vs rv rv' => post%qspec%Sep))
  (at level 89).

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
  PREy[V] sched (V "sc") * mallocHeap 0
  POST[_] mallocHeap 0.

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

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS],
    "queue"!"init" @ [Queue.initS], "queue"!"isEmpty" @ [isEmptyS],
    "queue"!"enqueue" @ [enqueueS], "queue"!"dequeue" @ [dequeueS] ]]
  bmodule "scheduler" {{
    (*bfunction "init"("q", "sp", "r") [initS]
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
    end with*) bfunctionNoRet "exit"("sc", "q", "r") [exitS]
      Diverge
      (*"q" <-* "sc";;
      "r" <-- Call "queue"!"isEmpty"("q")
      [Al q,
        PREonly[V, R] [| (q %= empty) \is R |]
          * queue q (V "q") * (V "sc" ^+ $8) =?> 2 * susps q (V "sc") * mallocHeap 0];;

      If ("r" = 1) {
        (* No threads left to run.  Let's loop forever! *)
        Diverge
      } else {
        (* Pick a thread to switch to. *)

        "r" <- "sc" + 8;;
        Call "queue"!"dequeue"("q", "r")
        [Al q, Al tsp, Al pc, Al sp,
          PREonly[V] [| (pc, sp) %in q |] * queue (q %- (pc, sp)) (V "q")
            * susps (q %- (pc, sp)) (V "sc") * susp (V "sc") pc sp
            * (V "sc" ==*> V "q", tsp, pc, sp) * mallocHeap 0];;

        Rp <-* "sc" + 8;;
        Sp <-* "sc" + 12;;
        IGoto* [("scheduler","exit")] Rp
      }*)
    end with bfunction "yield"("sc", "q", "curPc", "curSp", "newPc", "newSp") [yieldS]
      "q" <-* "sc";;
      (* Using "curPc" as a temporary before getting to its primary use... *)
      "curPc" <-- Call "queue"!"isEmpty"("q")
      [Al q, Al tsp, Al vs,
        PREy[V, R] [| (q %= empty) \is R |]
          * queue q (V "q") * (V "sc" ==*> V "q", tsp) * (V "sc" ^+ $8) =?> 2 * susps q (V "sc") * mallocHeap 0
          * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 tsp * any
        POST[_] mallocHeap 0];;

      If ("curPc" = 1) {
        (* No other threads to run.  Simply returning to caller acts like a yield. *)
        Return 0
      } else {
        (* Pick a thread to switch to. *)

        "curPc" <- "sc" + 8;;
        Call "queue"!"dequeue"("q", "curPc")
        [Al q, Al tsp, Al vs, Al pc, Al sp,
          PREy[V] [| (pc, sp) %in q |] * queue (q %- (pc, sp)) (V "q")
            * susps (q %- (pc, sp)) (V "sc") * susp (V "sc") pc sp
            * (V "sc" ==*> V "q", tsp, pc, sp) * mallocHeap 0
            * locals ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 tsp * any
          POST[_] mallocHeap 0];;
        "newPc" <-* "sc" + 8;;
        "newSp" <-* "sc" + 12;;

        Assert [PREy[V] susp (V "sc") (V "newPc") (V "newSp") * sched (V "sc") * mallocHeap 0
          POST[_] mallocHeap 0];;

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

        Assert [PREonly[V] Ex sp, Ex b, (V "sc" ==*> V "q", sp) * (V "sc" ^+ $8) =?> 2
          * queue b (V "q") * susps b (V "sc") * any * mallocHeap 0
          * susp (V "sc") (V "newPc") (V "newSp") * susp (V "sc") (V "curPc") (V "curSp")];;

        Note [mergeSusp];;

        (* Enqueue current thread; note that variable references below resolve in the temporary stack. *)
        Call "queue"!"enqueue"("q", "curPc", "curSp")
        [PREonly[V] Ex b, Ex p, Ex sp, (V "sc" ==*> p, sp) * (V "sc" ^+ $8) =?> 2
          * queue b p * susps b (V "sc") * any
          * mallocHeap 0 * susp (V "sc") (V "newPc") (V "newSp")];;

        (* Jump to dequeued thread. *)
        "sc" + 4 *<- Sp;;
        Rp <- "newPc";;
        Sp <- "newSp";;
        IGoto* [("scheduler","exit")] Rp
      }
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Ltac t := sep hints; try apply any_easy;
  try (apply himp_star_frame; [ reflexivity | apply susps_del_fwd; assumption ]);
    eauto.

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

  Lemma substH_in3 : forall (a b c : Type) (P : hpropB (a :: b :: c :: nil))
    (q1 : c -> PropX W (ST.settings * state))
    (q2 : b -> PropX W (ST.settings * state))
    (q3 : a -> PropX W (ST.settings * state)),
    (fun (stn : ST.settings) (sm : smem) => subst (G := a :: nil) (subst (G := a :: b :: nil) (subst (P stn sm) q1) q2) q3) =
    substH (substH (substH P q1) q2) q3.
    reflexivity.
  Qed.

  Hint Rewrite substH_in3 : sepFormula.

  sep_auto.
  apply unandL.
  eapply Imply_trans; [ | apply H3 ]; clear H3.
  repeat apply andR; try ((apply injR || apply cptrR); simpl; eauto).
  apply andL; apply swap; apply implyR.
  refl.
  apply andL; apply implyR.
  descend.
  rewrite substH_in3; descend.
  match goal with
    | [ |- interp _ (![?P] _ ---> ![?Q] _)%PropX ] =>
      let H := fresh in assert (H : P ===> Q); [ | rewrite sepFormula_eq; apply H ]
  end.
  repeat (apply Himp_star_frame; [ | apply Himp_refl ]).
  change ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)
    with (("rp" :: "sc" :: nil) ++ ("q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)).
  change 14 with (19 - length ("q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)) at 1.
  eapply Himp_trans; [ apply prelude_out | ].
  simpl; auto.
  rewrite H0; apply Himp_refl.

  t.

  post.
  evaluate hints.
  descend.
  step hints.
  step hints.
  step hints.
  unfold yieldInvariant; descend; step hints.
  instantiate (2 := x7).
  instantiate (3 := upd x1 "q" x8).
  descend; cancel hints.
  step hints.
  step hints.
  apply unandL; apply implyR.
  eapply Imply_trans; [ | apply H4 ]; clear H4.
  repeat apply andR; try ((apply injR || apply cptrR); simpl; eauto).
  apply andL; apply swap; apply implyR; refl.
  apply andL; apply implyR.
  descend.
  rewrite substH_in3; descend.
  step auto_ext.
  
  t.
  t.
  t.
  admit. (* Regular return.  Needs exit() assumption. *)
  t.

  post.
  evaluate hints.
  descend.
  step hints.
  2: step hints.
  eauto.
  step hints.
  unfold yieldInvariant; descend; step hints.
  instantiate (2 := x2).
  instantiate (4 := upd (upd x5 "curPc" (Regs x0 Rv)) "curPc" (sel x5 "sc" ^+ $8)).
  descend; cancel hints.
  step hints.
  apply himp_star_frame; [ reflexivity | apply susps_del_fwd; assumption ].
  step hints.
  descend.
  apply unandL; apply implyR.
  eapply Imply_trans; [ | apply H6 ]; clear H6.
  repeat apply andR; try ((apply injR || apply cptrR); simpl; eauto).
  apply andL; apply swap; apply implyR; refl.
  apply andL; apply implyR.
  descend.
  rewrite substH_in3; descend.
  step auto_ext.

  t.
  t.

  post.
  evaluate hints.
  descend.
  instantiate (2 := upd (upd x7 "newPc" x4) "newSp" x5).
  descend.
  step hints.
  rewrite (create_locals_return ("rp" :: "sc" :: nil) 12
    ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)
    14 28).
  assert (ok_return ("rp" :: "sc" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)
    ("rp" :: "sc" :: nil) 14 12 28)%nat by (split; [
      simpl; omega
      | reflexivity ] ).
  autorewrite with sepFormula.
  generalize dependent (upd (upd x7 "newPc" x4) "newSp" x5); intros.
  cancel auto_ext.
  step hints.
  descend; step hints.
  descend; step hints.
  apply unandL.
  eapply Imply_trans; [ | apply H4 ]; clear H4.
  repeat (apply andL; (apply injL || apply cptrL); intro).
  simpl; repeat apply andR; try ((apply injR || apply cptrR); simpl; eauto).
  apply andL; apply swap; apply implyR; refl.
  apply andL; apply implyR.
  descend.
  rewrite substH_in3; descend.
  step auto_ext.

  t.

  post.
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

  Lemma Labels_cong : forall stn stn' l pc,
    Labels stn l = Some pc
    -> Labels stn' = Labels stn
    -> Labels stn' l = Some pc.
    intros; rewrite H0; auto.
  Qed.

  Hint Immediate Labels_cong.

  simpl; repeat apply andR; try ((apply injR || apply cptrR); simpl; eauto).
  apply andL; apply swap; apply implyR.
  rewrite H7; instantiate (1 := fun p => sched_ (fst p) (snd p)); refl.
  apply andL; apply implyR.
  descend.
  rewrite substH_in3; descend.
  instantiate (1 := upd (upd x1 "curPc" x6) "q" x7).
  clear.
  step auto_ext.

  t.
  t.

  post.
  evaluate hints.
  descend.
  instantiate (3 := x3).
  step hints.
  step hints.
  step hints.
  descend; step hints.
  instantiate (6 := x3 %+ (sel x1 "curPc", sel x1 "curSp")).
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
    | [ H : _ |- _ ] => eapply H; eauto
  end.
  2: step hints.
  unfold localsInvariantCont.
  descend; step auto_ext.
  instantiate (1 := fun p => (fr_exit * (fun x y => x2 (x, y)))%Sep (fst p) (snd p));
    instantiate (1 := vs);
      match goal with
        | [ H : sel _ "sc" = sel _ "sc" |- _ ] => rewrite H
      end; clear.
  descend; step hints.


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

  rewrite stackSize_split in H0.
  assert (NoDup ("rp" :: "q" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)) by NoDup.
  evaluate hints; descend; repeat (step hints; descend); auto.

  t.
  t.
  t.
  t.
  t.





  vcgen; try abstract t.


  post.
  match goal with
    | [ H : context[?X - 2] |- _ ] =>
      replace X with (length ("rp" :: "sc" :: nil) + (X - length ("rp" :: "sc" :: nil))) in H
  end.
  assert (NoDup ("rp" :: "sc" :: nil)) by NoDup.
  evaluate hints; sep hints; auto.
  evaluate hints; simpl; omega.


  post.
  evaluate auto_ext.
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
  2: instantiate (4 := locals ("rp" :: "sc" :: nil) (upd x1 "sc" (sel x3 "sc")) x0 (sel x3 "ss")); sep_auto.
  step auto_ext.
  step auto_ext.
  big_imp.
  imp; [ | match goal with
             | [ H : Regs _ Sp = sel _ "ss" |- _ ] => rewrite H; refl
           end ]; propxFo; eauto.
  sep_auto.
  sep_auto; auto.


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
    | [ H : _ |- _ ] => eapply H; eauto
  end.
  instantiate (1 := sched (sel x6 "sc")); simpl.
  unfold localsInvariantCont.
  descend; step auto_ext.
  instantiate (1 := fun p => fr_exit (fst p) (snd p));
    instantiate (1 := vs);
      match goal with
        | [ H : sel _ "sc" = sel _ "sc" |- _ ] => rewrite H
      end; clear; descend; step auto_ext.
  step hints; apply any_easy.
Qed.

Transparent stackSize.
