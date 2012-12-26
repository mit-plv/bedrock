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

  Axiom sched_fwd : forall sc, sched sc ===> Ex b, Ex p, sc =*> p * (sc ^+ $4) =?> 2 * queue b p * susps b sc * any.
  Axiom sched_bwd : forall sc, (Ex b, Ex p, sc =*> p * (sc ^+ $4) =?> 2 * queue b p * susps b sc * any) ===> sched sc.
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
    Ex b, Ex p, sc =*> p * (sc ^+ $4) =?> 2 * queue b p * susps b sc * any.

  Theorem sched_extensional : forall sc, HProp_extensional (sched sc).
    reflexivity.
  Qed.

  Theorem sched_fwd : forall sc, sched sc ===> Ex b, Ex p, sc =*> p * (sc ^+ $4) =?> 2 * queue b p * susps b sc * any.
    unfold sched; sepLemma.
  Qed.

  Theorem sched_bwd : forall sc, (Ex b, Ex p, sc =*> p * (sc ^+ $4) =?> 2 * queue b p * susps b sc * any) ===> sched sc.
    unfold sched; sepLemma.
  Qed.
End Sched.

Import Sched.
Export Sched.
Hint Immediate sched_extensional.

Definition hints : TacPackage.
  prepare (sched_fwd, create_stack) (sched_bwd, susps_empty_bwd, susps_add_bwd).
Defined.

Definition initS : spec := SPEC reserving 11
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

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS],
    "queue"!"init" @ [Queue.initS], "queue"!"isEmpty" @ [isEmptyS],
    "queue"!"enqueue" @ [enqueueS], "queue"!"dequeue" @ [dequeueS] ]]
  bmodule "scheduler" {{
    bfunction "init"("q", "r") [initS]
      "q" <-- Call "queue"!"init"()
      [PRE[_, R] mallocHeap 0
       POST[R'] R' =*> R * (R' ^+ $4) =?> 2 * mallocHeap 0];;

      "r" <-- Call "malloc"!"malloc"(0, 3)
      [PRE[V, R] R =?> 3
       POST[R'] [| R' = R |] * R =*> V "q" * (R ^+ $4) =?> 2 ];;
      "r" *<- "q";;
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
      [Al q,
        PREonly[V, R] [| (q %= empty) \is R |]
          * queue q (V "q") * V "sc" =*> V "q" * (V "sc" ^+ $4) =?> 2 * susps q (V "sc") * mallocHeap 0];;

      If ("r" = 1) {
        (* No threads left to run.  Let's loop forever! *)
        Diverge
      } else {
        (* Pick a thread to switch to. *)

        "r" <- "sc" + 4;;
        Call "queue"!"dequeue"("q", "r")
        [Al q, Al pc, Al sp,
          PREonly[V] [| (pc, sp) %in q |] * queue (q %- (pc, sp)) (V "q")
            * susps (q %- (pc, sp)) (V "sc") * susp (V "sc") pc sp
            * (V "sc" ==*> V "q", pc, sp) * mallocHeap 0];;

        Rp <-* "sc" + 4;;
        Sp <-* "sc" + 8;;
        IGoto* [("scheduler","exit")] Rp
      }
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.


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
