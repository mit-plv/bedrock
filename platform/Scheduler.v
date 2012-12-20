Require Import AutoSep Bags Malloc Queue.

Set Implicit Arguments.


(* What does it mean for a program counter to be valid for a suspended thread? *)

Definition susp (sc pc sp : W) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ ExX (* inv *) : settings * smem, #0 (s, m)
    /\ AlX (* sched *) : settings * smem, AlX (* pre_exit *) : settings * state,
      Al pc_exit : W, Al st : settings * state,
      [| s.(Labels) ("scheduler"!"exit")%SP = Some pc_exit |]
      /\ Cptr pc_exit #0
      /\ (AlX (* fr_exit *) : settings * smem, Al st',
        (Ex vs : vals,
          ![^[locals ("rp" :: "sc" :: nil) vs 12 st'#Sp]
            * (#2 * #0 * ^[mallocHeap 0])] st'
          /\ [| sel vs "sc" = sc |])
        ---> #1 st')
      /\ [| st#Sp = sp |]
      /\ ![ #2 * #1 ] st
      ---> #3 st)%PropX.

(* What is a valid initial code pointer for a thread, given the requested stack size? *)

Definition starting (sc pc : W) (ss : nat) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ [| semp m |]
    /\ AlX (* sched *) : settings * smem, AlX (* pre_exit *) : settings * state,
      Al pc_exit : W, Al st : settings * state, Al vs : vals,
      [| s.(Labels) ("scheduler"!"exit")%SP = Some pc_exit |]
      /\ Cptr pc_exit #0
      /\ (AlX (* fr_exit *) : settings * smem, Al st',
        (Ex vs' : vals,
          ![^[locals ("rp" :: "sc" :: nil) vs' 12 st'#Sp]
            * (#2 * #0 * ^[mallocHeap 0])] st'
          /\ [| sel vs' "sc" = sc |])
        ---> #1 st')
      /\ ![ ^[locals ("rp" :: "sc" :: nil) vs ss st#Sp] * #1 ] st
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

Lemma create_stack : forall ns ss sp,
  NoDup ns
  -> sp =?> (length ns + ss) ===> Ex vs, locals ns vs ss sp.
  intros; eapply Himp_trans; [ apply allocated_split | ].
  instantiate (1 := length ns); omega.
  eapply Himp_trans.
  eapply Himp_star_frame.
  apply behold_the_array; auto.
  apply Himp_refl.
  unfold locals, array.
  Opaque mult.
  sepLemma.
  apply allocated_shift_base.
  Require Import Arith.
  unfold natToW; rewrite mult_comm; words.
  omega.
Qed.

Transparent mult.

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
          /\ Cptr pc_exit (fun x => pre_exit x)
          /\ (AlX, Al stn_st'', (Ex vs : vals,
            ![^[locals ("rp" :: "sc" :: nil) vs 12 stn_st''#Sp]
              * (^[sched_] * #0 * ^[mallocHeap 0])] stn_st''
            /\ [| sel vs "sc" = sc |])
          ---> Lift (pre_exit stn_st''))
          /\ [| stn_st'#Sp = sp |]
          /\ ![ inv * sched_ ] stn_st'
          ---> pre stn_st')%PropX)
  -> interp specs (![ susp sc pc sp * P ] (stn, st)).
  post.
  rewrite sepFormula_eq; rewrite sepFormula_eq in H1; propxFo.
  do 3 esplit.
  eauto.
  descend.
  eauto.
  instantiate (1 := fun p => x0 (fst p) (snd p)); auto.
  eapply Imply_trans; try apply H2; clear H2.
  apply andL; apply injL; intro.
  apply andL; apply cptrL; intro.
  simpl.
  apply andL.
  apply swap.
  apply andL; apply injL; intro.
  apply unandL.
  repeat apply andR.
  apply injR; eauto.
  apply cptrR; eauto.
  apply andL; apply swap; apply implyR.
  instantiate (1 := fun x y => a (x, y)).
  rewrite sepFormula_eq; apply Imply_refl.
  apply injR; auto.
  apply andL; apply implyR; apply Imply_refl.
Qed.

Lemma susp_elim : forall specs sc pc sp P stn st,
  interp specs (![ susp sc pc sp * P ] (stn, st))
  -> exists pre, specs pc = Some pre
    /\ exists inv, interp specs (![ inv * P ] (stn, st))
      /\ forall sched_ pre_exit pc_exit stn_st',
        stn.(Labels) ("scheduler"!"exit")%SP = Some pc_exit
        -> specs pc_exit = Some (fun x => pre_exit x)
        -> (forall fr_exit stn_st'', interp specs ((Ex vs : vals,
            ![^[locals ("rp" :: "sc" :: nil) vs 12 stn_st''#Sp]
              * (sched_ * (fun s m => fr_exit s m) * ^[mallocHeap 0])] stn_st''
            /\ [| sel vs "sc" = sc |])
          ---> pre_exit stn_st'')%PropX)
        -> stn_st'#Sp = sp
        -> interp specs (![ inv * sched_ ] stn_st')
        -> interp specs (pre stn_st').
  rewrite sepFormula_eq; repeat (propxFo; repeat (eauto; esplit)).
  instantiate (1 := fun stn x => x2 (stn, x)); auto.
  eapply (Imply_sound (H4 _ _ _ _)); clear H4.
  propxFo; eauto.
  rewrite <- sepFormula_eq in *.
  eapply Imply_trans; [ | apply H6 ].
  step auto_ext.
  step auto_ext.
  match goal with
    | [ |- interp ?specs (![?P] ?x ---> ![?Q] ?x)%PropX ] =>
      let H := fresh in assert (H : himp specs P Q); [ | rewrite sepFormula_eq; apply H ]
  end.
  repeat apply himp_star_frame; try reflexivity.
  instantiate (1 := fun p => sched_ (fst p) (snd p)); reflexivity.
  auto.
  eauto.
  post.
  rewrite sepFormula_eq; propxFo; eauto.
Qed.

Lemma starting_elim : forall specs sc pc ss P stn st,
  interp specs (![ starting sc pc ss * P ] (stn, st))
  -> exists pre, specs pc = Some pre
    /\ interp specs (![ P ] (stn, st))
    /\ forall sched_ pre_exit pc_exit stn_st' vs,
      interp specs ([| stn.(Labels) ("scheduler"!"exit")%SP = Some pc_exit |]
        /\ Cptr pc_exit (fun x => pre_exit x)
        /\ [| sel vs "sc" = sc |]
        /\ ![ locals ("rp" :: "sc" :: nil) vs ss stn_st'#Sp * sched_ ] stn_st'
        /\ (AlX , Al stn_st'', (Ex vs' : vals,
          ![^[locals ("rp" :: "sc" :: nil) vs' 12 stn_st''#Sp]
            * (^[sched_] * #0 * ^[mallocHeap 0])] stn_st''
          /\ [| sel vs' "sc" = sc |])
        ---> Lift (pre_exit stn_st''))
        ---> pre stn_st')%PropX.
  intros; rewrite sepFormula_eq in H; repeat (propxFo; repeat (eauto; esplit)).
  rewrite sepFormula_eq; unfold sepFormula_def; simpl.
  rewrite (split_semp _ _ _ H0); auto.
  eapply Imply_trans; [ | apply H4 ].
  apply andL; apply injL; intro.
  apply andL; apply cptrL; intro.
  apply andL; apply injL; intro.
  repeat apply andR.
  apply injR; eauto.
  apply cptrR; eauto.
  apply andL; apply swap; apply implyR.
  instantiate (1 := fun p => sched_ (fst p) (snd p)).
  rewrite sepFormula_eq; apply Imply_refl.
  apply andL; apply implyR.
  descend; step auto_ext.
  hnf; simpl; intros.
  apply Imply_refl.
  apply injR; auto.
Qed.

Ltac t := sep hints; try apply any_easy;
  try (apply himp_star_frame; [ reflexivity | apply susps_del_fwd; assumption ]);
    eauto.

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
  evaluate hints.
  descend.
  step hints.
  step hints.
  step hints.
  descend; step hints.
  descend; step hints.
  descend; step hints.
  pre_nomega.
  rewrite wordToNat_natToWord_idempotent in * by reflexivity.
  assumption.
  step hints.
  descend; step hints.
  descend; step hints.
  descend; step hints.
  descend; step hints.
  auto.
  descend; step hints.

  t.

  post.
  replace x0 with (length ("rp" :: "sc" :: nil) + (x0 - length ("rp" :: "sc" :: nil))) in H0.
  assert (NoDup ("rp" :: "sc" :: nil)) by NoDup.
  evaluate hints.
  descend.
  step hints.
  descend; step hints.
  rewrite <- minus_n_O; step hints.
  step auto_ext.
  descend; step hints.
  descend; step hints.
  auto.
  descend; step hints.
  evaluate hints; simpl; omega.

  t.

  post.
  evaluate auto_ext.
  toFront ltac:(fun P => match P with
                           | starting _ _ _ => idtac
                         end) H7.
  apply starting_elim in H7; post.
  descend.

  toFront_conc ltac:(fun P => match P with
                                | susp _ _ _ => idtac
                              end).
  apply susp_intro; descend.
  Focus 2.
  step auto_ext.
  step auto_ext.
  instantiate (2 := locals ("rp" :: "sc" :: nil) (upd x1 "sc" (sel x3 "sc")) x0 (sel x3 "ss")).
  step auto_ext.
  step auto_ext.
  eapply Imply_trans; try apply H10.
  apply andL; apply injL; intro.
  apply andL; apply cptrL; intro.
  apply andL; apply swap.
  apply andL; apply injL; intro.
  apply unandL.
  repeat apply andR.
  apply injR; eauto.
  apply cptrR; eauto.
  Focus 2.
  apply andL; apply implyR.
  descend.
  rewrite H12.
  descend; step auto_ext.
  apply injR; eauto.
  apply andL; apply swap; apply implyR.
  rewrite sepFormula_eq; apply Imply_refl.
  step auto_ext.
  descend; step auto_ext.
  descend; step auto_ext.
  descend; step auto_ext.
  descend; step auto_ext.
  descend; step auto_ext.
  descend; step auto_ext.
  auto.
  descend; step auto_ext.

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

  toFront ltac:(fun P => match P with
                           | susp _ _ _ => idtac
                         end) H6.

  apply susp_elim in H6; post.
  esplit; split.
  eauto.
  eapply H10.
  eauto.
  eauto.
  2: auto.
  Focus 2.
  instantiate (1 := sched (sel x6 "sc")); simpl.
  descend; step hints.
  apply any_easy.

  unfold localsInvariantCont; simpl; intros.
  step auto_ext.
  step auto_ext.
  step auto_ext.
Qed.
