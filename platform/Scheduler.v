Require Import AutoSep Bags Malloc Queue.

Set Implicit Arguments.


(* What does it mean for a program counter to be valid for a suspended thread? *)

Definition susp (sc pc sp : W) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ ExX (* inv *) : settings * smem, #0 (s, m)
    /\ AlX (* sched *) : W * settings * smem, AlX (* pre_exit *) : settings * state,
      AlX (* fr_exit *) : settings * smem, AlX (* pre_rp *) : settings * state,
      Al pc_exit : W, Al st : settings * state,
      [| s.(Labels) ("scheduler"!"exit")%SP = Some pc_exit |]
      /\ Cptr pc_exit #2
      /\ (Al st',
        (Ex vs : vals,
          ![^[locals ("rp" :: "sc" :: "rem" :: nil) vs 12 st'#Sp]
            * ((fun s m => Lift (Lift (Lift (Var0 (sel vs "sc", s, m))))) * #1 * ^[mallocHeap 0])] st'
          /\ Cptr st'#Rp #0)
        ---> #2 st')
      /\ [| st#Sp = sp |]
      /\ ![ #4 * (fun s m => Lift (Lift (Lift (Var0 (sc, s, m))))) ] st
      ---> #5 st)%PropX.

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
  prepare sched_fwd (sched_bwd, susps_empty_bwd, susps_add_bwd).
Defined.

Definition initS : spec := SPEC reserving 11
  PRE[_] mallocHeap 0
  POST[R] sched R * mallocHeap 0.

Definition spawnS : spec := SPEC("sc", "pc", "sp") reserving 14
  PRE[V] sched (V "sc") * susp (V "sc") (V "pc") (V "sp") * mallocHeap 0
  POST[_] sched (V "sc") * mallocHeap 0.

Definition exitS : spec := SPEC("sc", "rem") reserving 12
  PRE[V] sched (V "sc") * mallocHeap 0
  POST[_] [| False |].

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
    end with bfunction "spawn"("sc", "pc", "sp") [spawnS]
      "sc" <-* "sc";;
      Note [mergeSusp];;
      Call "queue"!"enqueue"("sc", "pc", "sp")
      [Al b, Al sc,
        PRE[V] susps (b %+ (V "pc", V "sp")) sc
        POST[_] susps (b %+ (V "pc", V "sp")) sc];;
      Return 0
    end with bfunction "exit"("sc", "rem", "q", "r") [exitS]
      "q" <-* "sc";;
      "r" <-- Call "queue"!"isEmpty"("q")
      [Al q,
        PRE[V, R] [| (q %= empty) \is R |]
          * queue q (V "q") * V "sc" =*> V "q" * (V "sc" ^+ $4) =?> 2 * susps q (V "sc") * mallocHeap 0
        POST[_] [| False |] ];;

      If ("r" = 1) {
        (* No threads left to run.  Let's loop forever! *)
        Diverge
      } else {
        (* Pick a thread to switch to. *)

        "r" <- "sc" + 4;;
        Call "queue"!"dequeue"("q", "r")
        [Al q, Al pc, Al sp,
          PRE[V] [| (pc, sp) %in q |] * queue (q %- (pc, sp)) (V "q")
            * susps (q %- (pc, sp)) (V "sc") * susp (V "sc") pc sp
            * (V "sc" ==*> V "q", pc, sp) * mallocHeap 0
          POST[_] [| False |] ];;

        Rp <-* "sc" + 4;;
        Sp <-* "sc" + 8;;
        IGoto* [("scheduler","exit")] Rp
      }
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Lemma susp_elim : forall specs sc pc sp P stn st,
  interp specs (![ susp sc pc sp * P ] (stn, st))
  -> exists pre, specs pc = Some pre
    /\ exists inv, interp specs (![ inv * P ] (stn, st))
      /\ forall sched_ pre_exit fr_exit pre_rp pc_exit stn_st',
        stn.(Labels) ("scheduler"!"exit")%SP = Some pc_exit
        -> specs pc_exit = Some (fun x => pre_exit x)
        -> (forall stn_st'', interp specs ((Ex vs : vals,
            ![^[locals ("rp" :: "sc" :: "rem" :: nil) vs 12 stn_st''#Sp]
              * ((fun s m => sched_ (sel vs "sc", s, m)) * (fun s m => fr_exit s m) * ^[mallocHeap 0])] stn_st''
            /\ Cptr stn_st''#Rp pre_rp)
          ---> pre_exit stn_st'')%PropX)
        -> stn_st'#Sp = sp
        -> interp specs (![ inv * (fun s m => sched_ (sc, s, m)) ] stn_st')
        -> interp specs (pre stn_st').
  rewrite sepFormula_eq; repeat (propxFo; repeat (eauto; esplit)).
  instantiate (1 := fun stn x => x2 (stn, x)); auto.
  eapply (Imply_sound (H4 _ _ _ _ _ _)); clear H4.
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
  instantiate (1 := fun p => fr_exit (fst p) (snd p)); reflexivity.
  eauto.
  post.
  rewrite sepFormula_eq; propxFo; eauto.
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
                         end) H8.

  apply susp_elim in H8; post.
  esplit; split.
  eauto.
  eapply H12.
  eauto.
  eauto.
  2: auto.
  Focus 2.
  instantiate (1 := fun p => sched (fst (fst p)) (snd (fst p)) (snd p)); simpl.
  descend; step hints.
  apply any_easy.

  unfold localsInvariant; simpl.
  intros.
  step auto_ext.
  step auto_ext.
  generalize sched_extensional.
  unfold HProp_extensional.
  intro Ho; rewrite <- Ho.
  step auto_ext.
  eauto.
  instantiate (1 := x7).
  instantiate (1 := fun _ _ => [|False|]%PropX).
  eapply Imply_trans with (![ [| False |] ] x11)%PropX.
  step auto_ext.
  rewrite sepFormula_eq; unfold sepFormula_def, injB, inj.
  apply Imply_I; eapply Inj_E; [ eapply And_E1; apply Env; simpl; eauto | tauto ].
Qed.
