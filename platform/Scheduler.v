Require Import AutoSep Bags Malloc Queue.

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
      /\ ![ ^[locals ("rp" :: "sc" :: nil) vs ss st#Sp * mallocHeap 0] * #1 ] st
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

Lemma tuple_predicate : forall A B pc state
  (P : A -> B -> PropX pc state) P' specs x y,
  interp specs (P x y)
  -> P' = (fun p => P (fst p) (snd p))
  -> interp specs (P' (x, y)).
  intros; subst; auto.
Qed.

Hint Extern 1 (interp _ _) =>
  eapply tuple_predicate; [ eassumption | reflexivity ].

Fixpoint eatEasy pc state G (P : propX pc state G)
  : list (propX pc state G) * list (propX pc state G) :=
  match P in propX _ _ G return list (propX _ _ G) * list (propX _ _ G) with
    | Inj _ p => (Inj p :: nil, nil)
    | Cptr _ pc f => (Cptr pc f :: nil, nil)
    | And _ Q R => let (easy1, hard1) := eatEasy Q in
      let (easy2, hard2) := eatEasy R in
        (easy1 ++ easy2, hard1 ++ hard2)
    | Or _ Q R => (nil, Or Q R :: nil)
    | Imply _ Q R => (nil, Imply Q R :: nil)
    | Forall _ _ Q => (nil, Forall Q :: nil)
    | Exists _ _ Q => (nil, Exists Q :: nil)
    | Var0 _ _ v => (nil, Var0 v :: nil)
    | Lift _ _ Q => (nil, Lift Q :: nil)
    | ForallX _ _ Q => (nil, ForallX Q :: nil)
    | ExistsX _ _ Q => (nil, ExistsX Q :: nil)
  end.

Definition andify' pc state G (Ps : list (propX pc state G)) :=
  fold_left (@And _ _ _) Ps.

Definition andify pc state G (Ps : list (propX pc state G)) :=
  andify' Ps (Inj True).

Lemma eatEasy_right1 : forall pc state (P : PropX pc state) specs,
  interp specs ([|True|] /\ P ---> [|True|] ---> P)%PropX.
  intros.
  repeat apply Imply_I.
  eapply And_E2; apply Env; simpl; eauto.
Qed.

Lemma eatEasy_right2 : forall pc state (P : PropX pc state) specs,
  interp specs (andify nil ---> andify (P :: nil) ---> P)%PropX.
  unfold andify, andify'; simpl; intros.
  do 2 apply Imply_I.
  eapply And_E2; apply Env; simpl; eauto.
Qed.

Lemma andify1'' : forall pc state (Ps : list (PropX pc state)) R' R specs,
  interp specs (R' ---> R)
  -> interp specs (andify' Ps R' ---> R).
  unfold andify'; induction Ps; simpl; intuition.
  apply IHPs.
  apply Imply_I; eapply Imply_E; [ apply interp_weaken; apply H | ].
  eapply And_E1; apply Env; simpl; eauto.
Qed.

Lemma andify1' : forall pc state (Qs Ps : list (PropX pc state)) R specs,
  interp specs (andify' (Ps ++ Qs) R ---> andify' Ps R).
  unfold andify'; induction Ps; simpl; intuition.
  apply andify1''; apply Imply_refl.
Qed.

Lemma andify1 : forall pc state (Qs Ps : list (PropX pc state)) specs,
  interp specs (andify (Ps ++ Qs) ---> andify Ps).
  intros; apply andify1'.
Qed.

Lemma andify2''' : forall pc state (Ps : list (PropX pc state)) R' R specs,
  interp specs ((R' ---> R) ---> andify' Ps R' ---> andify' Ps R)%PropX.
  unfold andify'; induction Ps; simpl; intuition.
  apply Imply_refl.
  apply Imply_I.
  eapply Imply_E.
  apply interp_weaken; apply IHPs.
  apply Imply_I; apply And_I.
  eapply Imply_E.
  apply Env; simpl; eauto.
  eapply And_E1; apply Env; simpl; eauto.
  eapply And_E2; apply Env; simpl; eauto.
Qed.

Lemma andify2'' : forall pc state (Ps : list (PropX pc state)) R' R specs,
  interp specs (R' ---> R)
  -> interp specs (andify' Ps R' ---> andify' Ps R).
  intros; eapply Imply_E.
  apply andify2'''.
  auto.
Qed.

Lemma andify2' : forall pc state (Qs Ps : list (PropX pc state)) R specs,
  interp specs (andify' (Ps ++ Qs) R ---> andify' Qs R).
  unfold andify'; induction Ps; simpl; intuition.
  apply Imply_refl.
  eapply Imply_trans; try apply IHPs.
  apply andify2''.
  eapply Imply_I; eapply And_E1; apply Env; simpl; eauto.
Qed.

Lemma andify2 : forall pc state (Qs Ps : list (PropX pc state)) specs,
  interp specs (andify (Ps ++ Qs) ---> andify Qs).
  intros; apply andify2'.
Qed.

Lemma eatEasy_right' : forall pc state G (P : propX pc state G),
  match G return propX pc state G -> Prop with
    | nil => fun P => forall specs,
      let (easy, hard) := eatEasy P in
        interp specs (andify easy ---> andify hard ---> P)%PropX
    | _ => fun _ => True
  end P.
  induction P; destruct G; simpl; intuition;
    try (apply eatEasy_right1 || apply eatEasy_right2; eauto).

  intros.
  destruct (eatEasy P1).
  destruct (eatEasy P2).
  repeat apply Imply_I.
  apply And_I.
  eapply Imply_E; [ eapply Imply_E | ].
  apply interp_weaken; apply IHP1.
  eapply Imply_E; [ apply interp_weaken; apply andify1 | ].
  eapply Env; simpl; eauto.
  eapply Imply_E; [ apply interp_weaken; apply andify1 | ].
  eapply Env; simpl; eauto.
  eapply Imply_E.
  eapply Imply_E.
  apply interp_weaken; apply IHP2.
  eapply Imply_E; [ apply interp_weaken; apply andify2 | ].
  apply Env; simpl; eauto.
  eapply Imply_E; [ apply interp_weaken; apply andify2 | ].
  apply Env; simpl; eauto.
Qed.

Lemma eatEasy_left1 : forall pc state (P : PropX pc state) specs,
  interp specs (P ---> andify (P :: nil))%PropX.
  unfold andify, andify'; simpl; intros.
  apply Imply_I.
  apply And_I.
  apply Inj_I; auto.
  apply Env; simpl; eauto.
Qed.

Lemma eatEasy_left2 : forall pc state (P : PropX pc state) specs,
  interp specs (P ---> andify nil).
  intros; apply Imply_I; apply Inj_I; auto.
Qed.

Lemma andify_app' : forall pc state (Qs Ps : list (PropX pc state)) R specs,
  interp specs (andify' Ps R ---> andify Qs ---> andify' (Ps ++ Qs) R)%PropX.
  unfold andify, andify'; induction Ps; simpl; intuition.
  apply Imply_I.
  eapply Imply_E.
  apply interp_weaken; apply andify2'''.
  apply Imply_I; apply Env; simpl; eauto.
Qed.

Lemma andify_app : forall pc state (Qs Ps : list (PropX pc state)) specs,
  interp specs (andify Ps ---> andify Qs ---> andify (Ps ++ Qs))%PropX.
  unfold andify, andify'; induction Ps; simpl; intuition.
  apply Imply_I; apply interp_weaken; apply Imply_refl.
  apply andify_app'.
Qed.

Lemma eatEasy_left1' : forall pc state G (P : propX pc state G),
  match G return propX pc state G -> Prop with
    | nil => fun P => forall specs,
      let (easy, hard) := eatEasy P in
        interp specs (P ---> andify easy)%PropX
    | _ => fun _ => True
  end P.
  induction P; destruct G; simpl; intuition;
    try (apply eatEasy_left1 || apply eatEasy_left2).

  destruct (eatEasy P1); destruct (eatEasy P2).
  apply andL; do 2 apply Imply_I.
  eapply Imply_E.
  eapply Imply_E.
  apply interp_weaken; apply andify_app.
  eapply Imply_E.
  apply interp_weaken; apply IHP1; apply Env; simpl; auto.
  apply Env; simpl; auto.
  eapply Imply_E.
  apply interp_weaken; apply IHP2; apply Env; simpl; auto.
  apply Env; simpl; auto.
Qed.

Lemma eatEasy_left2' : forall pc state G (P : propX pc state G),
  match G return propX pc state G -> Prop with
    | nil => fun P => forall specs,
      let (easy, hard) := eatEasy P in
        interp specs (P ---> andify hard)%PropX
    | _ => fun _ => True
  end P.
  induction P; destruct G; simpl; intuition;
    try (apply eatEasy_left1 || apply eatEasy_left2).

  destruct (eatEasy P1); destruct (eatEasy P2).
  apply andL; do 2 apply Imply_I.
  eapply Imply_E.
  eapply Imply_E.
  apply interp_weaken; apply andify_app.
  eapply Imply_E.
  apply interp_weaken; apply IHP1; apply Env; simpl; auto.
  apply Env; simpl; auto.
  eapply Imply_E.
  apply interp_weaken; apply IHP2; apply Env; simpl; auto.
  apply Env; simpl; auto.
Qed.

Theorem eatEasy_simpl : forall pc state (P Q : PropX pc state) specs,
  (let (easy1, hard1) := eatEasy P in
    let (easy2, hard2) := eatEasy Q in
    interp specs (andify easy1 ---> andify hard1 ---> andify easy2 /\ andify hard2)%PropX)
  -> interp specs (P ---> Q)%PropX.
  intros.
  specialize (eatEasy_left1' P); specialize (eatEasy_left2' P); destruct (eatEasy P); intros.
  specialize (eatEasy_right' Q); destruct (eatEasy Q); intros.
  apply Imply_trans with (andify l0 /\ andify l)%PropX.
  apply andR; auto.
  eapply Imply_trans; try apply H2.
  apply andL; apply swap; eauto.
  apply andL; auto.
Qed.

Ltac big_imp := ((eapply Imply_sound; [ match goal with
                                          | [ H : _ |- _ ] => apply H
                                        end | ])
|| (eapply Imply_trans; [ | match goal with
                              | [ H : _ |- _ ] => apply H
                            end ])); cbv beta; simpl.

Ltac cptr := post; rewrite sepFormula_eq;
  repeat match goal with
           | [ H : interp _ (![_] _) |- _ ] => rewrite sepFormula_eq in H
         end; propxFo; descend; eauto;
  try big_imp.

Lemma jiggle : forall pc state (P Q R S : PropX pc state) specs,
  interp specs (P ---> (Q /\ S) /\ R)%PropX
  -> interp specs (P ---> (Q /\ R) /\ S)%PropX.
  intros.
  eapply Imply_trans; try apply H.
  intros; apply Imply_I.
  repeat apply And_I.
  eapply And_E1; eapply And_E1; apply Env; simpl; eauto.
  eapply And_E2; apply Env; simpl; eauto.
  eapply And_E2; eapply And_E1; apply Env; simpl; eauto.
Qed.

Ltac refl := try rewrite sepFormula_eq;
  apply Imply_refl || (apply jiggle; apply Imply_refl).

Ltac imp := rewrite sepFormula_eq; apply eatEasy_simpl;
  unfold andify, andify'; simpl;
    repeat (apply andL; apply swap; ((apply injL || apply cptrL); intro));
      apply injL; intro; apply andR; [
        apply Imply_I; apply interp_weaken
        | try refl ].

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
        /\ ![ locals ("rp" :: "sc" :: nil) vs ss stn_st'#Sp * mallocHeap 0 * sched_ ] stn_st'
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

Lemma curry_predicate : forall A B pc state
  (P : A * B -> PropX pc state) P' specs x y,
  interp specs (P (x, y))
  -> P' = (fun x y => P (x, y))
  -> interp specs (P' x y).
  intros; subst; auto.
Qed.

Hint Extern 1 (simplify _ _ _) =>
  apply simplify_fwd; eapply curry_predicate; [ eassumption | reflexivity ].

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

Lemma substH_in2 : forall a b (P : hpropB (a :: b :: nil)) q1 q2,
  (fun stn sm => subst (G := a :: nil) (subst (P stn sm) q1) q2) = substH (substH P q1) q2.
reflexivity.
Qed.

Hint Rewrite substH_in2 : sepFormula.

Lemma starting_elim : forall specs sc pc ss P stn st,
  interp specs (![ starting sc pc ss * P ] (stn, st))
  -> exists pre, specs pc = Some pre
    /\ interp specs (![ P ] (stn, st))
    /\ forall sched_ pre_exit pc_exit stn_st' vs,
      interp specs ([| stn.(Labels) ("scheduler"!"exit")%SP = Some pc_exit |]
        /\ [| (fst stn_st').(Labels) = stn.(Labels) |]
        /\ Cptr pc_exit (fun x => pre_exit x)
        /\ [| sel vs "sc" = sc |]
        /\ ![ locals ("rp" :: "sc" :: nil) vs ss stn_st'#Sp * mallocHeap 0 * sched_ ] stn_st'
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
  instantiate (2 := fun p => sched_ (fst p) (snd p)).
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

  post.
  replace x0 with (length ("rp" :: "sc" :: nil) + (x0 - length ("rp" :: "sc" :: nil))) in H0.
  assert (NoDup ("rp" :: "sc" :: nil)) by NoDup.
  evaluate hints; sep hints; auto.
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
  apply andL; apply injL; intro.
  apply andL; apply cptrL; intro.
  apply andL; apply swap.
  apply andL; apply injL; intro.
  apply unandL.
  repeat apply andR.
  apply injR; eauto.
  apply injR; eauto.
  apply cptrR; eauto.
  Focus 2.
  apply andL; apply implyR.
  descend.
  rewrite H13.
  descend.
  clear.
  step auto_ext.
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
  eauto.
  2: auto.
  Focus 2.
  instantiate (1 := sched (sel x6 "sc")); simpl.
  descend; step hints.
  apply any_easy.

  unfold localsInvariantCont; simpl; intros.
  step auto_ext.
  step auto_ext.
  instantiate (1 := fun p => fr_exit (fst p) (snd p)).
  descend.
  instantiate (1 := vs).
  rewrite H6.
  clear.
  step auto_ext.
Qed.
