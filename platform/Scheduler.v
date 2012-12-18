Require Import AutoSep Bags Malloc Queue.

Set Implicit Arguments.


Section starL.
  Variable A : Type.
  Variable P : A -> HProp.

  Open Scope Sep_scope.

  Fixpoint starL (ls : list A) : HProp :=
    match ls with
      | nil => Emp
      | x :: ls => P x * starL ls
    end.
End starL.

Section starB.
  Definition bagify (ls : list (W * W)) : bag :=
    fold_left add ls empty.

  Definition predB := W * W -> HProp.
  Variable P : predB.

  Open Scope Sep_scope.

  Definition starB (b : bag) : HProp :=
    Ex ls, [| b %= bagify ls |] * starL P ls.

  Ltac to_himp := repeat intro.
  Ltac from_himp := match goal with
                      | [ |- interp ?specs (?p ?x ?y ---> ?q ?x ?y) ] =>
                        generalize dependent y; generalize dependent x; generalize dependent specs;
                          change (p ===> q)
                    end.

  Theorem starB_empty_bwd : Emp ===> starB empty.
    to_himp; apply existsR with nil; from_himp; sepLemma.
  Qed.

  Lemma exists_starL_fwd : forall A (P : A -> _) Q,
    (Ex x, P x) * Q ===> Ex x, P x * Q.
    sepLemma.
  Qed.

  Lemma equiv_symm : forall b1 b2,
    b1 %= b2
    -> b2 %= b1.
    unfold equiv; firstorder.
  Qed.

  Lemma equiv_trans : forall b1 b2 b3,
    b1 %= b2
    -> b2 %= b3
    -> b1 %= b3.
    unfold equiv; firstorder.
  Qed.

  Lemma bagify_cong : forall ls b1 b2,
    b1 %= b2
    -> fold_left add ls b1 %= fold_left add ls b2.
    induction ls; simpl; intuition.
  Qed.

  Lemma add_something : forall v ls b,
    fold_left add ls (b %+ v) %= fold_left add ls b %+ v.
    induction ls; simpl; intuition.
    eapply equiv_trans; [ | apply IHls ].
    apply bagify_cong; auto.
  Qed.

  Theorem starB_add_bwd : forall b v, starB b * P v ===> starB (b %+ v).
    intros; eapply Himp_trans; [ apply exists_starL_fwd | ]; cbv beta.
    to_himp; apply existsL; intro ls; apply existsR with (v :: ls); from_himp.
    simpl; generalize (starL P ls); generalize (P v); sepLemma.
    unfold bagify in *; simpl.
    apply equiv_symm; eapply equiv_trans; [ apply add_something | ]; auto.
  Qed.

  Lemma exists_starR_bwd : forall P A (Q : A -> _),
    Ex x, P * Q x ===> P * (Ex x, Q x).
    sepLemma.
  Qed.

  Fixpoint nuke (p : W * W) (ls : list (W * W)) : list (W * W) :=
    match ls with
      | nil => nil
      | p' :: ls => if W_W_dec p p' then ls else p' :: nuke p ls
    end.

  Lemma starL_del_fwd : forall v ls, In v ls
    -> starL P ls ===> P v * starL P (nuke v ls).
    induction ls; unfold bagify in *; simpl in *; intuition subst.
    destruct (W_W_dec v v); apply Himp_refl || tauto.
    destruct (W_W_dec v (a0, b)); subst; try apply Himp_refl.
    simpl.
    eapply Himp_trans.
    apply Himp_star_frame; [ apply Himp_refl | apply H ].
    generalize (starL P (nuke v ls)); generalize (P (a0, b)); generalize (P v); sepLemma.
  Qed.

  Lemma del_something : forall v ls b,
    v %in b
    -> fold_left add ls (b %- v) %= fold_left add ls b %- v.
    induction ls; simpl; intuition.
    eapply equiv_trans; [ | apply IHls ].
    apply bagify_cong; auto.
    auto.
  Qed.

  Lemma bagify_nuke' : forall v ls, In v ls
    -> forall b, fold_left add (nuke v ls) b %= fold_left add ls b %- v.
    induction ls; simpl; intuition subst.
    destruct (W_W_dec v v); intuition.
    eapply equiv_trans; [ | apply del_something ].
    apply bagify_cong; auto.
    auto.
    destruct (W_W_dec v (a0, b)); subst.
    eapply equiv_trans; [ | apply del_something ].
    apply bagify_cong; auto.
    auto.
    simpl; auto.
  Qed.

  Lemma bagify_nuke : forall v ls, In v ls
    -> bagify (nuke v ls) %= bagify ls %- v.
    intros; apply bagify_nuke'; auto.
  Qed.

  Lemma bagify_In' : forall v ls b b',
    v %in b
    -> b %= fold_left add ls b'
    -> In v ls \/ v %in b'.
    unfold bagify; induction ls; simpl; intuition.
    eapply IHls in H; [ | eauto ].
    intuition (eauto; bags).
  Qed.

  Lemma bagify_In : forall v ls b,
    v %in b
    -> b %= bagify ls
    -> In v ls.
    intros.
    eapply bagify_In' in H0; eauto.
    intuition bags.
  Qed.    

  Hint Resolve bagify_In bagify_nuke.

  Theorem starB_del_fwd : forall b v, v %in b
    -> starB b ===> P v * starB (b %- v).
    intros; eapply Himp_trans; [ | apply exists_starR_bwd ]; cbv beta.
    to_himp; apply existsL; intro ls; apply existsR with (nuke v ls).
    specialize (starL_del_fwd v ls);
      generalize (starL P ls); generalize (P v); generalize (starL P (nuke v ls)).
    intros; from_himp.
    sepLemma.
    eapply equiv_trans; [ | apply equiv_symm; apply bagify_nuke ].
    auto.
    eauto.
    transitivity (h0 * h); eauto.
    sepLemma.
  Qed.
End starB.


(** * The actual scheduler (will later move above stuff to Bags) *)

(* What does it mean for a program counter to be valid for a suspended thread? *)

Definition susp (sc pc sp : W) : HProp := fun s m =>
  (ExX : settings * state, Cptr pc #0
    /\ ExX : settings * smem, #0 (s, m)
    /\ AlX : W * settings * smem, Al pc_exit,
      [| s.(Labels) ("scheduler"!"exit")%SP = Some pc_exit |]
      /\ Cptr pc_exit (st ~> ExX (* fr *) : settings * smem, Ex vs : vals,
        ![^[locals ("rp" :: "sc" :: "rem" :: nil) vs 0 st#Sp]
          * ((fun s m => Lift (Var0 (sel vs "sc", s, m))) * #0)] st)
      /\ Al st : settings * state, 
        [| st#Sp = sp |]
        /\ ![ #1 * (fun s m => Var0 (sc, s, m)) ] st
        ---> #2 st)%PropX.

Inductive mergeSusp : Prop := MS.
Inductive splitSusp : Prop := SS.

Hint Constructors mergeSusp splitSusp.

Module Type SCHED.
  Parameter susps : bag -> W -> HProp.
  Parameter sched : W -> HProp.

  Axiom susps_empty_bwd : forall sc, Emp ===> susps empty sc.
  Axiom susps_add_bwd : forall sc b pc sp, pc = pc -> mergeSusp -> susp sc pc sp * susps b sc ===> susps (b %+ (pc, sp)) sc.
  Axiom susps_del_fwd : forall sc b pc sp, (pc, sp) %in b -> susps b sc ===> susp sc pc sp * susps (b %- (pc, sp)) sc.

  Axiom sched_fwd : forall sc, sched sc ===> Ex b, Ex p, sc =*> p * (sc ^+ $4) =?> 2 * queue b p * susps b sc.
  Axiom sched_bwd : forall sc, (Ex b, Ex p, sc =*> p * (sc ^+ $4) =?> 2 * queue b p * susps b sc) ===> sched sc.
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
    Ex b, Ex p, sc =*> p * (sc ^+ $4) =?> 2 * queue b p * susps b sc.

  Theorem sched_fwd : forall sc, sched sc ===> Ex b, Ex p, sc =*> p * (sc ^+ $4) =?> 2 * queue b p * susps b sc.
    unfold sched; sepLemma.
  Qed.

  Theorem sched_bwd : forall sc, (Ex b, Ex p, sc =*> p * (sc ^+ $4) =?> 2 * queue b p * susps b sc) ===> sched sc.
    unfold sched; sepLemma.
  Qed.
End Sched.

Import Sched.
Export Sched.

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
          * queue q (V "q") * (V "sc" ^+ $4) =?> 2 * susps q (V "sc") * mallocHeap 0
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
            * ((V "sc" ^+ $4) ==*> pc, sp) * mallocHeap 0
          POST[_] [| False |] ];;

        Rp <-* "sc" + 4;;
        Sp <-* "sc" + 8;;
        IGoto* [("scheduler","exit")] Rp
      }
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Lemma propToWord_elim_not1 : forall P b,
  P \is b
  -> b <> 1
  -> ~P.
  bags.
Qed.

Local Hint Immediate propToWord_elim_not1.

Ltac t := sep hints; try (apply himp_star_frame; [ reflexivity | apply susps_del_fwd; assumption ]); eauto.

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
  (* And here is where we need to prove that it is safe to jump to an activation record. *)
  admit.
Qed.
