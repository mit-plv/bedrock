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

Notation "#5" := (fun x => Lift (Lift (Lift (Lift (Lift (Var0 x)))))) : PropX_scope.

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

Definition any : HProp := fun _ _ => [| True |]%PropX.

Theorem any_easy : forall P, P ===> any.
  unfold any; repeat intro; step auto_ext; auto.
Qed.

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

Lemma propToWord_elim_not1 : forall P b,
  P \is b
  -> b <> 1
  -> ~P.
  bags.
Qed.

Local Hint Immediate propToWord_elim_not1.

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

  Theorem substH_lift5 : forall p' t1 t2 t3 t4 t5 p,
    substH (lift (t1 :: t2 :: t3 :: t4 :: t5 :: nil) p') p = lift (t1 :: t2 :: t3 :: t4 :: nil) p'.
    reflexivity.
  Qed.

  Theorem substH_lift6 : forall p' t1 t2 t3 t4 t5 t6 p,
    substH (lift (t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: nil) p') p = lift (t1 :: t2 :: t3 :: t4 :: t5 :: nil) p'.
    reflexivity.
  Qed.

  Hint Rewrite substH_lift5 substH_lift6 : sepFormula.
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

  (* Within [H], find a conjunct [P] such that [which P] doesn't fail, and reassociate [H]
   * to put [P] in front. *)
  Ltac toFront which H :=
    let rec toFront' P k :=
      match P with
        | SEP.ST.star ?Q ?R =>
          toFront' Q ltac:(fun it P' => k it (SEP.ST.star P' R))
          || toFront' R ltac:(fun it P' => k it (SEP.ST.star P' Q))
            || fail 2
        | _ => which P; k P (@SEP.ST.emp W (settings * state) nil)
      end in
      match type of H with
        | interp ?specs (![ ?P ] ?st) => toFront' P ltac:(fun it P' =>
          let H' := fresh in
            assert (H' : interp specs (![ SEP.ST.star it P' ] st)) by step auto_ext;
              clear H; rename H' into H)
      end.

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

  Show Existentials.
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
