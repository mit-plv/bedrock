Require Import AutoSep Bags Malloc RecPred ThreadQueue.
Import W_Bag.

Set Implicit Arguments.


Module Type S.
  Variable globalInv : bag -> HProp.
End S.

Module Make(M : S).
Import M.

Module M'.
  Open Scope Sep_scope.

  Definition globalInv (p : W) : hpropB ((settings * state : Type)%type :: nil) :=
    Ex b, starB (fun p' stn sm => Var0 (stateOut (stn, sm) p')) b * ^[globalInv (b %+ p)].
End M'.

Module Q := ThreadQueue.Make(M').
Import Q.

Module Type TQS.
  Parameter tqs : bag -> HProp.

  Axiom tqs_eq : tqs = starB tq.

  Definition tqs_pick_this_one (_ : W) := tqs.

  Axiom tqs_empty_bwd : Emp ===> tqs empty.
  Axiom tqs_add_bwd : forall ts t, tqs ts * tq t ===> tqs (ts %+ t).
  Axiom tqs_del_fwd : forall ts t, t %in ts -> tqs_pick_this_one t ts ===> tq t * tqs (ts %- t).
  Axiom tqs_del_bwd : forall ts t, t %in ts -> tqs (ts %- t) * tq t ===> tqs ts.
End TQS.

Module Tqs : TQS.
  Open Scope Sep_scope.

  Definition tqs := starB tq.

  Theorem tqs_eq : tqs = starB tq.
    auto.
  Qed.

  Definition tqs_pick_this_one (_ : W) := tqs.

  Theorem tqs_empty_bwd : Emp ===> tqs empty.
    apply starB_empty_bwd.
  Qed.

  Theorem tqs_add_bwd : forall ts t, tqs ts * tq t ===> tqs (ts %+ t).
    apply starB_add_bwd.
  Qed.

  Theorem tqs_del_fwd : forall ts t, t %in ts -> tqs_pick_this_one t ts ===> tq t * tqs (ts %- t).
    apply starB_del_fwd.
  Qed.

  Theorem tqs_del_bwd : forall ts t, t %in ts -> tqs (ts %- t) * tq t ===> tqs ts.
  Admitted.
End Tqs.

Import Tqs.
Export Tqs.

Definition hints : TacPackage.
  prepare tqs_del_fwd (tqs_empty_bwd, tqs_add_bwd).
Defined.

Definition starting (pc : W) (ss : nat) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ [| semp m |]
    /\ Al st : settings * state, Al vs, Al ts,
      ![ ^[locals ("rp" :: "sc" :: nil) vs ss st#Sp * tqs ts * globalInv ts * mallocHeap 0] ] st
      ---> #0 st)%PropX.

Lemma starting_elim : forall specs pc ss P stn st,
  interp specs (![ starting pc ss * P ] (stn, st))
  -> (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs ts, interp specs (![ locals ("rp" :: "sc" :: nil) vs ss stn_st#Sp
      * tqs ts * globalInv ts * mallocHeap 0 ] stn_st
    ---> pre stn_st)%PropX).
  cptr.
  generalize (split_semp _ _ _ H0 H); intros; subst; auto.
  rewrite <- sepFormula_eq; descend; step auto_ext.
Qed.


Definition allocS : spec := SPEC reserving 15
  Al ts,
  PRE[_] tqs ts * mallocHeap 0
  POST[R] tqs (ts %+ R) * mallocHeap 0.

Definition spawnS : spec := SPEC("q", "pc", "ss") reserving 25
  Al ts,
  PRE[V] [| V "q" %in ts |] * [| V "ss" >= $2 |]
    * tqs ts * starting (V "pc") (wordToNat (V "ss") - 2) * mallocHeap 0
  POST[_] tqs ts * mallocHeap 0.

Definition m := bimport [[ "threadq"!"init" @ [Q.initS], "threadq"!"spawn" @ [Q.spawnS] ]]
  bmodule "threadqs" {{
    bfunction "alloc"("r") [allocS]
      "r" <-- Call "threadq"!"init"()
      [PRE[_, R] tq R
       POST[R'] tq R'];;
      Return "r"
    end with bfunction "spawn"("q", "pc", "ss") [spawnS]
      Call "threadq"!"spawn"("q", "pc", "ss")
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
    end
  }}.

Hint Extern 1 (@eq W _ _) => words.

Ltac t := sep hints; auto.

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

  post; evaluate hints; descend.
  change (tqs x0) with (tqs_pick_this_one (sel x2 "q") x0) in H7.
  toFront ltac:(fun P => match P with
                           | starting _ _ => idtac
                         end) H7; apply starting_elim in H7; post.
  toFront_conc ltac:(fun P => match P with
                                | Q.starting _ _ _ => idtac
                              end); apply Q.starting_intro; descend.
  2: step hints.
  step hints.
  step hints.
  descend.
  apply andL; apply swap; apply injL; intro.
  unfold ginv, M'.globalInv.
  autorewrite with sepFormula.
  match goal with
    | [ |- interp _ (![?P * exB ?Q * ?R] ?p ---> _)%PropX ] =>
      apply Imply_trans with (![Ex b, P * Q b * R] p)%PropX
  end.
  make_Himp.
  
  Lemma get_ex : forall P Q R S,
    P * Q * R * S ===> R * (P * Q * S).
    sepLemma.
  Qed.

  eapply Himp_trans; [ apply get_ex | ].
  eapply Himp_trans; [ apply Himp_ex_star | ].
  apply Himp'_ex; intro.
  apply Himp_ex_c; exists x6.

  Lemma get_ex' : forall P Q R S,
    R * (P * Q * S) ===> P * Q * R * S.
    sepLemma.
  Qed.

  apply get_ex'.

  Lemma ex_out : forall A (P : A -> HProp) p specs,
    interp specs (![exB P] p ---> Ex x, ![P x] p)%PropX.
    rewrite sepFormula_eq; unfold sepFormula_def; intros.
    apply Imply_refl.
  Qed.

  eapply Imply_trans; [ apply ex_out | ].
  apply existsL; intro.
  eapply Imply_trans; [ | apply H12 ]; clear H12.
  make_Himp.

  Lemma Himp_star_assoc' : forall P Q R,
    P * (Q * R) ===> P * Q * R.
    sepLemma.
  Qed.

  Lemma get_first : forall P Q R P' Q' R',
    P ===> P'
    -> Q * R ===> Q' * R'
    -> P * Q * R ===> P' * Q' * R'.
    intros; eapply Himp_trans; [ | apply Himp_star_assoc' ].
    eapply Himp_trans; [ apply Himp_star_assoc | ].
    apply Himp_star_frame; auto.
  Qed.

  autorewrite with sepFormula.
  apply Himp_star_frame; try apply Himp_refl.
  apply get_first.
  sepLemma.

  Lemma blergh : forall P Q R,
    P * (Q * R) ===> Q * (P * R).
    sepLemma.
  Qed.

  eapply Himp_trans; [ apply blergh | ].
  eapply Himp_trans.
  apply Himp_star_frame.
  apply starB_substH_fwd.
  apply Himp_refl.
  eapply Himp_trans.
  apply Himp_star_frame.
  instantiate (1 := tqs x6).
  rewrite tqs_eq; apply starB_weaken; intros.
  unfold Himp, himp; intros.
  unfold substH, predOut.
  simpl.
  rewrite memoryIn_memoryOut; apply Himp_refl.
  apply Himp_refl.
  instantiate (1 := x6 %+ sel x2 "q").
  intro; step hints.
  step hints.
  sep hints; auto.
  apply tqs_del_bwd; auto.

  t.
  t.
  t.
Qed.

End Make.
