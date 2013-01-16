Require Import AutoSep Malloc Bags ThreadQueues.
Import W_Bag.
Export AutoSep Malloc W_Bag.


Module Type S.
  Parameter globalSched : W.

  Parameter globalInv : HProp.
End S.

Module Make(M : S).
Import M.

Module M''.
  Definition world := unit.

  Definition evolve (_ _ : unit) := True.

  Theorem evolve_refl : forall w, evolve w w.
    red; auto.
  Qed.

  Theorem evolve_trans : forall w1 w2 w3, evolve w1 w2 -> evolve w2 w3 -> evolve w1 w3.
    red; auto.
  Qed.

  Open Scope Sep_scope.

  Definition globalInv (ts : bag) (_ : world) : HProp :=
    Ex q, [| q %in ts |] * globalSched =*> q * globalInv.
End M''.

Module Q' := ThreadQueues.Make(M'').
Import M'' Q'.
Export M'' Q'.

Module Type SCHED.
  Parameter sched : HProp.

  Axiom sched_fwd : sched ===> Ex ts, Ex q, [| q %in ts |] * globalSched =*> q * tqs ts tt.
  Axiom sched_bwd : (Ex ts, Ex q, [| q %in ts |] * globalSched =*> q * tqs ts tt) ===> sched.
End SCHED.

Module Sched : SCHED.
  Open Scope Sep_scope.

  Definition sched := Ex ts, Ex q, [| q %in ts |] * globalSched =*> q * tqs ts tt.

  Theorem sched_fwd : sched ===> Ex ts, Ex q, [| q %in ts |] * globalSched =*> q * tqs ts tt.
    unfold sched; sepLemma.
  Qed.

  Theorem sched_bwd : (Ex ts, Ex q, [| q %in ts |] * globalSched =*> q * tqs ts tt) ===> sched.
    unfold sched; sepLemma.
  Qed.
End Sched.

Import Sched.
Export Sched.

Definition hints : TacPackage.
  prepare sched_fwd sched_bwd.
Defined.

Definition starting (pc : W) (ss : nat) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ [| semp m |]
    /\ Al st : settings * state, Al vs,
      ![ ^[locals ("rp" :: nil) vs ss st#Sp * sched * M.globalInv * mallocHeap 0] ] st
      ---> #0 st)%PropX.

Lemma starting_elim : forall specs pc ss P stn st,
  interp specs (![ starting pc ss * P ] (stn, st))
  -> (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs, interp specs (![ locals ("rp" :: nil) vs ss stn_st#Sp
      * sched * M.globalInv * mallocHeap 0 ] stn_st
    ---> pre stn_st)%PropX).
  cptr.
  generalize (split_semp _ _ _ H0 H); intros; subst; auto.
  rewrite <- sepFormula_eq; descend; step auto_ext.
Qed.

Local Hint Resolve split_a_semp_a semp_smem_emp.

Lemma starting_intro : forall specs pc ss P stn st,
  (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs, interp specs (![ locals ("rp" :: nil) vs ss stn_st#Sp
      * sched * M.globalInv * mallocHeap 0 ] stn_st
    ---> pre stn_st)%PropX)
  -> interp specs (![ starting pc ss * P ] (stn, st)).
  cptr.
Qed.

Lemma other_starting_intro : forall specs ts w pc ss P stn st,
  (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs ts' w', interp specs ([| ts %<= ts' |]
      /\ [| M''.evolve w w' |]
      /\ ![ locals ("rp" :: nil) vs ss stn_st#Sp
      * tqs ts' w' * M''.globalInv ts' w' * mallocHeap 0 ] stn_st
    ---> pre stn_st)%PropX)
  -> interp specs (![ Q'.starting ts w pc ss * P ] (stn, st)).
  cptr.
Qed.


Definition initS : spec := SPEC reserving 16
  PRE[_] globalSched =?> 1 * mallocHeap 0
  POST[R] sched * mallocHeap 0.

Definition spawnS : spec := SPEC("pc", "ss") reserving 32
  PRE[V] [| V "ss" >= $2 |] * sched * starting (V "pc") (wordToNat (V "ss") - 1) * mallocHeap 0
  POST[_] sched * mallocHeap 0.

Definition exitS : spec := SPEC reserving 17
  PREonly[_] sched * M.globalInv * mallocHeap 0.

Definition yieldS : spec := SPEC reserving 24
  PRE[_] sched * M.globalInv * mallocHeap 0
  POST[_] sched * M.globalInv * mallocHeap 0.

Definition m := bimport [[ "threadqs"!"alloc" @ [Q'.allocS], "threadqs"!"spawn" @ [Q'.spawnS],
                           "threadqs"!"exit" @ [Q'.exitS], "threadqs"!"yield" @ [Q'.yieldS] ]]
  bmodule "scheduler" {{
    bfunction "init"() [initS]
      $[globalSched] <-- Call "threadqs"!"alloc"()
      [PRE[_, R] globalSched =?> 1
       POST[_] globalSched =*> R];;
      Return 0
    end with bfunction "spawn"("pc", "ss") [spawnS]
      Call "threadqs"!"spawn"($[globalSched], "pc", "ss")
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
    end with bfunction "exit"() [exitS]
      Call "threadqs"!"exit"($[globalSched])
      [PREonly[_] [| False |] ]
    end with bfunction "yield"() [yieldS]
      Call "threadqs"!"yield"($[globalSched])
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
    end
  }}.

Ltac t := abstract (unfold globalInv; sep hints; auto).

Local Hint Extern 1 (@eq W _ _) => words.
Local Hint Immediate evolve_refl.

Theorem ok : moduleOk m.
  vcgen.

  t.
  t.
  t.
  t.

  post; evaluate auto_ext.
  match goal with
    | [ H : interp ?specs (![?P] ?x) |- _ ] =>
      let H' := fresh in assert (H' : interp specs (![P * tqs empty tt] x))
        by (sepLemma; rewrite tqs_eq; apply tqs'_empty_bwd);
        clear H; rename H' into H
  end.
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
                           | starting _ _ => idtac
                         end) H7; apply starting_elim in H7; post.
  descend.
  toFront_conc ltac:(fun P => match P with
                                | Q'.starting _ _ _ _ => idtac
                              end); apply other_starting_intro; descend.
  2: step hints.
  step hints.
  repeat (apply andL; apply injL; intro).
  eapply Imply_trans; [ | apply H12 ]; clear H12.
  unfold globalInv; descend; step hints.
  eauto.
  destruct w'; step hints.
  step hints.
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

  unfold globalInv.
  post; evaluate hints; descend.
  step hints.
  auto.
  step hints.
  apply andL; apply injL; intro.
  repeat (apply existsL; intro).
  descend.

  Lemma getOutHere : forall P Q A (R : A -> _) S T,
    P * (Q * (Ex x, R x) * S) * T ===> Ex x, P * Q * R x * S * T.
    sepLemma.
  Qed.

  Lemma useHimp : forall specs P x P',
    P ===> P'
    -> interp specs (![P] x ---> ![P'] x)%PropX.
    rewrite sepFormula_eq; intros; apply H.
  Qed.

  eapply Imply_trans; [ eapply useHimp; apply getOutHere | ].

  Lemma breakout : forall A (P : A -> _) Q x specs,
    (forall v, interp specs (![P v] x ---> Q)%PropX)
    -> interp specs (![exB P] x ---> Q)%PropX.
    rewrite sepFormula_eq; propxFo.
    unfold sepFormula_def, exB, ex.
    simpl.
    apply existsL; auto.
  Qed.
    
  apply breakout; intro.
  descend; step hints.
  descend; step hints.
  descend; step hints.
  descend; step hints.
  descend; step hints.
  descend; step hints.
  auto.
  descend; step hints.
  eauto.
  destruct x8; step hints.

  t.
  t.
  t.
Qed.

End Make.
