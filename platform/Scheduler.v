Require Import AutoSep Malloc Bags ThreadQueues SinglyLinkedList.
Import W_Bag.
Export AutoSep Malloc W_Bag.

Lemma equiv_empty : forall ls, empty %= bagify ls
  -> ls = nil.
  unfold bagify; destruct ls; simpl; intuition.
  eapply equiv_symm in H; eapply equiv_trans in H; [ | eapply equiv_symm; eapply add_something ].
  elimtype False.
  generalize dependent (fold_left add ls empty); intros.
  bags.
  specialize (H a).
  destruct (W_Key.eq_dec a a); congruence.
Qed.

Theorem starB_empty_fwd : forall P, starB P empty ===> Emp.
  unfold starB; intros; intro.
  apply himp_ex_p; intros.
  apply himp_star_pure_c; intro H.
  apply equiv_empty in H; subst.
  reflexivity.
Qed.


Module Type S.
  Parameter globalSched : W.

  Parameter globalInv : HProp.
End S.

Module Make(M : S).
Import M.

Definition allIn (b : bag) := List.Forall (fun p => p %in b).
Definition allInOrZero (b : bag) := List.Forall (fun p => p = $0 \/ p %in b).

Definition files (ts : bag) : bag -> HProp :=
  starB (fun p => Ex fd, Ex inq, Ex outq, (p ==*> fd, inq, outq) * [| inq %in ts |] * [| outq %in ts |])%Sep.

Module M''.
  Definition world := bag.

  Definition evolve : bag -> bag -> Prop := incl.

  Theorem evolve_refl : forall w, evolve w w.
    red; bags.
  Qed.

  Theorem evolve_trans : forall w1 w2 w3, evolve w1 w2 -> evolve w2 w3 -> evolve w1 w3.
    unfold evolve in *; bags.
  Qed.

  Open Scope Sep_scope.

  Definition globalInv (ts : bag) (w : world) : HProp :=
    (* The scheduler entry point *)
    Ex p, globalSched =*> p
    * Ex ready, Ex free, Ex wait, Ex waitLen, (p ==*> ready, free, wait, waitLen)

    (* The ready queue is a valid thread queue, for threads ready to run immediately. *)
    * [| ready %in ts |]

    (* The free list stores available file pointers. *)
    * Ex freeL, sll freeL free * [| allIn w freeL |]

    (* Each available file pointer stores a record of a file descriptor and input/output thread queues. *)
    * files ts w

    (* There is an array correspoinding to outstanding declare() calls, mapping each to a queue that should be poked when its event is enabled. *)
    * Ex waitL, array waitL wait * [| allInOrZero ts waitL |]
      * [| length waitL = wordToNat waitLen |]
      * [| (length waitL >= 2)%nat |] * [| wait <> 0 |] * [| freeable wait (length waitL) |]

    (* Finally, the application-specific global invariant holds. *)
    * globalInv.
End M''.

Module Q' := ThreadQueues.Make(M'').
Import M'' Q'.
Export M'' Q'.

Module Type SCHED.
  Parameter sched : bag -> HProp.
  (* Parameter is available file pointers. *)

  Axiom sched_fwd : forall fs, sched fs ===>
    Ex ts, Ex p, globalSched =*> p
    * Ex ready, Ex free, Ex wait, Ex waitLen, (p ==*> ready, free, wait, waitLen)
    * [| ready %in ts |]
    * Ex freeL, sll freeL free * [| allIn fs freeL |]
    * files ts fs
    * Ex waitL, array waitL wait * [| allInOrZero ts waitL |] * [| length waitL = wordToNat waitLen |]
      * [| (length waitL >= 2)%nat |] * [| wait <> 0 |] * [| freeable wait (length waitL) |]
    * tqs ts fs.

  Axiom sched_bwd : forall fs,
    (Ex ts, Ex p, globalSched =*> p
     * Ex ready, Ex free, Ex wait, Ex waitLen, (p ==*> ready, free, wait, waitLen)
     * [| ready %in ts |]
     * Ex freeL, sll freeL free * [| allIn fs freeL |]
     * files ts fs
     * Ex waitL, array waitL wait * [| allInOrZero ts waitL |] * [| length waitL = wordToNat waitLen |]
       * [| (length waitL >= 2)%nat |] * [| wait <> 0 |] * [| freeable wait (length waitL) |]
     * tqs ts fs)
    ===> sched fs.

  Axiom files_empty_fwd : forall ts, files ts empty ===> Emp.
  Axiom files_empty_bwd : forall ts, Emp ===> files ts empty.
End SCHED.

Module Sched : SCHED.
  Open Scope Sep_scope.

  Definition sched fs :=
    Ex ts, Ex p, globalSched =*> p
    * Ex ready, Ex free, Ex wait, Ex waitLen, (p ==*> ready, free, wait, waitLen)
    * [| ready %in ts |]
    * Ex freeL, sll freeL free * [| allIn fs freeL |]
    * files ts fs
    * Ex waitL, array waitL wait * [| allInOrZero ts waitL |] * [| length waitL = wordToNat waitLen |]
      * [| (length waitL >= 2)%nat |] * [| wait <> 0 |] * [| freeable wait (length waitL) |]
    * tqs ts fs.

  Theorem sched_fwd : forall fs, sched fs ===>
    Ex ts, Ex p, globalSched =*> p
    * Ex ready, Ex free, Ex wait, Ex waitLen, (p ==*> ready, free, wait, waitLen)
    * [| ready %in ts |]
    * Ex freeL, sll freeL free * [| allIn fs freeL |]
    * files ts fs
    * Ex waitL, array waitL wait * [| allInOrZero ts waitL |] * [| length waitL = wordToNat waitLen |]
      * [| (length waitL >= 2)%nat |] * [| wait <> 0 |] * [| freeable wait (length waitL) |]
    * tqs ts fs.
    intros; apply Himp_refl.
  Qed.

  Theorem sched_bwd : forall fs,
    (Ex ts, Ex p, globalSched =*> p
     * Ex ready, Ex free, Ex wait, Ex waitLen, (p ==*> ready, free, wait, waitLen)
     * [| ready %in ts |]
     * Ex freeL, sll freeL free * [| allIn fs freeL |]
     * files ts fs
     * Ex waitL, array waitL wait * [| allInOrZero ts waitL |] * [| length waitL = wordToNat waitLen |]
       * [| (length waitL >= 2)%nat |] * [| wait <> 0 |] * [| freeable wait (length waitL) |]
     * tqs ts fs)
     ===> sched fs.
    intros; apply Himp_refl.
  Qed.

  Theorem files_empty_fwd : forall ts, files ts empty ===> Emp.
    intros; apply starB_empty_fwd.
  Qed.

  Theorem files_empty_bwd : forall ts, Emp ===> files ts empty.
    intros; apply starB_empty_bwd.
  Qed.
End Sched.

Import Sched.
Export Sched.

Lemma allocate_array' : forall p n offset,
  allocated p offset n ===> Ex ls, [| length ls = n |] * array ls (p ^+ $(offset)).
  induction n; simpl.

  sepLemma.
  instantiate (1 := nil); auto.
  sepLemma.

  intros; sepLemmaLhsOnly.
  etransitivity; [ eapply himp_star_frame; [ apply IHn | reflexivity ] | ]; clear IHn.
  sepLemmaLhsOnly.
  apply himp_ex_c; exists (x :: x0).
  sepLemma.
  etransitivity; [ eapply himp_star_frame; [ apply ptsto32m'_in | reflexivity ] | ].
  etransitivity; [ | apply ptsto32m'_out ].
  simpl.
  destruct offset; simpl.
  replace (p ^+ natToW 0) with p by words; sepLemma.
  etransitivity; [ | apply ptsto32m'_shift_base ].
  instantiate (1 := 4); reflexivity.
  auto.
  replace (p ^+ natToW (S offset) ^+ $0) with (p ^+ natToW (S offset)) by words.
  sepLemma.
  etransitivity; [ | apply ptsto32m'_shift_base ].
  instantiate (1 := 4).
  rewrite <- wplus_assoc.
  rewrite <- natToW_plus.
  replace (S offset + 4) with (S (S (S (S (S offset))))) by omega.
  reflexivity.
  auto.
Qed.

Inductive make_array (sz : nat) : Prop := MakeArray.

Hint Constructors make_array.

Lemma allocate_array : forall p n,
  make_array n
  -> p =?> n ===> Ex ls, [| length ls = n |] * array ls p.
  intros; eapply Himp_trans; [ apply allocate_array' | ].
  replace (p ^+ $0) with p by words; apply Himp_refl.
Qed.

Theorem tqs_empty_bwd : forall w, Emp ===> tqs empty w.
  intros; rewrite tqs_eq; apply tqs'_empty_bwd.
Qed.

Definition hints : TacPackage.
  prepare (sched_fwd, SinglyLinkedList.nil_fwd, SinglyLinkedList.cons_fwd, allocate_array, files_empty_fwd)
  (sched_bwd, SinglyLinkedList.nil_bwd, SinglyLinkedList.cons_bwd, tqs_empty_bwd, files_empty_bwd).
Defined.

Definition starting (pc : W) (ss : nat) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ [| semp m |]
    /\ Al st : settings * state, Al vs, Al fs,
      [| st#Sp <> 0 /\ freeable st#Sp (1 + ss) |]
      /\ ![ ^[locals ("rp" :: nil) vs ss st#Sp * sched fs * M.globalInv * mallocHeap 0] ] st
      ---> #0 st)%PropX.

Lemma starting_elim : forall specs pc ss P stn st,
  interp specs (![ starting pc ss * P ] (stn, st))
  -> (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs fs, interp specs ([| stn_st#Sp <> 0 /\ freeable stn_st#Sp (1 + ss) |]
      /\ ![ locals ("rp" :: nil) vs ss stn_st#Sp
      * sched fs * M.globalInv * mallocHeap 0 ] stn_st
    ---> pre stn_st)%PropX).
  cptr.
  generalize (split_semp _ _ _ H0 H); intros; subst; auto.
  rewrite <- sepFormula_eq; descend; step auto_ext.
  auto.
  step auto_ext.
Qed.

Local Hint Resolve split_a_semp_a semp_smem_emp.

Lemma starting_intro : forall specs pc ss P stn st,
  (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs fs, interp specs ([| stn_st#Sp <> 0 /\ freeable stn_st#Sp (1 + ss) |]
      /\ ![ locals ("rp" :: nil) vs ss stn_st#Sp
      * sched fs * M.globalInv * mallocHeap 0 ] stn_st
    ---> pre stn_st)%PropX)
  -> interp specs (![ starting pc ss * P ] (stn, st)).
  cptr.
Qed.

Lemma other_starting_intro : forall specs ts w pc ss P stn st,
  (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs ts' w', interp specs ([| ts %<= ts' |]
      /\ [| M''.evolve w w' |]
      /\ [| stn_st#Sp <> 0 /\ freeable stn_st#Sp (1 + ss) |]
      /\ ![ locals ("rp" :: nil) vs ss stn_st#Sp
      * tqs ts' w' * M''.globalInv ts' w' * mallocHeap 0 ] stn_st
    ---> pre stn_st)%PropX)
  -> interp specs (![ Q'.starting ts w pc ss * P ] (stn, st)).
  cptr.
Qed.


Local Notation "'PREexit' [ vs ] pre" := (Q'.Q.localsInvariantExit (fun vs _ => pre%qspec%Sep))
  (at level 89).

Definition initS : spec := SPEC reserving 18
  PRE[_] globalSched =?> 1 * mallocHeap 0
  POST[R] sched empty * mallocHeap 0.

Definition spawnS : spec := SPEC("pc", "ss") reserving 26
  Al fs,
  PRE[V] [| V "ss" >= $2 |] * sched fs * starting (V "pc") (wordToNat (V "ss") - 1) * mallocHeap 0
  POST[_] sched fs * mallocHeap 0.

Definition exitS : spec := SPEC("sc", "ss") reserving 2
  Al fs,
  PREexit[V] [| V "ss" >= $3 |] * sched fs * M.globalInv * mallocHeap 0.

Definition yieldS : spec := SPEC reserving 25
  Al fs,
  PRE[_] sched fs * M.globalInv * mallocHeap 0
  POST[_] Ex fs', [| fs %<= fs' |] * sched fs' * M.globalInv * mallocHeap 0.

Definition initSize := 2.

Theorem initSize_eq : initSize = 2.
  auto.
Qed.

Opaque initSize.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "threadqs"!"alloc" @ [Q'.allocS], "threadqs"!"spawn" @ [Q'.spawnS],
                           "threadqs"!"exit" @ [Q'.exitS], "threadqs"!"yield" @ [Q'.yieldS] ]]
  bmodule "scheduler" {{
    bfunction "init"("root", "ready", "wait") [initS]
      "root" <-- Call "malloc"!"malloc"(0, 4)
      [PRE[_, R] globalSched =?> 1 * R =?> 4 * mallocHeap 0
       POST[_] sched empty * mallocHeap 0];;

      globalSched *<- "root";;

      Assert [PRE[V] globalSched =*> V "root" * V "root" =?> 4 * mallocHeap 0 * tqs empty empty
        POST[_] sched empty * mallocHeap 0];;

      "ready" <-- Call "threadqs"!"alloc"()
      [PRE[V, R] globalSched =*> V "root" * V "root" =?> 4 * tqs (empty %+ R) empty * mallocHeap 0
       POST[_] sched empty * mallocHeap 0];;

      "wait" <-- Call "malloc"!"malloc"(0, initSize)
      [PRE[V, R] R =?> initSize * [| R <> 0 |] * [| freeable R initSize |]
         * globalSched =*> V "root" * V "root" =?> 4
         * tqs (empty %+ V "ready") empty
       POST[_] sched empty];;

      Note [make_array initSize];;

      Assert [Al waitL,
        PRE[V] array waitL (V "wait") * [| length waitL = 2 |] * [| V "wait" <> 0 |] * [| freeable (V "wait") 2 |]
          * [| ($0 < natToW (length waitL))%word |]
          * globalSched =*> V "root" * V "root" =?> 4 * tqs (empty %+ V "ready") empty
        POST[_] sched empty];;

      "wait"+0 *<- 0;;

      Assert [Al waitL,
        PRE[V] array waitL (V "wait") * [| length waitL = 2 |] * [| V "wait" <> 0 |] * [| freeable (V "wait") 2 |]
          * [| ($1 < natToW (length waitL))%word |] * [| Array.selN waitL 0 = $0 |]
          * globalSched =*> V "root" * V "root" =?> 4 * tqs (empty %+ V "ready") empty
        POST[_] sched empty];;

      "wait"+4 *<- 0;;

      "root" *<- "ready";;
      "root"+4 *<- 0;;
      "root"+8 *<- "wait";;
      "root"+12 *<- 2;;
      Return 0
    end with bfunction "spawn"("pc", "ss", "root") [spawnS]
      "root" <-* globalSched;;
      "root" <-* "root";;

      Call "threadqs"!"spawn"("root", "pc", "ss")
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
    end (*with bfunctionNoRet "exit"("sc", "ss") [exitS]
      "sc" <-* globalSched;;
      Goto "threadqs"!"exit"
    end with bfunction "yield"() [yieldS]
      Call "threadqs"!"yield"($[globalSched], $[globalSched])
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
    end*)
  }}.

Ltac finish := auto;
  try solve [ try rewrite initSize_eq in *;
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H
           end; reflexivity || auto 2 ].

Lemma selN_updN_eq : forall v a n,
  (n < length a)%nat
  -> Array.selN (Array.updN a n v) n = v.
  induction a; destruct n; simpl; intuition.
Qed.

Lemma selN_upd_eq : forall v a n,
  (n < length a)%nat
  -> goodSize (length a)
  -> Array.selN (Array.upd a (natToW n) v) n = v.
  intros; rewrite upd_updN.
  apply selN_updN_eq; auto.
  eauto using goodSize_weaken.
Qed.

Local Hint Extern 1 (selN _ _ = _) => apply selN_upd_eq; solve [ finish ].

Ltac t' := unfold globalInv; sep hints; finish.

Ltac spawn := post; evaluate hints;
  match goal with
    | [ H : interp _ _ |- _ ] =>
      toFront ltac:(fun P => match P with
                               | starting _ _ => idtac
                             end) H; apply starting_elim in H; post; descend
  end;
  try (toFront_conc ltac:(fun P => match P with
                                     | Q'.starting _ _ _ _ => idtac
                                   end); apply other_starting_intro; descend;
  try match goal with
        | [ |- interp _ (![ _ ] _) ] => step hints
      end);
  (try (repeat (apply andL; apply injL; intro);
    match goal with
      | [ H : forall stn_st : ST.settings * state, _ |- _ ] =>
        eapply Imply_trans; [ | apply H ]; clear H
    end); t').

Ltac t := solve [
  match goal with
    | [ |- context[starting] ] =>
      match goal with
        | [ |- context[Q'.starting] ] => spawn
      end
    | _ => t'
  end ].

Local Hint Extern 1 (@eq W _ _) => words.
Local Hint Immediate evolve_refl.

Hint Rewrite upd_length : sepFormula.

Local Hint Unfold allIn allInOrZero.

Local Hint Extern 1 (List.Forall _ (Array.upd _ (natToW 1) (natToW 0))) =>
  rewrite upd_updN by auto;
    repeat match goal with
             | [ ls : list W |- _ ] =>
               match goal with
                 | [ _ : length ?E = _ |- _ ] =>
                   match E with
                     | context[ls] => destruct ls; try discriminate
                   end
               end
           end; simpl in *.

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

(*
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
  step hints.
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

  post.
  evaluate hints.
  descend.
  2: instantiate (8 := upd x0 "sc" x1); unfold globalInv; descend; step hints.
  rewrite H0; assumption.

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
*)
Qed.

Transparent initSize.

End Make.
