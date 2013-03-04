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
    Ex p, Ex ready, Ex free, Ex wait, Ex waitLen, Ex freeL, Ex waitL,
    
    (* The scheduler entry point *)
    globalSched =*> p * (p ==*> ready, free, wait, waitLen)

    (* The ready queue is a valid thread queue, for threads ready to run immediately. *)
    * [| ready %in ts |]

    (* The free list stores available file pointers. *)
    * sll freeL free * [| allIn w freeL |]

    (* Each available file pointer stores a record of a file descriptor and input/output thread queues. *)
    * files ts w

    (* There is an array correspoinding to outstanding declare() calls, mapping each to a queue that should be poked when its event is enabled. *)
    * array waitL wait * [| allInOrZero ts waitL |]
      * [| length waitL = wordToNat waitLen |]
      * [| wait <> 0 |] * [| freeable wait (length waitL) |]

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
      * [| wait <> 0 |] * [| freeable wait (length waitL) |]
    * tqs ts fs.

  Axiom sched_bwd : forall fs,
    (Ex ts, Ex p, globalSched =*> p
     * Ex ready, Ex free, Ex wait, Ex waitLen, (p ==*> ready, free, wait, waitLen)
     * [| ready %in ts |]
     * Ex freeL, sll freeL free * [| allIn fs freeL |]
     * files ts fs
     * Ex waitL, array waitL wait * [| allInOrZero ts waitL |] * [| length waitL = wordToNat waitLen |]
       * [| wait <> 0 |] * [| freeable wait (length waitL) |]
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
      * [| wait <> 0 |] * [| freeable wait (length waitL) |]
    * tqs ts fs.

  Theorem sched_fwd : forall fs, sched fs ===>
    Ex ts, Ex p, globalSched =*> p
    * Ex ready, Ex free, Ex wait, Ex waitLen, (p ==*> ready, free, wait, waitLen)
    * [| ready %in ts |]
    * Ex freeL, sll freeL free * [| allIn fs freeL |]
    * files ts fs
    * Ex waitL, array waitL wait * [| allInOrZero ts waitL |] * [| length waitL = wordToNat waitLen |]
      * [| wait <> 0 |] * [| freeable wait (length waitL) |]
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
       * [| wait <> 0 |] * [| freeable wait (length waitL) |]
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

Definition yieldS : spec := SPEC reserving 28
  Al fs,
  PRE[_] sched fs * M.globalInv * mallocHeap 0
  POST[_] Ex fs', [| fs %<= fs' |] * sched fs' * M.globalInv * mallocHeap 0.

Definition pickNextS : spec := SPEC reserving 13
  Al p, Al ready, Al free, Al wait, Al waitLen, Al ts, Al fs, Al waitL,
  PRE[_] globalSched =*> p * (p ==*> ready, free, wait, waitLen)
    * tqs ts fs * [| ready %in ts |]
    * array waitL wait * [| allInOrZero ts waitL |]
    * [| length waitL = wordToNat waitLen |] * mallocHeap 0
  POST[R] [| R %in ts |]
    * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
    * tqs ts fs * [| ready %in ts |]
    * array waitL wait * [| allInOrZero ts waitL |]
    * [| length waitL = wordToNat waitLen |] * mallocHeap 0.

Definition initSize := 2.

Theorem initSize_eq : initSize = 2.
  auto.
Qed.

Opaque initSize.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "threadqs"!"alloc" @ [Q'.allocS], "threadqs"!"spawn" @ [Q'.spawnS],
                           "threadqs"!"exit" @ [Q'.exitS], "threadqs"!"yield" @ [Q'.yieldS],
                           "threadqs"!"isEmpty" @ [Q'.isEmptyS],

                           "sys"!"abort" @ [abortS], "sys"!"close" @ [closeS],
                           "sys"!"listen" @ [listenS], "sys"!"accept" @ [acceptS],
                           "sys"!"read" @ [readS], "sys"!"write" @ [Sys.writeS],
                           "sys"!"declare" @ [declareS], "sys"!"wait" @ [Sys.waitS] ]]
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
    end*) with bfunction "yield"("root", "ready", "q") [yieldS]
      "root" <-* globalSched;;
      "ready" <-* "root";;

      "q" <-- Call "scheduler"!"pickNext"()
      [Al ts, Al fs, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
        PRE[V, R] globalSched =*> V "root" * (V "root" ==*> V "ready", free, wait, waitLen)
          * [| V "ready" %in ts |] * [| R %in ts |]
          * sll freeL free * [| allIn fs freeL |]
          * files ts fs
          * array waitL wait * [| allInOrZero ts waitL |]
          * [| length waitL = wordToNat waitLen |]
          * [| wait <> 0 |] * [| freeable wait (length waitL) |]
          * tqs ts fs * M.globalInv * mallocHeap 0
        POST[_] Ex ts', Ex fs', Ex p, Ex ready, Ex free, Ex wait, Ex waitLen, Ex freeL, Ex waitL,
          [| ts %<= ts' |] * [| fs %<= fs' |]
          * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
          * [| ready %in ts' |]
          * sll freeL free * [| allIn fs' freeL |]
          * files ts' fs'
          * array waitL wait * [| allInOrZero ts' waitL |]
          * [| length waitL = wordToNat waitLen |]
          * [| wait <> 0 |] * [| freeable wait (length waitL) |]
          * tqs ts' fs' * M.globalInv * mallocHeap 0 ];;

      Call "threadqs"!"yield"("ready", "q")
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
    end with bfunction "pickNext"("root", "ready", "wait", "waitLen", "blocking", "n") [pickNextS]
      "root" <-* globalSched;;
      "ready" <-* "root";;

      "blocking" <-- Call "threadqs"!"isEmpty"("ready")
      [Al free, Al wait, Al waitLen, Al ts, Al fs, Al waitL,
        PRE[V] globalSched =*> V "root" * (V "root" ==*> V "ready", free, wait, waitLen)
          * tqs ts fs * [| V "ready" %in ts |]
          * array waitL wait * [| allInOrZero ts waitL |]
          * [| length waitL = wordToNat waitLen |]
        POST[R] [| R %in ts |]
          * tqs ts fs * globalSched =*> V "root" * (V "root" ==*> V "ready", free, wait, waitLen)
          * array waitL wait ];;

      "n" <-- Call "sys"!"wait"("blocking")
      [Al free, Al wait, Al waitLen, Al ts, Al waitL,
        PRE[V] globalSched =*> V "root" * (V "root" ==*> V "ready", free, wait, waitLen)
          * [| V "ready" %in ts |]
          * array waitL wait * [| allInOrZero ts waitL |]
          * [| length waitL = wordToNat waitLen |]
        POST[R] [| R %in ts |]
          * globalSched =*> V "root" * (V "root" ==*> V "ready", free, wait, waitLen)
          * array waitL wait ];;

      "wait" <-* "root"+8;;
      "waitLen" <-* "root"+12;;

      If ("n" < "waitLen") {
        Assert [Al free, Al ts, Al waitL,
          PRE[V] globalSched =*> V "root" * (V "root" ==*> V "ready", free, V "wait", V "waitLen")
          * [| V "ready" %in ts |] * [| allInOrZero ts waitL |]
          * array waitL (V "wait") * [| (V "n" < natToW (length waitL))%word |]
        POST[R] [| R %in ts |]
          * globalSched =*> V "root" * (V "root" ==*> V "ready", free, V "wait", V "waitLen")
          * array waitL (V "wait") ];;

        "n" <- 4 * "n";;
        "wait" <-* "wait" + "n";;

        If ("wait" = 0) {
          Call "sys"!"abort"()
          [PREonly[_] [| False |] ]
        } else {
          Return "wait"
        }
      } else {
        Return "ready"
      }
    end
  }}.

Ltac finish := auto;
  try solve [ try rewrite initSize_eq in *;
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H
           end; reflexivity || eauto 2 ].

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


Lemma breakout : forall A (P : A -> _) Q R x specs,
  (forall v, interp specs (![P v * Q] x ---> R)%PropX)
  -> interp specs (![exB P * Q] x ---> R)%PropX.
  rewrite sepFormula_eq; propxFo.
  unfold sepFormula_def, exB, ex.
  simpl.
  repeat (apply existsL; intros); step auto_ext.
  apply unandL.
  eapply Imply_trans; try apply H; clear H.
  do 2 eapply existsR.
  simpl.
  repeat apply andR.
  apply injR; eauto.
  apply andL; apply implyR.
  apply Imply_refl.
  apply andL; apply swap; apply implyR.
  apply Imply_refl.
Qed.

Ltac exBegone :=
  match goal with
    | [ |- interp ?specs (![ ?P ] ?x ---> ?Q)%PropX ] =>
      toFront' ltac:(fun R => match R with
                                | exB _ => idtac
                              end) P
      ltac:(fun it P' =>
        apply Imply_trans with (![ it * P'] x)%PropX; [ step auto_ext | ])
  end; repeat match goal with
                | [ |- interp _ (![ exB _ * _] _ ---> _)%PropX ] => apply breakout; intro
              end.


Ltac t := solve [
  match goal with
    | [ |- context[starting] ] =>
      match goal with
        | [ |- context[Q'.starting] ] => spawn
      end
    | [ |- context[evolve] ] =>
      unfold globalInv; post; evaluate hints; descend; [ step hints | step hints | ];
        descend; step hints;
        repeat ((apply andL; apply injL) || apply existsL; intro); descend;
          exBegone; t'
    | _ => t'
  end ].

Local Hint Extern 1 (@eq W _ _) => words.
Local Hint Immediate evolve_refl.

Hint Rewrite upd_length : sepFormula.

Local Hint Extern 1 (allInOrZero _ nil) => constructor.
Local Hint Extern 1 (allInOrZero _ (_ :: _)) => constructor.

Local Hint Extern 1 (allIn empty _) => constructor.

Local Hint Extern 1 (allInOrZero _ (Array.upd _ (natToW 1) (natToW 0))) =>
  hnf; rewrite upd_updN by auto;
    repeat match goal with
             | [ ls : list W |- _ ] =>
               match goal with
                 | [ _ : length ?E = _ |- _ ] =>
                   match E with
                     | context[ls] => destruct ls; try discriminate
                   end
               end
           end; simpl in *.

Local Hint Extern 1 (freeable _ _) => congruence.
Local Hint Extern 1 (himp _ _ (sll nil (natToW 0))) => solve [ step hints ].

Lemma length_ok : forall u v n,
  u < v
  -> n = wordToNat v
  -> u < natToW n.
  intros; subst; unfold natToW; rewrite natToWord_wordToNat; auto.
Qed.

Local Hint Immediate length_ok.

Lemma selN_In : forall ls n,
  (n < length ls)%nat
  -> In (Array.selN ls n) ls.
  induction ls; destruct n; simpl; intuition.
Qed.

Lemma sel_In : forall ls n,
  n < natToW (length ls)
  -> goodSize (length ls)
  -> In (Array.sel ls n) ls.
  unfold Array.sel; intros; apply selN_In; nomega.
Qed.    

Lemma found_queue : forall x ls i b,
  x = Array.sel ls i
  -> Array.sel ls i <> 0
  -> allInOrZero b ls
  -> i < natToW (length ls)
  -> goodSize (length ls)
  -> x %in b.
  intros; subst.
  eapply Forall_forall in H1; [ | eauto using sel_In ].
  tauto.
Qed.

Local Hint Extern 1 (_ %in _) =>
  eapply found_queue; [ eassumption | eassumption | eassumption | eassumption | eauto ].

Lemma allIn_monotone : forall b ls b',
  allIn b ls
  -> b %<= b'
  -> allIn b' ls.
  intros; eapply Forall_weaken; eauto.
  bags.
  specialize (H0 x); omega.
Qed.

Local Hint Immediate allIn_monotone.

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
Qed.

Transparent initSize.

End Make.
