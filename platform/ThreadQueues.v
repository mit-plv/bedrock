Require Import AutoSep Bags Malloc ThreadQueue RecPred.
Import W_Bag.

Set Implicit Arguments.


Module Type S.
  Variable world : Type.

  Variable evolve : world -> world -> Prop.
  Axiom evolve_refl : forall w, evolve w w.
  Axiom evolve_trans : forall w1 w2 w3, evolve w1 w2 -> evolve w2 w3 -> evolve w1 w3.

  Variable globalInv : bag -> world -> HProp.

  Hypothesis globalInv_extensional : forall b1 b2 w, b1 %= b2
    -> globalInv b1 w ===> globalInv b2 w.
End S.

Module Make(M : S).
Import M.

Module M'.
  Open Scope Sep_scope.

  Definition world := (bag * M.world)%type.
  Definition evolve (w1 w2 : world) :=
    fst w1 %<= fst w2
    /\ M.evolve (snd w1) (snd w2).

  Local Hint Resolve M.evolve_refl M.evolve_trans.

  Theorem evolve_refl : forall w, evolve w w.
    unfold evolve; auto.
  Qed.

  Theorem evolve_trans : forall w1 w2 w3, evolve w1 w2 -> evolve w2 w3 -> evolve w1 w3.
    unfold evolve; intuition eauto.
  Qed.

  Definition globalInv (w : world) (p : W) : hpropB (tq_args world :: nil) :=
    starB (fun p' stn sm => Var0 {| World := w; Pointer := p'; Settings := stn; Mem := sm |}) (fst w %- p) * ^[M.globalInv (fst w) (snd w)].
End M'.

Module Q := ThreadQueue.Make(M').
Import M' Q.

Module Type TQS.
  Parameter tqs' : world -> bag -> HProp.

  Axiom tqs'_eq : tqs' = fun w => starB (tq w).

  Parameter tqs : bag -> M.world -> HProp.

  Axiom tqs_eq : tqs = fun b w => tqs' (b, w) b.

  Definition tqs'_pick_this_one (_ : W) := tqs'.

  Axiom tqs'_empty_bwd : forall w, Emp ===> tqs' w empty.
  Axiom tqs'_add_bwd : forall w ts t, tqs' w ts * tq w t ===> tqs' w (ts %+ t).
  Axiom tqs'_del_fwd : forall w ts t, t %in ts -> tqs'_pick_this_one t w ts ===> tq w t * tqs' w (ts %- t).
  Axiom tqs'_del_bwd : forall w ts t, t %in ts -> tqs' w (ts %- t) * tq w t ===> tqs' w ts.

  Axiom tqs'_weaken : forall w w' b, evolve w w' -> tqs' w b ===>* tqs' w' b.
End TQS.

Module Tqs : TQS.
  Open Scope Sep_scope.

  Definition tqs' w := starB (tq w).

  Theorem tqs'_eq : tqs' = fun w => starB (tq w).
    auto.
  Qed.

  Definition tqs b w := tqs' (b, w) b.

  Theorem tqs_eq : tqs = fun b w => tqs' (b, w) b.
    auto.
  Qed.

  Definition tqs'_pick_this_one (_ : W) := tqs'.

  Theorem tqs'_empty_bwd : forall w, Emp ===> tqs' w empty.
    intros; apply starB_empty_bwd.
  Qed.

  Theorem tqs'_add_bwd : forall w ts t, tqs' w ts * tq w t ===> tqs' w (ts %+ t).
    intros; apply (starB_add_bwd (tq w)).
  Qed.

  Theorem tqs'_del_fwd : forall w ts t, t %in ts -> tqs'_pick_this_one t w ts ===> tq w t * tqs' w (ts %- t).
    intros; apply (starB_del_fwd (tq w)); auto.
  Qed.

  Theorem tqs'_del_bwd : forall w ts t, t %in ts -> tqs' w (ts %- t) * tq w t ===> tqs' w ts.
    intros; eapply Himp_trans; [ | apply (starB_del_bwd (tq w)); eauto ].
    eapply Himp_trans; [ apply Himp_star_comm | ].
    apply Himp_refl.
  Qed.

  Theorem tqs'_weaken : forall w w' b, evolve w w' -> tqs' w b ===>* tqs' w' b.
    intros; apply starB_weaken_weak; intros.
    apply tq_weaken; unfold evolve in *; simpl in *; intuition.
  Qed.
End Tqs.

Import Tqs.
Export Tqs.

Definition hints : TacPackage.
  prepare tqs'_del_fwd (tqs'_empty_bwd, tqs'_add_bwd).
Defined.

Definition starting (ts : bag) (w : M.world) (pc : W) (ss : nat) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ [| semp m |]
    /\ Al st : settings * state, Al vs, Al ts', Al w',
      [| ts %<= ts' |]
      /\ [| M.evolve w w' |]
      /\ ![ ^[locals ("rp" :: "sc" :: nil) vs ss st#Sp * tqs ts' w' * M.globalInv ts' w' * mallocHeap 0] ] st
      ---> #0 st)%PropX.

Lemma starting_elim : forall specs ts w pc ss P stn st,
  interp specs (![ starting ts w pc ss * P ] (stn, st))
  -> (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs ts' w', interp specs ([| ts %<= ts' |]
      /\ [| M.evolve w w' |]
      /\ ![ locals ("rp" :: "sc" :: nil) vs ss stn_st#Sp
      * tqs ts' w' * M.globalInv ts' w' * mallocHeap 0 ] stn_st
    ---> pre stn_st)%PropX).
  cptr.
  generalize (split_semp _ _ _ H0 H); intros; subst; auto.
  rewrite <- sepFormula_eq; descend; step auto_ext.
  eauto.
  eauto.
  step auto_ext.
Qed.


Definition allocS : spec := SPEC reserving 15
  Al ts, Al w,
  PRE[_] tqs ts w * mallocHeap 0
  POST[R] tqs (ts %+ R) w * mallocHeap 0.

Definition spawnS : spec := SPEC("q", "pc", "ss") reserving 25
  Al ts, Al w, Al w',
  PRE[V] [| V "q" %in ts |] * [| V "ss" >= $2 |] * [| M.evolve w w' |]
    * tqs ts w * starting ts w' (V "pc") (wordToNat (V "ss") - 2) * mallocHeap 0
  POST[_] tqs ts w' * mallocHeap 0.

Definition exitS : spec := SPEC("q") reserving 14
  Al ts, Al w, Al w',
  PREonly[V] [| V "q" %in ts |] * [| M.evolve w w' |]
    * tqs ts w * M.globalInv ts w' * mallocHeap 0.

Definition yieldS : spec := SPEC("q") reserving 21
  Al ts, Al w, Al w',
  PRE[V] [| V "q" %in ts |] * [| M.evolve w w' |]
    * tqs ts w * M.globalInv ts w' * mallocHeap 0
  POST[_] Ex ts', Ex w'', [| ts %<= ts' |] * [| M.evolve w' w'' |]
    * tqs ts' w'' * M.globalInv ts' w'' * mallocHeap 0.

Definition m := bimport [[ "threadq"!"init" @ [Q.initS], "threadq"!"spawn" @ [Q.spawnS],
                           "threadq"!"exit" @ [Q.exitS], "threadq"!"yield" @ [Q.yieldS] ]]
  bmodule "threadqs" {{
    bfunction "alloc"("r") [allocS]
      "r" <-- Call "threadq"!"init"()
      [Al ts, Al w,
        PRE[_, R] tq (ts, w) R * tqs ts w
        POST[R'] tqs (ts %+ R') w ];;
      Return "r"
    end with bfunction "spawn"("q", "pc", "ss") [spawnS]
      Call "threadq"!"spawn"("q", "pc", "ss")
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
    end with bfunctionNoRet "exit"("q") [exitS]
      Call "threadq"!"exit"("q")
      [PREonly[_] [| False |] ]
    end with bfunction "yield"("q") [yieldS]
      Call "threadq"!"yield"("q")
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
   end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Ltac t := abstract (sep hints; auto).

Local Hint Immediate M.evolve_refl.

Theorem ok : moduleOk m.
  vcgen.

  t.
  t.
  t.
  t.
  t.
  t.
  t.

  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H6.
  eapply use_HimpWeak in H6; [ | apply (tqs'_weaken (w' := (x1 %+ Regs x0 Rv, x2))); (red; intuition) ].
  toFront ltac:(fun P => match P with
                           | tq _ _ => idtac
                         end) H6.
  eapply use_HimpWeak in H6; [ | apply (tq_weaken (w' := (x1 %+ Regs x0 Rv, x2))); (red; simpl; intuition) ].
  descend.
  step hints.
  step hints.
  descend; step hints.
  rewrite H5; step hints.
  simpl; auto.

  t.
  t.
  t.
  t.

  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H7.
  eapply use_HimpWeak in H7; [ | apply (tqs'_weaken (w' := (x0, x2))); (red; intuition) ].
  change (tqs' (x0, x2) x0) with (tqs'_pick_this_one (sel x4 "q") (x0, x2) x0) in H7.
  toFront ltac:(fun P => match P with
                           | starting _ _ _ _ => idtac
                         end) H7; apply starting_elim in H7; post.
  evaluate hints.
  descend.
  toFront_conc ltac:(fun P => match P with
                                | Q.starting _ _ _ _ => idtac
                              end); apply Q.starting_intro; descend.
  2: step hints.
  step hints.
  step hints.
  descend.
  apply andL; apply injL; intro.
  apply andL; apply swap; apply injL; intro.
  unfold ginv, M'.globalInv.
  autorewrite with sepFormula.
  destruct w'; simpl in *.
  destruct H7; simpl in *.
  eapply Imply_trans; [ | eapply (H13 _ _ b w) ]; clear H13.
  repeat (apply andR; [ apply injR; assumption | ]).

  Lemma switchy : forall P Q R S T R',
    R ===> R'
    -> P * Q * (R * S) * T ===> P * Q * R' * S * T.
    sepLemma.
  Qed.

  make_Himp.
  eapply Himp_trans; [ eapply switchy; apply starB_substH_fwd | ].
  unfold substH; simpl.
  match goal with
    | [ |- (_ * _ * ?P * _ * _ ===> _)%Sep ] =>
      replace P with (tqs' (b, w) (b %- sel x4 "q")) by (rewrite tqs'_eq; reflexivity)
  end.
  rewrite tqs_eq.

  Local Hint Extern 1 (_ %in _) => eapply incl_mem; eassumption.
  Local Hint Extern 1 (himp _ _ _) => apply tqs'_del_bwd.

  hnf; intros; step hints.
  step hints.
  t.

  t.
  t.
  t.

  t.
  t.
  t.

  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H5.
  eapply use_HimpWeak in H5; [ | apply (tqs'_weaken (w' := (x0, x2))); (red; intuition) ].
  change (tqs' (x0, x2) x0) with (tqs'_pick_this_one (sel x4 "q") (x0, x2) x0) in H5.
  evaluate hints.
  descend.
  step hints.
  step hints.
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  match goal with
    | [ |- himp _ ?P ?Q ] => let H := fresh in assert (H : P ===> Q); [ | apply H ]
  end.

  Lemma swatchy : forall P Q R P',
    P ===> P'
    -> (P * Q) * R ===> P' * Q * R.
    sepLemma.
  Qed.

  eapply Himp_trans; [ | apply swatchy; apply starB_substH_bwd ].
  unfold substH; simpl.
  match goal with
    | [ |- (_ ===> ?P * _ * _)%Sep ] => 
      replace P with (tqs' (x0, x2) (x0 %- sel x4 "q")) by (rewrite tqs'_eq; reflexivity)
  end.
  sepLemma.

  t.

  t.
  t.
  t.
  t.

  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H7.
  eapply use_HimpWeak in H7; [ | apply (tqs'_weaken (w' := (x0, x2))); (red; intuition) ].
  change (tqs' (x0, x2) x0) with (tqs'_pick_this_one (sel x4 "q") (x0, x2) x0) in H7.
  evaluate hints.
  descend.
  step hints.
  step hints.
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  match goal with
    | [ |- himp _ ?P ?Q ] => let H := fresh in assert (H : P ===> Q); [ | apply H ]
  end.
  eapply Himp_trans; [ | apply swatchy; apply starB_substH_bwd ].
  unfold substH; simpl.
  match goal with
    | [ |- (_ ===> ?P * _ * _)%Sep ] => 
      replace P with (tqs' (x0, x2) (x0 %- sel x4 "q")) by (rewrite tqs'_eq; reflexivity)
  end.
  sepLemma.
  step hints.
  descend; step hints.
  descend; step hints.
  step hints.
  destruct x8; simpl in *.
  descend; step hints.
  descend; step hints.
  descend; step hints.
  auto.
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  make_Himp.

  Lemma swotchy : forall P Q R S T U S',
    S ===> S'
    -> P * (Q * (R * ((S * T) * U))) ===> P * Q * R * S' * T * U.
    sepLemma.
  Qed.

  eapply Himp_trans; [ apply swotchy; apply starB_substH_fwd | ].
  unfold substH; simpl.
  match goal with
    | [ |- (_ * _ * _ * ?P * _ * _ ===> _)%Sep ] => 
      replace P with (tqs' (b, w) (b %- sel x4 "q")) by (rewrite tqs'_eq; reflexivity)
  end.
  destruct H16; simpl in *.
  sepLemma.
  etransitivity; [ apply himp_star_comm | ].
  auto.

  t.
  t.
  t.
Qed.

End Make.
