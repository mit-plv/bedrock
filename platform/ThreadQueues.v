Require Import AutoSep Bags Malloc ThreadQueue Misc.
Import W_Bag.

Set Implicit Arguments.


Module Type S.
  Variable world : Type.

  Variable evolve : world -> world -> Prop.
  Axiom evolve_refl : forall w, evolve w w.
  Axiom evolve_trans : forall w1 w2 w3, evolve w1 w2 -> evolve w2 w3 -> evolve w1 w3.

  Variable globalInv : bag -> world -> HProp.
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
      /\ [| st#Sp <> 0 /\ freeable st#Sp (1 + ss) |]
      /\ ![ ^[locals ("rp" :: nil) vs ss st#Sp * tqs ts' w' * M.globalInv ts' w' * mallocHeap 0] ] st
      ---> #0 st)%PropX.

Lemma starting_elim : forall specs ts w pc ss P stn st,
  interp specs (![ starting ts w pc ss * P ] (stn, st))
  -> (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs ts' w', interp specs ([| ts %<= ts' |]
      /\ [| M.evolve w w' |]
      /\ [| stn_st#Sp <> 0 /\ freeable stn_st#Sp (1 + ss) |]
      /\ ![ locals ("rp" :: nil) vs ss stn_st#Sp
      * tqs ts' w' * M.globalInv ts' w' * mallocHeap 0 ] stn_st
    ---> pre stn_st)%PropX).
  cptr.
  generalize (split_semp _ _ _ H0 H); intros; subst; auto.
  rewrite <- sepFormula_eq; descend; step auto_ext.
  eauto.
  eauto.
  eauto.
  step auto_ext.
Qed.


Definition allocS : spec := SPEC reserving 14
  Al ts, Al w,
  PRE[_] tqs ts w * mallocHeap 0
  POST[R] tqs (ts %+ R) w * mallocHeap 0.

Definition isEmptyS : spec := SPEC("sc") reserving 4
  Al ts, Al w,
  PRE[V] [| V "sc" %in ts |] * tqs ts w * mallocHeap 0
  POST[_] tqs ts w * mallocHeap 0.

Definition spawnS : spec := SPEC("sc", "pc", "ss") reserving 18
  Al ts, Al w, Al w',
  PRE[V] [| V "sc" %in ts |] * [| V "ss" >= $2 |] * [| M.evolve w w' |]
    * tqs ts w * starting ts w' (V "pc") (wordToNat (V "ss") - 1) * mallocHeap 0
  POST[_] tqs ts w' * mallocHeap 0.

Definition exitS : spec := SPEC("sc", "ss") reserving 0
  Al ts, Al w, Al w',
  PREexit[V] [| V "ss" >= $3 |] * [| V "sc" %in ts |] * [| M.evolve w w' |]
    * tqs ts w * M.globalInv ts w' * mallocHeap 0.

Definition yieldS : spec := SPEC("sc") reserving 19
  Al ts, Al w, Al w',
  PRE[V] [| V "sc" %in ts |] * [| M.evolve w w' |]
    * tqs ts w * M.globalInv ts w' * mallocHeap 0
  POST[_] Ex ts', Ex w'', [| ts %<= ts' |] * [| M.evolve w' w'' |]
    * tqs ts' w'' * M.globalInv ts' w'' * mallocHeap 0.

Notation "'balias' name () [ p ] l 'end'" :=
  (let p' := p in
   let vars := nil in
    {| FName := name;
      FPrecondition := Precondition p' None;
      FBody := Goto l%SP;
      FVars := vars;
      FReserved := Reserved p' |})
  (no associativity, at level 95, name at level 0, p at level 0, only parsing) : SPfuncs_scope.

Definition m := bimport [[ "threadq"!"init" @ [Q.initS], "threadq"!"isEmpty" @ [Q.isEmptyS],
                           "threadq"!"spawn" @ [Q.spawnS],
                           "threadq"!"exit" @ [Q.exitS], "threadq"!"yield" @ [Q.yieldS] ]]
  bmodule "threadqs" {{
    bfunction "alloc"("r") [allocS]
      "r" <-- Call "threadq"!"init"()
      [Al ts, Al w,
        PRE[_, R] tq (ts, w) R * tqs ts w
        POST[R'] tqs (ts %+ R') w ];;
      Return "r"
    end with balias "isEmpty"() [isEmptyS]
      "threadq"!"isEmpty"
    end with balias "spawn"() [spawnS]
      "threadq"!"spawn"
    end with balias "exit"() [exitS]
      "threadq"!"exit"
    end with balias "yield"() [yieldS]
      "threadq"!"yield"
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

  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H4.
  change (tqs' (x, x0) x) with (tqs'_pick_this_one (sel x2 "sc") (x, x0) x) in H4.
  Local Hint Extern 1 (_ %in _) => eapply incl_mem; eassumption.
  Local Hint Extern 1 (himp _ _ _) => apply tqs'_del_bwd.
  t.

  t.

  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H4.
  eapply use_HimpWeak in H4; [ | apply (tqs'_weaken (w' := (x, x1))); (red; intuition) ].
  change (tqs' (x, x1) x) with (tqs'_pick_this_one (sel x3 "sc") (x, x1) x) in H4.
  toFront ltac:(fun P => match P with
                           | starting _ _ _ _ => idtac
                         end) H4; apply starting_elim in H4; post.
  evaluate hints.
  descend.
  toFront_conc ltac:(fun P => match P with
                                | Q.starting _ _ _ _ => idtac
                              end); apply Q.starting_intro; descend.
  2: step hints.
  step hints.
  step hints.
  step hints.
  destruct w'; simpl in *.
  destruct H; simpl in *.
  eapply Imply_trans; [ | eapply (H4 _ _ b0 w) ]; clear H4.
  repeat (apply andR; [ apply injR; assumption | ]).
  repeat (apply andR; [ apply injR; auto | ]).

  Lemma switchy : forall P Q R S T R',
    R ===> R'
    -> P * Q * (R * S) * T ===> P * Q * R' * S * T.
    sepLemma.
  Qed.

  make_Himp.
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  eapply Himp_trans; [ eapply switchy; apply starB_substH_fwd | ].
  unfold substH; simpl.
  match goal with
    | [ |- (_ * _ * ?P * _ * _ ===> _)%Sep ] =>
      replace P with (tqs' (b0, w) (b0 %- sel x3 "sc")) by (rewrite tqs'_eq; reflexivity)
  end.
  rewrite tqs_eq.

  hnf; intros; step hints.
  step hints.
  t.

  t.

  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H4.
  eapply use_HimpWeak in H4; [ | apply (tqs'_weaken (w' := (x, x1))); (red; intuition) ].
  change (tqs' (x, x1) x) with (tqs'_pick_this_one (sel x2 "sc") (x, x1) x) in H4.
  evaluate hints.
  descend.
  eauto.
  step hints.
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  make_Himp.

  eapply Himp_trans; [ | apply Himp_star_comm ].
  apply Himp_star_frame; try apply Himp_refl.
  eapply Himp_trans; [ | apply starB_substH_bwd ].
  unfold substH; simpl.
  match goal with
    | [ |- (?P ===> ?Q)%Sep ] => 
      replace P with Q; try apply Himp_refl
  end.
  rewrite tqs'_eq; reflexivity.

  t.

  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H4.
  eapply use_HimpWeak in H4; [ | apply (tqs'_weaken (w' := (x, x1))); (red; intuition) ].
  change (tqs' (x, x1) x) with (tqs'_pick_this_one (sel x3 "sc") (x, x1) x) in H4.
  evaluate hints.
  descend.
  step hints.
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  make_Himp.

  Lemma swatchy : forall P Q Q' R,
    Q' ===> Q
    -> P * (Q' * R) ===> P * (Q * R).
    sepLemma.
  Qed.

  eapply Himp_trans; [ | apply swatchy; apply starB_substH_bwd ].
  unfold substH; simpl.
  match goal with
    | [ |- (_ ===> _ * (?P * _))%Sep ] => 
      replace P with (tqs' (x, x1) (x %- sel x3 "sc")) by (rewrite tqs'_eq; reflexivity)
  end.
  sepLemma.
  step hints.
  descend; step hints.
  descend; step hints.
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  instantiate (1 := snd x6).
  instantiate (1 := fst x6).
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  make_Himp.

  Lemma swotchy : forall P Q R S T R' U,
    R ===> R'
    -> P * star (star Q (R * U)) S * T ===> P * Q * R' * U * S * T.
    sepLemma.
  Qed.

  eapply Himp_trans; [ apply swotchy; apply starB_substH_fwd | ].
  unfold substH; simpl.
  match goal with
    | [ |- (_ * _ * ?P * _ * _ * _ ===> _)%Sep ] => 
      replace P with (tqs' (fst x6, snd x6) (fst x6 %- sel x3 "sc"))
  end.
  sepLemma.
  destruct x6; destruct H0; simpl in *; auto.
  destruct x6; destruct H0; simpl in *; auto.
  destruct x6; destruct H0; simpl in *; auto.
  rewrite tqs'_eq.
  destruct x6; reflexivity.
Qed.

End Make.
