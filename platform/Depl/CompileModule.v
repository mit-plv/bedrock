(** Compiling the deeply embedded programming language *)

Require Import Bool.

Require Import AutoSep Wrap Malloc.

Require Import Depl.Logic Depl.Statements Depl.Compile.


(** * Functions *)

(** Type of one function in a Depl module *)
Record function := {
  Name : string;
  (** This name is copied over verbatim into the Bedrock module. *)

  SpecVars : list fo_var;
  (** Spec variables scoped over both precondition and postcondition *)

  Formals : list pr_var;
  (** Formal function argument names *)

  Locals : list pr_var;
  (** Other available variables *)

  Precondition : pred;
  Postcondition : pred;
  Body : stmt
  (** Yeah, you know what these are. *)
}.

(** Helper to copy formal parameter values from a [vals] to a [fo_env] *)
Fixpoint formals (V : vals) (xs : list pr_var) (fE : fo_env) : fo_env :=
  match xs with
    | nil => fE
    | x :: xs => fo_set (formals V xs fE) (x ++ "0")%string (Dyn (sel V x))
  end.

(** Generic top-level function spec (see [Compile.precond] for comments) *)
Definition precond (frmls lcls : list pr_var) (pre post : pred) (inBody : bool) : assert :=
  (Al fE,
    PRE[V] mallocHeap 0 * predD pre (formals V frmls fE)
    POST[R] mallocHeap 0 * predD post (fo_set (formals V frmls fE) "result" (Dyn R)))
  inBody (fun w => w) (if inBody then frmls ++ lcls else frmls) (if inBody then 0 else length lcls).

(** A default function, for when things go horribly wrong *)
Definition function0 name : Programming.function := {|
  FName := name;
  FVars := nil;
  FReserved := 0;
  FPrecondition := (st ~> [| False |]);
  FBody := Skip
|}.

(** Initial symbolic variable assignment *)
Definition vars0 (xs : list pr_var) : vars := 
  fun x => if in_dec string_dec x xs then Some (Logic.Var (x ++ "0")%string) else None.

(** Generating one Bedrock function *)
Definition compileFunction (f : function) : Programming.function :=
  let xs := Formals f ++ Locals f in
  match boundVars (Precondition f), boundVars (Postcondition f) with
    | Some bvs, Some bvs' => {|
      FName := Name f;
      FVars := Formals f;
      FReserved := length (Locals f);
      FPrecondition := precond (Formals f) (Locals f) (Precondition f) (Postcondition f) false;
      FBody := ($[Sp+0] <- Rp;;
        (fun _ _ =>
          Structured nil (fun im mn _ => Structured.Assert_ im mn
            (precond (Formals f) (Locals f) (Precondition f) (Postcondition f) true)));;
        (fun _ _ => Stmt (map (fun s => s ++ "0")%string xs ++ SpecVars f)
          bvs bvs' xs (vars0 (Formals f))
          (Precondition f) (Postcondition f) (Body f) xs 0))%SP
    |}
    | _, _ => function0 (Name f)
  end.

(** Deciding whether a list is duplicate-free *)
Section NoDup_dec.
  Variable A : Type.
  Variable dec : forall x y : A, {x = y} + {x <> y}.

  Hint Constructors NoDup.

  Definition NoDup_dec : forall ls : list A, {NoDup ls} + {~NoDup ls}.
  Proof.
    refine (fix NoDup_dec (ls : list A) : {NoDup ls} + {~NoDup ls} :=
      match ls return {NoDup ls} + {~NoDup ls} with
        | nil => left _
        | x :: ls' => if in_dec dec x ls' then right _ else
          if NoDup_dec ls' then left _ else right _
      end); clear NoDup_dec; abstract (eauto; inversion_clear 1; tauto).
  Defined.
End NoDup_dec.

(** Does a list of variables include any ending in "0"?
  * We're using that convention for our automatically generated variables,
  * so it's a no-no for the programmer to use it. *)

Fixpoint anyZero (x : fo_var) : bool :=
  match x with
    | "" => false
    | "0" => true
    | String _ x' => anyZero x'
  end.

Fixpoint anyZeros (xs : list fo_var) : bool :=
  match xs with
    | nil => false
    | x :: xs' => anyZero x || anyZeros xs'
  end.

(** A computable syntactic well-formedness check... *)
Definition functionWf (f : function) : bool :=
  let xs := Formals f ++ Locals f in
  let fvs := map (fun s => s ++ "0")%string xs ++ SpecVars f in
  if in_dec string_dec "rp" xs
    then false
  else if in_dec string_dec "result" fvs
    then false
  else if (if NoDup_dec _ string_dec xs then false else true)
    then false
  else if anyZeros (SpecVars f)
    then false
  else match boundVars (Precondition f), boundVars (Postcondition f) with
         | Some bvs, Some bvs' =>
           if in_dec string_dec "result" bvs
             then false
           else if in_dec string_dec "result" bvs'
             then false
           else notsInList bvs fvs && notsInList bvs' ("result" :: fvs)
         | _, _ => false
       end.

(** ...and a residual part, for what we ask the user to prove *)
Definition functionVc (f : function) : list Prop :=
  let xs := Formals f ++ Locals f in
  let fvs := map (fun s => s ++ "0")%string xs ++ SpecVars f in
    stmtV xs (Body f)
    :: stmtD (normalize (Precondition f))
    (normalize (Postcondition f)) fvs xs (vars0 (Formals f)) (Body f) (fun _ => False)
    :: wellScoped fvs (Precondition f)
    :: wellScoped ("result" :: fvs) (Postcondition f)
    :: predExt (Precondition f)
    :: predExt (Postcondition f)
    :: nil.

(** Combined syntactic check for all functions *)
Fixpoint functionsWf (fs : list function) : bool :=
  match fs with
    | nil => true
    | f :: fs' => functionWf f && functionsWf fs'
  end.

(** Combine the VCs of all functions. *)
Fixpoint makeVcs (fs : list function) : list Prop :=
  match fs with
    | nil => nil
    | f :: fs' => functionVc f ++ makeVcs fs'
  end.

Ltac clear_fancier := clear_fancy;
  repeat match goal with
           | [ H : context[map] |- _ ] => clear H
         end.

Lemma sel_eta : forall V, sel V = V.
Proof.
  auto.
Qed.

Theorem normalize_sound_fwd : forall p fvs bvs fE,
  wellScoped fvs p
  -> boundVars p = Some bvs
  -> (forall x, In x fvs -> ~In x bvs)
  -> predD p fE ===> normalD (normalize p) fE.
Proof.
  intros.
  change (predD p fE) with (SubstsH (SNil _ _) (predD p fE)).
  change (normalD (normalize p) fE) with (SubstsH (SNil _ _) (normalD (normalize p) fE)).
  eapply normalize_sound_fwd; eauto.
Qed.

Theorem normalize_sound_bwd : forall p fvs bvs fE,
  wellScoped fvs p
  -> boundVars p = Some bvs
  -> (forall x, In x fvs -> ~In x bvs)
  -> normalD (normalize p) fE ===> predD p fE.
Proof.
  intros.
  change (predD p fE) with (SubstsH (SNil _ _) (predD p fE)).
  change (normalD (normalize p) fE) with (SubstsH (SNil _ _) (normalD (normalize p) fE)).
  eapply normalize_sound_bwd; eauto.
Qed.

Lemma weaken_predD : forall p xs fE fE',
  wellScoped xs p
  -> (forall x, In x xs -> fE x = fE' x)
  -> predD p fE ===> predD p fE'.
Proof.
  intros.
  change (predD p fE) with (SubstsH (SNil _ _) (predD p fE)).
  change (predD p fE') with (SubstsH (SNil _ _) (predD p fE')).
  eapply weaken_predD; eauto.
Qed.

(** Relate the above definitions to what [StructuredModule] wants. *)
Theorem makeVcs_correct : forall mn fs0 fs, functionsWf fs = true
  -> vcs (makeVcs fs)
  -> vcs (StructuredModule.makeVcs nil fs0
    (map (fun p => match p with
                     | {| FName := f; FVars := ns; FReserved := res;
                       FPrecondition := pre; FBody := ch |} =>
                     (f, pre, fun im' H => toCmd ch mn H ns res)
                   end)
    (map compileFunction fs))).
Proof.
  induction fs; simpl; intuition.
  apply andb_prop in H; intuition.
  unfold functionWf in H1.
  unfold compileFunction at 1.

  repeat match goal with
           | [ H : context[if anyZeros ?X then _ else _] |- _ ] =>
             case_eq (anyZeros X); intros;
               match goal with
                 | [ H' : _ = _ |- _ ] => rewrite H' in *
               end; try discriminate
           | [ H : context[if (if ?E then _ else _) then _ else _] |- _ ] => destruct E; try discriminate
           | [ H : context[if ?E then _ else _] |- _ ] => destruct E; try discriminate
           | [ H : context[match ?E with None => _ | _ => _ end] |- _ ] => case_eq E; intros;
             match goal with
               | [ H' : _ = _ |- _ ] => rewrite H' in *
             end; try discriminate
         end.
  apply andb_prop in H1; intuition idtac.
  simpl.
  wrap0.

  post; clear_fancier.
  assert (In "rp" ("rp" :: Formals a)) by (simpl; tauto).
  assert (~In "rp" (Formals a)) by (intro; apply n0; eauto using in_or_app).
  change (sel x1) with x1 in *.
  unfold lvalIn, regInL in *; simpl in H1.
  change (LvMem (Indir Sp (natToW O))) with (LvMem (Indir Sp (variablePosition ("rp" :: Formals a) "rp"))) in *.
  evaluate auto_ext.

  post.
  assert (forall x4 x v, In x (map (fun s : string => (s ++ "0")%string) (Formals a ++ Locals a) ++ SpecVars a)
    -> formals x2 (Formals a) x0 x
    = formals (upd (merge x2 x4 ("rp" :: Formals a)) "rp" v)
    (Formals a) x0 x).
  intros.
  apply in_app_or in H; intuition idtac.
  apply in_map_iff in H18; destruct H18; intuition subst.

  Lemma append0_invert : forall x y,
    (x ++ "0" = y ++ "0")%string
    -> x = y.
  Proof.
    induction x; destruct y; simpl in *; intuition.
    destruct y; discriminate.
    destruct x; discriminate.
    injection H; clear H; intros; subst.
    f_equal; auto.
  Qed.

  Lemma formals_switch : forall V V' x xs fE,
    (In x xs -> sel V x = sel V' x)
    -> formals V xs fE (x ++ "0")%string = formals V' xs fE (x ++ "0")%string.
  Proof.
    induction xs; simpl; intuition.
    unfold fo_set.
    destruct (string_dec (x ++ "0")%string (a ++ "0")%string); subst; auto.
    apply append0_invert in e; subst.
    f_equal; auto.
  Qed.

  apply formals_switch.
  apply in_app_or in H19; intuition idtac.
  rewrite sel_upd_ne.
  symmetry; apply sel_merge.
  simpl; tauto.
  intro; subst.
  eauto using in_or_app.

  Lemma NoDup_unapp : forall A (ls2 ls1 : list A),
    NoDup (ls1 ++ ls2)
    -> forall x, In x ls1 -> In x ls2 -> False.
  Proof.
    induction ls1; inversion 1; simpl; intuition (subst; eauto using in_or_app).
  Qed.

  exfalso; eauto using NoDup_unapp.
  
  Lemma anyZero_duh : forall s, anyZero (s ++ "0")%string = true.
  Proof.
    induction s; simpl; intuition.
    destruct a.
    rewrite IHs.
    repeat match goal with
             | [ |- (if ?E then _ else _) = _ ] => destruct E; auto
           end.
  Qed.

  Lemma formals_irrel : forall V V' x xs fE,
    anyZero x = false
    -> formals V xs fE x = formals V' xs fE x.
  Proof.
    induction xs; simpl; intuition.
    unfold fo_set.
    destruct (string_dec x (a ++ "0")%string); subst; auto.
    rewrite anyZero_duh in H; discriminate.
  Qed.

  Lemma anyZeros_correct : forall x xs, anyZeros xs = false
    -> In x xs
    -> anyZero x = false.
  Proof.
    induction xs; simpl; intuition subst.

    apply orb_false_iff in H; intuition.
    apply orb_false_iff in H; intuition.
  Qed.

  eauto using formals_irrel, anyZeros_correct.

  generalize dependent (map (fun s : string => (s ++ "0")%string) (Formals a ++ Locals a) ++ SpecVars a); intros.
  clear_fancier.
  clear H8.
  change (locals ("rp" :: Formals a) x2 (length (Locals a)) (Regs x Sp))
    with (locals_in ("rp" :: Formals a) x2 (length (Locals a)) (Regs x Sp)
      (Locals a) ("rp" :: Formals a ++ Locals a) 0) in *.
  assert (ok_in ("rp" :: Formals a) (length (Locals a))
    (Locals a) ("rp" :: Formals a ++ Locals a) 0).
  repeat split; unfold pr_var; auto; try omega.
  simpl; constructor; auto.
  assert (In "rp" ("rp" :: Formals a ++ Locals a)) by (simpl; tauto).
  change (sel x2) with x2 in *.
  unfold lvalIn, regInL in *; simpl in H14.
  change (LvMem (Indir Sp (natToW O))) with (LvMem (Indir Sp (variablePosition ("rp" :: Formals a ++ Locals a) "rp"))) in *.
  evaluate auto_ext.
  fold (@app pr_var) in *.
  descend.
  rewrite sel_eta.
  step auto_ext.
  etransitivity; [ apply himp_star_comm | ]; apply himp_star_frame; try reflexivity.
  eapply weaken_predD; eauto.
  eauto.
  step auto_ext.
  descend; step auto_ext.
  instantiate (1 := x6).
  change (locals ("rp" :: Formals a) x6 (Datatypes.length (Locals a)) (Regs x Sp))
    with (locals_out ("rp" :: Formals a) x6 (Datatypes.length (Locals a)) (Regs x Sp)
      (Locals a) ("rp" :: Formals a ++ Locals a) 0).
  assert (ok_out ("rp" :: Formals a) (Datatypes.length (Locals a))
    (Locals a) ("rp" :: Formals a ++ Locals a) 0).
  repeat split; unfold pr_var; auto; try omega.
  rewrite sel_eta.
  descend; step auto_ext.
  eapply weaken_predD; eauto.
  simpl; intuition (subst; eauto).
  unfold fo_set.
  destruct (string_dec x6 "result"); subst; auto.
  symmetry; auto.  


  post.
  generalize dependent (map (fun s : string => (s ++ "0")%string) (Formals a ++ Locals a) ++ SpecVars a); intros.
  clear_fancier.
  clear H8.
  descend.
  repeat rewrite sel_eta in *.
  step auto_ext.
  fold (@app pr_var).
  Focus 2.
  apply himp_star_frame; try reflexivity.
  eapply normalize_sound_fwd; eauto using notsInList_true.

  Lemma formals_grab : forall V x xs fE,
    In x xs
    -> formals V xs fE (x ++ "0")%string = Dyn (sel V x).
  Proof.
    induction xs; simpl; intuition (subst; eauto).
    unfold fo_set.
    destruct (string_dec (x ++ "0")%string (x ++ "0")%string); subst; congruence.
    unfold fo_set.
    destruct (string_dec (x ++ "0")%string (a ++ "0")%string); subst; auto.
    apply append0_invert in e; subst.
    auto.
  Qed.

  Lemma vars_ok_formals : forall V xs fE,
    vars_ok (formals V xs fE) V (vars0 xs).
  Proof.
    unfold vars_ok, vars0; induction xs; simpl; intuition.

    destruct (string_dec a x); subst.
    injection H; clear H; intros; subst; simpl.
    unfold fo_set.
    destruct (string_dec (x ++ "0") (x ++ "0")); tauto.
    destruct (in_dec string_dec x xs); try discriminate.
    injection H; clear H; intros; subst; simpl.
    unfold fo_set.
    destruct (string_dec (x ++ "0") (a ++ "0")).
    apply append0_invert in e; congruence.
    auto using formals_grab.
  Qed.

  apply vars_ok_formals.
  step auto_ext.
  step auto_ext.
  descend; step auto_ext.
  descend; step auto_ext.
  rewrite sel_eta.
  step auto_ext.
  eapply normalize_sound_bwd; eauto using notsInList_true.


  hnf; auto.

  unfold vars0 in *.
  destruct (in_dec string_dec x (Formals a)); auto; try congruence.
  injection H; clear H; intros; subst; simpl.
  apply H1.
  apply in_or_app; left.
  apply in_map_iff; eauto using in_or_app.

  eauto using notsInList_true.

  subst; tauto.

  apply in_app_or in H14; intuition idtac.
  apply in_map_iff in H1; destruct H1; intuition subst.
  apply in_app_or in H16; intuition idtac.
  eapply notsInList_true in H7.
  tauto.
  apply H.
  right.
  apply in_or_app; left.
  apply in_map_iff.
  eauto using in_or_app.
  eapply notsInList_true in H7.
  tauto.
  apply H.
  right.
  apply in_or_app; left.
  apply in_map_iff.
  eauto using in_or_app.
  eapply notsInList_true in H7.
  tauto.
  apply H.
  right.
  apply in_or_app; auto.
Qed.


(** * Modules *)

(** A named group of functions *)
Record module := {
  MName : string;
  Functions : list function
}.

(** Generating a full module *)
Section compileModule.
  Variable m : module.

  Definition compileModule : XCAP.module :=
    bmodule_ nil (MName m) (map compileFunction (Functions m)).

  Lemma preserve_None : forall fs,
    fold_left
    (fun (mOpt : option (LabelMap.t unit)) (f : function) =>
      match mOpt with
        | Some mp =>
          if LabelMap.mem (elt:=unit) (Name f, Local 0) mp
            then None
            else Some (LabelMap.add (Name f, Local 0) tt mp)
        | None => None
      end) fs None = None.
  Proof.
    induction fs; simpl; intuition.
  Qed.

  Theorem NoDupFunc_out : forall fs (mp : LabelMap.t unit),
    match (List.fold_left (fun mOpt f =>
      match mOpt with
        | None => None
        | Some mp => let k := (Name f, Local 0) in
          if LabelMap.mem k mp then None
            else Some (LabelMap.add k tt mp)
      end) fs (Some mp)) with
      | None => False
      | Some _ => True
    end
    -> match (List.fold_left (fun mOpt (p : StructuredModule.function (MName m)) => let '(modl, _, _) := p in
      match mOpt with
        | None => None
        | Some m => let k := (modl, Local 0) in
          if LabelMap.mem k m then None
            else Some (LabelMap.add k tt m)
      end) (map (fun p => match p with
                            | {| FName := f; FVars := ns; FReserved := res;
                              FPrecondition := pre; FBody := ch |} =>
                            (f, pre, fun im' H => toCmd ch (MName m) H ns res)
                          end)
      (map compileFunction fs)) (Some mp)) with
         | None => False
         | Some _ => True
       end.
  Proof.
    induction fs as [ | [ ] ]; simpl; intuition.

    unfold compileFunction; simpl.
    destruct (boundVars Precondition0); simpl.
    destruct (boundVars Postcondition0); simpl.
    destruct (LabelMap.mem (Name0, Local 0) mp).
    rewrite preserve_None in *; tauto.
    apply IHfs; auto.
    destruct (LabelMap.mem (Name0, Local 0) mp).
    rewrite preserve_None in *; tauto.
    apply IHfs; auto.
    destruct (LabelMap.mem (Name0, Local 0) mp).
    rewrite preserve_None in *; tauto.
    apply IHfs; auto.
  Qed.

  Hypothesis NoDupFunc :
    match (List.fold_left (fun mOpt f =>
      match mOpt with
        | None => None
        | Some mp => let k := (Name f, Local 0) in
          if LabelMap.mem k mp then None
          else Some (LabelMap.add k tt mp)
      end) (Functions m) (Some (LabelMap.empty unit))) with
      | None => False
      | Some _ => True
    end.

  Hypothesis FuncsWf : functionsWf (Functions m) = true.
  Hypothesis FuncsVcs : vcs (makeVcs (Functions m)).
  
  (** Final correctness theorem *)
  Theorem compileModule_ok : moduleOk compileModule.
  Proof.
    intros; apply bmoduleOk; auto.

    apply NoDupFunc_out; auto.

    apply makeVcs_correct; auto.
  Qed.
End compileModule.
