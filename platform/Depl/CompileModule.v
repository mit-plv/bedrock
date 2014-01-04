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
    | x :: xs => fo_set (formals V xs fE) x (Dyn (sel V x))
  end.

(** Generic top-level function spec (see [Compile.precond] for comments) *)
Definition precond (frmls lcls : list pr_var) (pre post : pred) (inBody : bool) : assert :=
  (PRE[V] mallocHeap 0 * predD pre (formals V frmls fo_empty)
   POST[R] mallocHeap 0 * predD post (fo_set (formals V frmls fo_empty) "result" (Dyn R)))
  false (fun w => w) (if inBody then frmls ++ lcls else lcls) 0.

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
      FVars := xs;
      FReserved := 0;
      FPrecondition := precond (Formals f) (Locals f) (Precondition f) (Postcondition f) false;
      FBody := ($[Sp+0] <- Rp;;
        (fun _ _ =>
          Structured nil (fun im mn _ => Structured.Assert_ im mn
            (precond (Formals f) (Locals f) (Precondition f) (Postcondition f) true)));;
        (Stmt (map (fun s => s ++ "0")%string xs ++ SpecVars f)
          bvs bvs' xs (vars0 xs)
          (Precondition f) (Postcondition f) (Body f)))%SP
    |}
    | _, _ => function0 (Name f)
  end.

(** A computable syntactic well-formedness check... *)
Definition functionWf (f : function) : bool :=
  let xs := Formals f ++ Locals f in
  let fvs := map (fun s => s ++ "0")%string xs ++ SpecVars f in
  if in_dec string_dec "rp" xs
    then false
  else if in_dec string_dec "result" fvs
    then false
  else match boundVars (Precondition f), boundVars (Postcondition f) with
         | Some bvs, Some bvs' =>
           if in_dec string_dec "result" bvs
             then false
             else notsInList bvs fvs && notsInList bvs' ("result" :: fvs)
         | _, _ => false
       end.

(** ...and a residual part, for what we ask the user to prove *)
Definition functionVc (f : function) : list Prop :=
  let xs := Formals f ++ Locals f in
  let fvs := map (fun s => s ++ "0")%string xs ++ SpecVars f in
    stmtV xs (Body f)
    :: stmtD (normalize (Precondition f)) (normalize (Postcondition f)) fvs (vars0 xs) (Body f) (fun _ => False)
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
           | [ H : context[if ?E then _ else _] |- _ ] => destruct E; try discriminate
           | [ H : context[match ?E with None => _ | _ => _ end] |- _ ] => case_eq E; intros;
             match goal with
               | [ H' : _ = _ |- _ ] => rewrite H' in *
             end; try discriminate
         end.
  apply andb_prop in H1; intuition idtac.
  repeat match goal with
           | [ H : vcs (_ :: _) |- _ ] => inversion_clear H
         end.
  repeat constructor; simpl; auto.

  propxFo.

  (* Some function prelude execution *)
  admit.
  admit.
  admit.

  hnf; auto.

  unfold vars0; intros.
  destruct (in_dec string_dec x (Formals a ++ Locals a)); auto; congruence.

  unfold vars0; intros.
  destruct (in_dec string_dec x (Formals a ++ Locals a)); try discriminate.
  inversion_clear H11.
  simpl.
  apply H13.
  apply in_or_app; left.
  apply in_map_iff; eauto.

  eauto using notsInList_true.
  eauto using notsInList_true.
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
