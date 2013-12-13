(** Compiling the deeply embedded programming language *)

Require Import AutoSep Wrap Malloc.

Require Import Depl.Logic Depl.Cancel Depl.AlgebraicDatatypes Depl.Statements.


(** * Lowering DEPL expressions to Bedrock SPS expressions *)

Definition exprC (e : expr) : rvalue' :=
  match e with
    | Var x => x
    | Const w => w
  end.
(** The above looks like a bit of magic.  It's all in the coercions (from main Bedrock library). *)

Theorem exprC_correct : forall specs P stn st xs V vs fE e e' res,
  vars_ok fE V vs
  -> exprD vs e = Some e'
  -> exprV xs e
  -> ~In "rp" xs
  -> interp specs (![locals ("rp" :: xs) V res (Regs st Sp) * P] (stn, st))
  -> exists w,
    evalRvalue stn st (exprC e xs) = Some w
    /\ Logic.exprD e' fE = Dyn w.
Proof.
  destruct e; simpl; intuition.

  injection H0; clear H0; intros; subst; eauto.

  assert (Hnone : evalInstrs stn st (IL.Assign Rv (variableSlot x xs) :: nil) <> None).
  simp.
  generalize dependent H0.
  evaluate auto_ext.

  assert (Hsome : forall st', evalInstrs stn st (IL.Assign Rv (variableSlot x xs) :: nil) = Some st'
    -> Regs st' Rv = sel V x).
  simp.
  generalize dependent H0.
  evaluate auto_ext; auto.

  Transparent evalInstrs.
  simpl in *.
  Opaque evalInstrs.
  match goal with
    | [ |- exists x, ?X = _ /\ _ ] => destruct X; try tauto
  end.
  specialize (Hsome _ eq_refl); simpl in *.
  rewrite rupd_eq in Hsome; subst.
  eauto.
Qed.


(** * Lowering statements *)

Fixpoint stmtC (s : stmt) : chunk :=
  match s with
    | Assign x e => x <- exprC e
    | Seq s1 s2 => stmtC s1;; stmtC s2
    | Ret e => Return (exprC e)
  end%SP.

(** Version of [Logic.predD] specialized to predicates with no free higher-order variables *)
Definition predD (p : pred) (fE : fo_env) : HProp :=
  predD p (fun _ _ => Emp)%Sep fE.

(** Helper to copy formal parameter values from a [vals] to a [fo_env] *)
Fixpoint formals (V : vals) (xs : list pr_var) (fE : fo_env) : fo_env :=
  match xs with
    | nil => fE
    | x :: xs => fo_set (formals V xs fE) x (Dyn (sel V x))
  end.

(** Generic precondition of a statement, translated to base Bedrock from Depl-speak *)
Definition precond (vs : vars) (pre post : pred) :=
  (* First, quantify over a context assigning values to specification variables. *)
  Al fE,
    (* Naturally, we rely on the malloc() data structures being around. *)
    PRE[V] mallocHeap 0
      (* We also need the Depl precondition, of course. *)
      * predD pre fE
      (* Finally, the symbolic variable valuation should be accurate. *)
      * [| vars_ok fE V vs |]
    POST[R] mallocHeap 0
      (* The postcondition holds, in an [fo_env] that lets it mention the return value. *)
      * predD post (fo_set fE "result" (Dyn R)).

(** Generic postcondition of a statement *)
Definition postcond (vs : vars) (pre post : pred) (s : stmt) :=
  match stmtD vs s with
    | Error =>
      (* It's going to crash.  No guarantees! *)
      fun _ _ _ _ => st ~> [| True |]
    | Returned _ =>
      (* We returned already.  Unreachable! *)
      PREonly[_] [| False |]
    | Success vs' =>
      (* Still executing. *)
      precond vs' pre post
  end.

(** * Key lemmas to pass to Wrap *)

Lemma Stmt_post : forall xs vs pre post im mn (H : importsGlobal im) ns res pre0 specs,
  (forall specs0 st0,
    interp specs0 (pre0 st0)
    -> interp specs0 (precond vs pre post true (fun x => x) ns res st0))
  -> incl xs ns
  -> (forall x, In x xs -> vs x <> None)
  -> forall s st,
    stmtV xs s
    -> interp specs (Structured.Postcondition (toCmd (stmtC s) mn H ns res pre0) st)
    -> interp specs (postcond vs pre post s true (fun x => x) ns res st).
Proof.
  induction s; post; intuition; unfold postcond.

  match goal with
    | [ H : interp _ _, H' : forall specs0 : codeSpec _ _, _ |- _ ] =>
      apply H' in H; clear H'; post
  end.

  match goal with
    | [ |- context[match ?E with None => _ | _ => _ end] ] =>
      match E with
        | context[match _ with None => _ | _ => _ end] => fail 1
        | _ => case_eq E; post
      end
  end.
  specialize (H2 _ H4).
  match goal with
    | [ |- context[match ?E with None => _ | _ => _ end] ] =>
      match E with
        | context[match _ with None => _ | _ => _ end] => fail 1
        | _ => case_eq E; post
      end
  end.
  

  case_eq (exprD vs e); post.
  
  



(** Main statement compiler/combinator/macro *)
Definition Stmt
  (xs : list pr_var)
  (* Program variables available to mention *)
  (vs : vars)
  (* Symbolic valuation to those variables *)
  (pre post : pred)
  (* The Depl-level separation-logic specification for this statement *)
  (s : stmt)
  (* The statement to compile *)
  : chunk.
  apply (WrapC (stmtC s)
    (precond vs pre post)
    (postcond vs pre post s)

    (* VERIFICATION CONDITION *)
    (fun _ xs' _ =>
      incl xs xs'
      :: nil)).
