Require Import SyntaxExpr WritingPrograms Wf Compiler.
Export WritingPrograms CompileStatement Compiler.
Require Import Malloc MyMalloc MyFree Bootstrap.
Export Malloc.
Require Export AutoSep Semantics.
Require ConstFolding ElimDead.

Notation "'cfunction' name ( x1 , .. , xN ) b 'end'" :=
  {| Name := name;
    Vars := cons x1 (.. (cons xN nil) ..);
    Body := b%stmnt |}
  (no associativity, at level 95, name at level 0, only parsing).

Notation "{{ x 'with' .. 'with' y }}" := (cons x .. (cons y nil) ..) (only parsing) : Cfuncs_scope.
Delimit Scope Cfuncs_scope with Cfuncs.

Definition optimizer := GoodOptimizer.compose ConstFolding.constant_folding ElimDead.elim_dead_top.

Definition optimizer_is_good_optimizer := GoodOptimizer.is_good_optimizer_trans ConstFolding.constant_folding_is_good_optimizer ElimDead.elim_dead_top_is_good_optimizer.

Notation "'cmodule' name fs" := (Compiler.compile optimizer name fs%Cfuncs)
  (no associativity, at level 95, name at level 0, only parsing).

Ltac Forall := repeat (apply Forall_cons || apply Forall_nil).

Ltac compile :=
  apply (compileOk optimizer optimizer_is_good_optimizer); [ Forall | NoDup ]; constructor; auto;
    (NoDup || (Forall; hnf; tauto)
      || (eapply Wf.prove_NoUninitializedSafe; try eassumption; [ simpl; tauto ])
        || (eapply Wf.prove_NoUninitializedRunsTo; try eassumption; [ simpl; tauto ])
          || (hnf; simpl; tauto)).

Definition toSpec (a : assert) : spec := {|
  Reserved := 0;
  Formals := nil;
  Precondition := fun _ => a
|}.

Coercion toSpec : assert >-> spec.

Definition dempty : Semantics.WDict.dict := fun _ => nil.


(** * Link together a unified runtime for compiled programs. *)

Definition lib0 := link MyMalloc.m MyFree.m.
Definition lib := link Malloc.m lib0.

Theorem lib0Ok : moduleOk lib0.
  link MyMalloc.m_ok MyFree.ok.
Qed.

Theorem libOk : moduleOk lib.
  link Malloc.ok lib0Ok.
Qed.


(** * Helpful tactics for verifying Bedrock structured programs that call Cito code *)

Definition singletonArray (p : W) (ws : list W) : arrays :=
  (WMake.add WMake.empty p,
    WDict.upd dempty p ws).

Theorem singletonArray_bwd : forall (p : W) (ws : list W),
  Ex junk, [| p <> $8 |] * [| freeable (p ^- $8) (length ws + 2) |] * [| goodSize (length ws + 2) |]
  * (p ^- $8) =*> junk * (p ^- $4) =*> length ws * array ws p
  ===> heap (singletonArray p ws).
  intros; apply Himp_ex_c; exists (p :: nil); simpl.
  unfold array_ptr, MyMalloc.array_with_size.
  rewrite WDict.sel_upd_eq by auto.
  sepLemma.
  unfold WMake.equiv; tauto.
Qed.

Global Opaque singletonArray.

Hint Extern 1 (@eq W _ _) => words.

Hint Rewrite wplus_wminus : sepFormula.

Lemma sel_upd_eq' : forall vs x v y,
  x = y
  -> upd vs x v y = v.
  intros; change (upd vs x v y) with (sel (upd vs x v) y); descend.
Qed.

Lemma sel_upd_ne' : forall vs x v y,
  x <> y
  -> upd vs x v y = sel vs y.
  intros; change (upd vs x v y) with (sel (upd vs x v) y); descend.
Qed.

Hint Rewrite sel_upd_eq' sel_upd_ne' using solve [ auto ] : sepFormula.

Lemma fst_singletonArray : forall p ws,
  fst (singletonArray p ws) = WMake.add WMake.empty p.
  auto.
Qed.

Lemma snd_singletonArray : forall p ws,
  snd (singletonArray p ws) = WDict.upd dempty p ws.
  auto.
Qed.

Hint Rewrite fst_singletonArray snd_singletonArray : sepFormula.

Hint Rewrite WDict.sel_upd_eq WDict.sel_upd_ne using solve [ auto ] : sepFormula.

Lemma safe_access_singletonArray : forall p ws n,
  n < length ws
  -> goodSize (length ws)
  -> safe_access (singletonArray p ws) p n.
  intros; hnf; descend.
  auto.
  pre_nomega.
  rewrite wordToNat_natToWord_idempotent.
  rewrite wordToNat_natToWord_idempotent.
  auto.
  auto.
  change (goodSize n).
  eapply goodSize_weaken; eauto.
Qed.

Hint Extern 1 (safe_access _ _ _) => apply safe_access_singletonArray; [ simpl; omega | reflexivity ].

Ltac RunsTo0 := 
  match goal with
    | [ H : RunsTo _ _ ?E _ |- _ ] =>
      match E with
        | While (_) {{ _ }} => fail 1
        | _ => inversion H; clear H; repeat match goal with
                                              | [ x : _ |- _ ] => subst x
                                            end; simpl in *; autorewrite with sepFormula in *
      end
  end.

Ltac RunsTo := repeat RunsTo0.

Ltac Safe :=
  match goal with
    | [ |- Safety.Safe _ _ _ ] =>
      repeat match goal with
               | [ |- Safety.Safe _ _ _ ] => constructor; intros; RunsTo
             end; descend; auto
  end.

Ltac step hints :=
  try match goal with
        | [ |- interp _ (![_] _ ---> ![_] _)%PropX ] =>
          repeat match goal with
                   | [ H : RunsTo _ _ _ _ |- _ ] => clear H
                 end
      end; PreAutoSep.step hints.

Ltac sep hints fs :=
  match goal with
    | [ |- context[funcSpec] ] =>
      post;
      match goal with
        | [ H : context[locals ?ns ?vs ?res ?sp] |- exists fs : W -> option Callee, _ ] =>
          let offset := eval simpl in (4 * length ns) in
            change (locals ns vs res sp)
        with (locals_call ns vs res sp ("rp" :: "__reserved" :: "__arg" :: nil) (res - 3) offset)
          in H;
          assert (ok_call ns ("rp" :: "__reserved" :: "__arg" :: nil) res (res - 3) offset)
            by (split; [ simpl; omega
              | split; [ simpl; omega
                | split; [ NoDup
                  | reflexivity ] ] ]);
            exists fs
      end; evaluate hints; descend; repeat (step hints; descend); auto; try Safe
    | _ => AutoSep.sep hints
  end.


(** * Linking tactics *)

Ltac link' := simpl Imports; simpl Exports; unfold imports, modName; simpl; link_simp; tauto.

Ltac link ok1 ok2 :=
  apply linkOk; [ apply ok1
    | apply ok2
    | exact eq_refl
    | link'
    | link'
    | link' ].

Ltac safety ok :=
  eapply Safety.safety; try eassumption; [
    simpl Imports; simpl Exports; unfold imports, modName; simpl; link_simp;
      unfold Safety.labelSys, Safety.labelSys'; simpl; tauto
    | apply ok
    | apply LabelMap.find_2; link'
    | propxFo; apply materialize_allocated; assumption ].
