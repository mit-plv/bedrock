Require Import AutoSep Malloc.


(* These bits belong in Programming. *)

Definition ICall_ imps modName (rv : rvalue) (afterCall : assert) : cmd imps modName.
  red; refine (fun pre => {|
    Postcondition := afterCall;
    VerifCond := forall stn st specs,
      interp specs (pre (stn, st))
      -> forall rp, specs rp = Some afterCall
        -> match evalRvalue stn {| Regs := rupd (Regs st) Rp rp; Mem := Mem st |} rv with
             | None => False
             | Some w => exists pre', specs w = Some pre'
               /\ interp specs (pre' (stn, {| Regs := rupd (Regs st) Rp rp; Mem := Mem st |}))
           end;
    Generate := fun Base Exit => {|
      Entry := 0;
      Blocks := (pre, (Assign Rp (RvLabel (modName, Local Exit)) :: nil, Uncond rv)) :: nil
    |}
  |}).

  Ltac preSimp := simpl in *; intuition eauto; repeat (apply Forall_nil || apply Forall_cons); simpl; unfold importsGlobal in *.

  Ltac destrOpt E := let Heq := fresh "Heq" in case_eq E; (intros ? Heq || intro Heq); rewrite Heq in *.

  Ltac lomega := (let H := fresh in intro H; discriminate
    || injection H; clear H; intro; try subst; simpl in *; congruence || nomega)
  || (repeat match goal with
                 | [ |- eq (A := ?A) _ _ ] =>
                   match A with
                     | N => fail 1
                     | _ => f_equal
                   end
               end; nomega).

  Ltac simp := repeat (match goal with
                         | [ x : codeGen _ _ _ _ _ |- _ ] => destruct x; simpl in *
                         | [ H : _ /\ _ |- _ ] => destruct H
                         | [ H : Logic.ex _ |- _ ] => destruct H
                         | [ H1 : notStuck _ _, H2 : _ |- _ ] => specialize (H1 _ _ _ H2)
                         | [ H : LabelMap.find _ _ = Some _ |- _ ] => apply LabelMap.find_2 in H
                         | [ H : forall k v, _ |- _ ] => destruct (split_add H); clear H
                         | [ H : forall n x y, _ |- _ ] => destruct (nth_app_hyp H); clear H
                         | [ H : _ |- _ ] => destruct (specialize_imps H); clear H
                         | [ H : forall x, _ -> _ |- _ ] => specialize (H _ (refl_equal _))
                         | [ H : forall x y z, _ -> _ , H' : _ |- _ ] => specialize (H _ _ _ H')
                         | [ H : forall x y, _ -> _ , H' : LabelMap.MapsTo _ _ _ |- _ ] => destruct (H _ _ H'); clear H; auto
                         | [ |- blockOk _ _ _ ] => red
                         | [ _ : match ?E with Some _ => _ | None => _ end = Some _ |- _ ] => destrOpt E; [ | discriminate ]
                         | [ _ : match ?E with Some _ => _ | None => _ end = None -> False |- _ ] => destrOpt E; [ | tauto ]
                         | [ _ : match ?E with Some _ => _ | None => False end |- _ ] => destrOpt E; [ | tauto ]
                         | [ |- context[if ?E then _ else _] ] => destrOpt E
                         | [ H : ?E = None -> False |- _ ] =>
                           match E with
                             | Some _ => clear H
                             | _ => case_eq E; intros; tauto || clear H
                           end
                         | [ H : _ |- _ ] => rewrite H
                         | [ H : ?P -> _ |- _ ] =>
                           match type of P with
                             | Prop => let H' := fresh in assert (H' : P) by (lomega || auto); specialize (H H'); clear H'
                           end
                         | [ x : N |- _ ] => unfold x in *; clear x
                         | [ H : nth_error ?ls (nat_of_N ?n) = _ |- _ ] =>
                           match goal with
                             | [ _ : n < N_of_nat (length ls) |- _ ] => fail 1
                             | _ => specialize (nth_error_bound' _ _ H)
                           end
                         | [ H : snd ?x = _ |- _ ] => destruct x; simpl in H; congruence
                         | [ H : forall rp, _ rp = Some _ -> _, H' : _ _ = Some _ |- _ ] => specialize (H _ H')
                       end; intros; unfold evalBlock, evalCond in *; simpl; autorewrite with N in *).

  Ltac struct := preSimp; simp; eauto 15.

  abstract struct.
  Transparent evalInstrs.
  abstract struct.
Defined.

Definition ICall' (retOpt : option lvalue') (f : rvalue') (args : list rvalue')
  (afterCall : list string -> nat -> assert) : chunk := fun ns res =>
  Structured (Assign Rp (f ns)
    :: setArgs 4 args ns
    ++ Binop Sp Sp Plus (natToW (4 + 4 * List.length ns))
    :: Assign Rv Rp :: nil)
  (fun im mn H => Seq_ H (ICall_ im mn Rv (afterCall ns res))
    (Straightline_ im mn
      (Binop Sp Sp Minus (natToW (4 + 4 * List.length ns))
        :: match retOpt with
             | None => nil
             | Some lv => Assign (lv ns) Rv :: nil
           end))).

Local Notation RET := (fun inv ns => inv true (fun w => w ^- $(4 + 4 * List.length ns)) ns).

Notation "rv <-- 'ICall' f ( x1 , .. , xN ) [ p ]" :=
  (ICall' (@Some lvalue' rv) f (@cons rvalue' x1 (.. (@cons rvalue' xN nil) ..)) (RET p))
  (no associativity, at level 95, f at level 0) : SP_scope.

Opaque evalInstrs.


(** * Now, back to this example. *)

Inductive fn := Fn (f : W -> W).
Definition app (f : fn) (x : W) := let (f) := f in f x.

Definition goodMemo (f : fn) (pc : W) : HProp := fun s m =>
  (ExX : settings * state, Cptr pc #0
    /\ ExX : settings * smem, #0 (s, m)
    /\ Al st : settings * state, AlX : settings * smem, AlX : settings * state,
    (Ex vs, Cptr st#Rp #0
      /\ ![ ^[locals ("rp" :: "x" :: nil) vs 0 st#Sp] * #1 * #2 ] st
      /\ Al st' : settings * state,
      ([| st'#Sp = st#Sp /\ st'#Rv = app f (sel vs "x") |]
        /\ Ex vs', ![ ^[locals ("rp" :: "x" :: nil) vs' 0 st#Sp] * #1 * #2 ] st')
      ---> #0 st')
    ---> #3 st)%PropX.

Module Type MEMO.
  Parameter memo : fn -> W -> HProp.

  Axiom memo_fwd : forall f p,
    memo f p ===> Ex pc, Ex lastIn, Ex lastOut, (p ==*> pc, lastIn, lastOut) * [| lastOut = app f lastIn |] * goodMemo f pc.

  Axiom memo_bwd : forall f p,
    (Ex pc, Ex lastIn, Ex lastOut, (p ==*> pc, lastIn, lastOut) * [| lastOut = app f lastIn|] * goodMemo f pc) ===> memo f p.
End MEMO.

Module Memo : MEMO.
  Definition memo (f : fn) (p : W) : HProp :=
    (Ex pc, Ex lastIn, Ex lastOut, (p ==*> pc, lastIn, lastOut) * [| lastOut = app f lastIn |] * goodMemo f pc)%Sep.

  Theorem memo_fwd : forall (f : fn) p,
    memo f p ===> Ex pc, Ex lastIn, Ex lastOut, (p ==*> pc, lastIn, lastOut) * [| lastOut = app f lastIn |] * goodMemo f pc.
    unfold memo; sepLemma.
  Qed.

  Theorem memo_bwd : forall f p,
    (Ex pc, Ex lastIn, Ex lastOut, (p ==*> pc, lastIn, lastOut) * [| lastOut = app f lastIn|] * goodMemo f pc) ===> memo f p.
    unfold memo; sepLemma.
  Qed.
End Memo.

Import Memo.
Export Memo.

Definition hints : TacPackage.
  prepare memo_fwd memo_bwd.
Defined.

Definition initS : spec := SPEC("f", "in", "out") reserving 7
  Ex f,
  PRE[V] goodMemo f (V "f") * [| V "out" = app f (V "in") |] * mallocHeap
  POST[R] memo f R * mallocHeap.

Definition callS : spec := SPEC("m", "x") reserving 4
  Ex f,
  PRE[V] memo f (V "m")
  POST[R] [| R = app f (V "x") |] * memo f (V "m").

Definition memoizeM := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "memoize" {{
  bfunction "init"("f", "in", "out", "r") [initS]
    "r" <-- Call "malloc"!"malloc"(1)
    [PRE[V, R] R =?> 3
     POST[R'] [| R' = R |] * R ==*> V "f", V "in", V "out" ];;
    "r" *<- "f";;
    "r" <- "r" + 4;;
    "r" *<- "in";;
    "r" <- "r" + 4;;
    "r" *<- "out";;
    Return "r" - 8
  end with bfunction "call"("m", "x", "tmp", "tmp2") [callS]
    "tmp" <-* "m" + 4;;
    If ("x" = "tmp") {
      (* We're in luck!  This call is cached. *)

      "tmp" <-* "m" + 8;;
      Return "tmp"
    } else {
      (* This is a different argument from last time.  Call the function again. *)

      "tmp" <-* "m";;
      "tmp" <-- ICall "tmp"("x")
      [Ex f,
        PRE[V, R] [| R = app f (V "x") |] * memo f (V "m")
        POST[R'] [| R' = R |] * memo f (V "m") ];;

      "tmp2" <- "m" + 4;;
      "tmp2" *<- "x";;
      "tmp2" <- "m" + 8;;
      "tmp2" *<- "tmp";;

      Return "tmp"
    }
  end
}}.

Lemma use_himp : forall pc state specs (P Q : hprop pc state nil), himp specs P Q
  -> forall s m, interp specs (P s m)
    -> interp specs (Q s m).
  intros; apply (Imply_sound (H _ _)); auto.
Qed.

Lemma Imply_refl : forall pc state specs (P : PropX pc state),
  interp specs (P ---> P).
  intros; apply Imply_I; apply Env; simpl; auto.
Qed.

Theorem allXR : forall pc state specs P A (p : propX pc state (A :: nil)),
  (forall x, interp specs (P ---> PropX.Subst p x))
  -> interp specs (P ---> (ForallX p)).
  intros.
  apply Imply_I.
  apply ForallX_I; intro.
  eapply Imply_E.
  eauto.
  eauto.
Qed.

Hint Extern 1 (@eq W _ _) =>
  match goal with
    | [ |- context[app] ] => fail 1
    | _ => words
  end.

Theorem memoizeMOk : moduleOk memoizeM.
  unfold memoizeM; unfold ICall', ICall_; vcgen.

  Focus 17.
  
  post.
  autorewrite with IL.

  change (locals ("rp" :: "m" :: "x" :: "tmp" :: "tmp2" :: nil) x3 2 (Regs x0 Sp))
    with (locals_call ("rp" :: "m" :: "x" :: "tmp" :: "tmp2" :: nil) x3 2 (Regs x0 Sp)
      ("rp" :: "x" :: nil) 0 20) in H1.
  assert (ok_call ("rp" :: "m" :: "x" :: "tmp" :: "tmp2" :: nil) ("rp" :: "x" :: nil) 2 0 20)
    by (split; [ simpl; omega
      | split; [ simpl; omega
        | split; [ repeat constructor; simpl; intuition congruence
          | reflexivity ] ] ]).

  evaluate hints.

  match goal with
    | [ H : interp ?specs (![SEP.ST.star ?P (SEP.ST.star (goodMemo ?f ?pc) ?Q)] ?s) |- _ ] =>
      assert (interp specs (![SEP.ST.star (goodMemo f pc) (SEP.ST.star Q P)] s))
  end.
  
  step hints.
  clear H9.
  subst.
  rewrite sepFormula_eq in H2.
  apply simplify_fwd in H2.
  do 3 destruct H2.
  simpl in H2.
  destruct H3.
  simpl in H3.
  do 2 destruct H3.
  do 2 destruct H7.
  descend.
  step hints.
  step hints.
  eapply Imply_sound; [ apply H9 | ].
  apply simplify_bwd; simpl.
  repeat esplit.
  autorewrite with IL.
  rewrite H0.
  reflexivity.

  autorewrite with sepFormula.
  simpl.
  autorewrite with sepFormula.
  autorewrite with IL.
  apply simplify_fwd.
  
  match goal with
    | [ |- interp ?specs (![?P * ?Q * ?R] ?s) ] =>
      assert (interp specs (![R * (P * Q)] s))
  end.
  Focus 2.
  eapply interp_interp_himp; eauto.
  cancel auto_ext.
  apply simplify_bwd.
  rewrite sepFormula_eq.
  do 3 esplit.
  eauto.
  split; apply simplify_fwd; simpl.
  assumption.

  eapply use_himp; [ | eauto ].
  clear H4.
  cancel auto_ext.
  intros.
  descend.
  apply andL.
  apply injL; destruct 1.
  apply existsL; intro.
  autorewrite with sepFormula.
  simpl.
  autorewrite with sepFormula.
  unfold substH.
  simpl.
  eapply existsR.
  eapply existsXR; unfold PropX.Subst; simpl.
  eapply existsR.
  autorewrite with sepFormula; simpl.
  unfold substH; simpl.
  apply andR.

  match goal with
    | [ |- context[locals ("rp" :: "m" :: "x" :: "tmp" :: "tmp2" :: nil) ?vs 2 ?sp] ] =>
      rewrite (create_locals_return ("rp" :: "x" :: nil) 0 ("rp" :: "m" :: "x" :: "tmp" :: "tmp2" :: nil) 2 20)
  end.
  assert (ok_return ("rp" :: "m" :: "x" :: "tmp" :: "tmp2" :: nil) ("rp" :: "x" :: nil) 2 0 20)%nat by (split; [
    simpl; omega
    | reflexivity ] ).
  autorewrite with sepFormula.
  simpl.
  match goal with
    | [ |- context[fun stn0 sm => ?f ?a ?b ?c stn0 sm] ] =>
      rewrite (@use_HProp_extensional (f a b c)) by auto
  end.
  cancel hints.
  eauto.
  cancel hints.
  etransitivity; [ | apply himp_star_comm ].
  apply himp_star_frame_comm.
  reflexivity.
  do 2 intro.
  eapply existsXR; unfold PropX.Subst; simpl.
  apply andR.
  apply cptrR; eauto.
  eapply existsXR; unfold PropX.Subst; simpl.
  apply andR.



  apply Imply_refl.

  apply allR; intro.


  apply allXR; unfold PropX.Subst; simpl; intro.
  apply allXR; unfold PropX.Subst; simpl; intro.
  apply swap; apply implyR.
  eapply Imply_trans; [ | apply H9 ].
  apply Imply_refl.

  
  descend.
  eapply existsXR; unfold PropX.Subst; simpl.
  apply andR.
  apply cptrR; eauto.
  apply allR; intro.
  apply swap; apply implyR.
  eapply Imply_trans; [ | apply H6 ].
  apply andL; apply injL; intro.
  apply existsL; intro.
  autorewrite with sepFormula; simpl.
  apply andR.
  apply injR.
  unfold ST.settings in *.
  words.
  eapply existsR.
  autorewrite with sepFormula; simpl.
  unfold substH; simpl.
  cancel auto_ext.
  rewrite H14.
  destruct x10; simpl in *.
  assumption.

  Ltac t := sep hints; auto.

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
