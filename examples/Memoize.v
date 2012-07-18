Require Import AutoSep Malloc.


(* Two definitions based on hiding functions inside a new datatype, to avoid confusing our reification tactics *)
Inductive fn := Fn (f : W -> W).
Definition app (f : fn) (x : W) := let (f) := f in f x.

(* What does it mean for a program counter to implement a mathematical function? *)
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
  (* Arguments: mathematical function that is implemented, and pointer to private data *)

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

Hint Extern 1 (@eq W _ _) =>
  match goal with
    | [ |- context[app] ] => fail 1
    | _ => words
  end.

Theorem memoizeMOk : moduleOk memoizeM.
  vcgen.

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
  repeat match goal with
           | [ |- context C[Regs (match ?st with
                                    | (_, y) => y
                                  end) ?r] ] =>
             let E := context C[st#r] in change E
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
  apply forallXR; unfold PropX.Subst; simpl; intro.
  apply forallXR; unfold PropX.Subst; simpl; intro.
  apply swap; apply implyR.
  eapply Imply_trans; [ | apply H9 ].
  apply Imply_refl.
  
  descend.
  eapply existsXR; unfold PropX.Subst; simpl.
  apply andR.
  apply cptrR; eauto.
  apply allR; intro.
  apply swap; apply implyR.
  repeat match goal with
           | [ |- context C[Regs (match ?st with
                                    | (_, y) => y
                                  end) ?r] ] =>
             let E := context C[st#r] in change E
         end.
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
