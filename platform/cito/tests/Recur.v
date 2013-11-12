Require Import Compile Recall.

Definition f := cfunction "f"("a", "b")
  "a" <== "__arg"[1];:
  If ("a" = 0) {
    "__arg"[0] <== 7
  } else {
    "b" <== "__arg"[3];;
    "__arg"[1] <== "a" - 1;;
    Call "b"["__arg"];;
    "a" <== "__arg"[0];;
    "__arg"[0] <== "a" + 1
  }
end.

Definition g := cfunction "g"("a", "b")
  "a" <== "__arg"[1];:
  If ("a" = 0) {
    "__arg"[0] <== 8
  } else {
    "b" <== "__arg"[2];;
    "__arg"[1] <== "a" - 1;;
    Call "b"["__arg"];;
    "a" <== "__arg"[0];;
    "__arg"[0] <== "a" + 2
  }
end.

Definition m := cmodule "Recur" {{
  f
  with g
}}.

Theorem ok : moduleOk m.
  compile.
Qed.

Definition mainS := SPEC reserving 49
  PREonly[V] mallocHeap 0.

Definition returnOk (arr : W) (arrs : arrays) :=
  fst arrs = WMake.add WMake.empty (arr ^+ $8)
  /\ let ls := snd arrs (arr ^+ $8) in
    length ls = 4 /\ Array.sel ls 0 = 10.

Definition heap_returnOk (_ : W) := heap.

Lemma WMake_add : forall ls s s',
  WMake.equiv s
  (fold_left WMake.add ls s')
  -> List.Forall (fun x => WMake.mem x s) ls /\ WMake.incl s' s.
  induction ls; simpl; intuition.
  apply IHls in H; intuition.
  apply IHls in H; intuition.
Qed.

Lemma singleton_equiv : forall arr x,
  WMake.equiv (WMake.add WMake.empty (arr ^+ $8)) (WMake.setify x)
  -> NoDup x
  -> x = (arr ^+ $8) :: nil.
  unfold WMake.setify; destruct x; simpl; intros.
  WMake.sets.
  specialize (H (arr ^+ $8)); tauto.
  inversion_clear H0.
  specialize (WMake_add _ _ _ H); intuition idtac.
  assert (a = arr ^+ $8) by WMake.sets.
  f_equal; auto.
  destruct x; simpl in *; auto.
  inversion_clear H3.
  assert (a0 = arr ^+ $8) by WMake.sets.
  subst; tauto.
Qed.

Lemma array4 : forall p a b c d,
  array (a :: b :: c :: d :: nil) p = (p =*> a * ((p ^+ $4) =*> b * ((p ^+ $8) =*> c * ((p ^+ $12) =*> d))))%Sep.
  auto.
Qed.

Hint Rewrite array4 : sepFormula.

Theorem returnOk_fwd : forall arr arrs,
  returnOk arr arrs
  -> heap_returnOk arr arrs
  ===> Ex a, Ex b, Ex c, Ex d, Ex e, (arr ==*> a, b, $10, c, d, e) * [| arr <> 0 |] * [| freeable arr 6 |].
  intros.
  destruct arrs.
  hnf in H; simpl in *; intuition subst.
  apply Himp'_ex; intro.
  eapply Himp_trans; [ apply Himp_star_assoc | ].
  do 2 (apply Himp_star_pure_c; intro).
  apply singleton_equiv in H0; auto; subst.
  simpl.
  unfold array_ptr, MyMalloc.array_with_size.
  rewrite H.
  destruct (d (arr ^+ $8)); try discriminate; simpl in *.
  do 4 (destruct d0; try discriminate; simpl in *).
  sepLemma; autorewrite with sepFormula in *; auto.
  sepLemma.
  rewrite <- H2.
  reflexivity.
Qed.

Definition hints : TacPackage.
  prepare returnOk_fwd singletonArray_bwd.
Defined.

Inductive please_unfold := PleaseUnfold.
Local Hint Constructors please_unfold.

Definition myFuncs (stn : settings) (pc : W) : option Callee :=
  match Labels stn ("test", Global "f"), Labels stn ("test", Global "g") with
    | Some fpc, Some gpc =>
      if weq pc fpc
        then Some (Internal (Body f))
        else if weq pc gpc
          then Some (Internal (Body g))
          else None
    | _, _ => None
  end.

Definition main := bimport [[ "Cito_Recur"!"f" @ [funcSpec f],
                              "Cito_Recur"!"g" @ [funcSpec g],
                              "sys"!"printInt" @ [printIntS], "sys"!"abort" @ [abortS],
                              "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "test" {{
    bstub "f" [funcFinalSpec myFuncs f]
      AssertStar (("test","f") :: ("test","g") :: nil)
      (fun _ _ => funcFinalSpec' myFuncs f);;

      Goto "Cito_Recur"!"f"
    end with bstub "g" [funcFinalSpec myFuncs g]
      AssertStar (("test","f") :: ("test","g") :: nil)
      (fun _ _ => funcFinalSpec' myFuncs g);;

      Goto "Cito_Recur"!"g"
    end
   with bfunction "main"("arr", "tmp", "f", "g") [mainS]
      "arr" <-- Call "malloc"!"malloc"(0, 6)
      [PREonly[V, R] R =?> 6 * [| R <> 0 |] * [| freeable R 6 |] * mallocHeap 0];;

      "f" <-- Recall "test"!"f";;
      "g" <-- Recall "test"!"g";;
      "arr" + 4 *<- 4;;
      "arr" + 8 *<- 0;;
      "arr" + 12 *<- 2;;
      "arr" + 16 *<- "f";;
      "arr" + 20 *<- "g";;

      "tmp" <- "arr" + 8;;
      Note [please_unfold];;
      Call "test"!"f"(42, "tmp")
      [Al arrs,
        PREonly[V] heap_returnOk (V "arr") arrs * mallocHeap 0 * [| returnOk (V "arr") arrs |] ];;

      Assert [Al a, Al b, Al c, Al d, Al e,
        PREonly[V] (V "arr" ==*> a, b, $10, c, d, e) * mallocHeap 0
          * [| V "arr" <> 0 |] * [| freeable (V "arr") 6 |] ];;

      "tmp" <-* "arr" + 8;;
      Call "malloc"!"free"(0, "arr", 6)
      [PREonly[_] Emp ];;

      Call "sys"!"printInt"("tmp")
      [PREonly[_] Emp ];;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ];;

      Fail
    end
  }}.

Ltac myFuncs :=
  unfold myFuncs; intros;
    repeat match goal with
             | [ _ : context[match ?E with Some _ => _ | None => _ end] |- _ ] =>
               destruct E
             | [ _ : context[if ?E then _ else _] |- _ ] =>
               destruct E
           end; intuition congruence.

Lemma myFuncs_foreign : forall stn pc precond P,
  myFuncs stn pc = Some (Foreign precond P)
  -> False.
  myFuncs.
Qed.

Lemma myFuncs_internal : forall stn pc s,
  myFuncs stn pc = Some (Internal s)
  -> (Labels stn ("test", Global "f") = Some pc
    /\ s = Body f)
  \/ (Labels stn ("test", Global "g") = Some pc
    /\ s = Body g).
  myFuncs.
Qed.

Ltac returnOk :=
  match goal with
    | [ |- returnOk _ _ ] => 
      RunsTo; hnf; descend; auto; reflexivity
  end.

Ltac t := try congruence;
  try match goal with
        | [ |- context[please_unfold] ] => unfold heap_returnOk
      end;
  sep hints (fun _ : W => @None Callee); auto; try returnOk.

Theorem mainOk : moduleOk main.
  vcgen.

  t.

  post; descend.
  
  apply injL; intro.
  apply myFuncs_foreign in H0; tauto.

  apply injL; intro.
  apply myFuncs_internal in H0; intuition subst.
  rewrite H1 in H0; injection H0; clear H0; intros; subst.
  post; descend; eauto 1.
  apply andR; [ eapply existsR; apply injR; eauto | ].
  rewrite sepFormula_eq; apply Imply_refl.
  rewrite H2 in H0; injection H0; clear H0; intros; subst.
  post; descend; eauto 1.
  apply andR; [ eapply existsR; apply injR; eauto | ].
  rewrite sepFormula_eq; apply Imply_refl.

  post; descend; eauto.

  t.

  post; descend.
  
  apply injL; intro.
  apply myFuncs_foreign in H0; tauto.

  apply injL; intro.
  apply myFuncs_internal in H0; intuition subst.
  rewrite H1 in H0; injection H0; clear H0; intros; subst.
  post; descend; eauto 1.
  apply andR; [ eapply existsR; apply injR; eauto | ].
  rewrite sepFormula_eq; apply Imply_refl.
  rewrite H2 in H0; injection H0; clear H0; intros; subst.
  post; descend; eauto 1.
  apply andR; [ eapply existsR; apply injR; eauto | ].
  rewrite sepFormula_eq; apply Imply_refl.

  post; descend; eauto.

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

  unfold heap_returnOk; post.
  eauto.
  match goal with
    | [ H : context[locals ?ns ?vs ?res ?sp] |- _ ] =>
      let offset := eval simpl in (4 * length ns) in
        change (locals ns vs res sp)
    with (locals_call ns vs res sp ("rp" :: "__reserved" :: "__arg" :: nil) (res - 3) offset)
      in H;
      assert (ok_call ns ("rp" :: "__reserved" :: "__arg" :: nil) res (res - 3) offset)
        by (split; [ simpl; omega
          | split; [ simpl; omega
            | split; [ NoDup
              | reflexivity ] ] ])
  end.
  evaluate hints.
  descend.
  instantiate (2 := singletonArray (Regs x7 Rv ^+ natToW 8) ($0 :: $2 :: x5 :: x2 :: nil)).
  step hints; auto.
  step hints.
  auto.

  Hint Rewrite sel_upd_ne' using congruence : sepFormula.
  constructor; intros; simpl; autorewrite with sepFormula.
  constructor; intros; simpl; autorewrite with sepFormula.
  auto.
  inversion H17; clear H17; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  apply Safety.ConditionFalse.
  reflexivity.
  constructor; intros; simpl; autorewrite with sepFormula.
  constructor; intros; simpl; autorewrite with sepFormula.
  auto.
  inversion H17; clear H17; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  constructor; intros; simpl; autorewrite with sepFormula.
  constructor; intros; simpl; autorewrite with sepFormula.
  auto.
  inversion H17; clear H17; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  constructor; intros; simpl; autorewrite with sepFormula.
  eapply Safety.CallInternal.
  descend.
  match goal with
    | [ |- myFuncs _ ?X = _ ] => change X with x2
  end.
  unfold myFuncs; simpl.
  repeat match goal with
           | [ H : _ = Some _ |- _ ] => rewrite H
         end.
  destruct (weq x2 x5).
  exfalso; subst.
  rewrite H12 in H8.
  injection H8; clear H8; intros.
  apply (f_equal (fun f => f (stn, st))) in H8.
  generalize H8; clear; intros.

  Definition projx1 pc state G (p : propX pc state G) : propX pc state G :=
    match p with
      | And _ p1 _ => p1
      | p' => p'
    end.

  apply (f_equal (projx1 _ _ _)) in H8; simpl in H8.

  Definition unexX pc state G (p : propX pc state G) : { T : Type & T -> propX pc state G } :=
    match p with
      | Exists _ _ p1 => existT _ _ p1
      | p' => existT (fun T => T -> propX pc state _) _ (fun _ : unit => Inj True)
    end.

  apply (f_equal (unexX _ _ _)) in H8; simpl in H8.
  Require Import Eqdep.
  apply inj_pair2 in H8.
  apply (f_equal (fun f => f "f")) in H8.

  Definition uninjX pc state G (p : propX pc state G) : Prop :=
    match p with
      | Inj _ P => P
      | _ => True
    end.

  apply (f_equal (uninjX _ _ _)) in H8; simpl in H8.
  assert ("f" = "f") by auto.
  rewrite H8 in H.
  discriminate.

  destruct (weq x2 x2); tauto.
  simpl; autorewrite with sepFormula.
  intros.
  constructor; intros; simpl; autorewrite with sepFormula.
  constructor; intros; simpl; autorewrite with sepFormula.
  change (vs_arg "__arg") with (sel vs_arg "__arg").
  hnf; simpl; autorewrite with sepFormula; split; simpl; auto.
  inversion H18; clear H18; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  apply Safety.ConditionFalse.
  reflexivity.
  constructor; intros; simpl; autorewrite with sepFormula.
  constructor; intros; simpl; autorewrite with sepFormula.
  hnf; simpl; autorewrite with sepFormula; split; simpl; auto.
  inversion H18; clear H18; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  constructor; intros; simpl; autorewrite with sepFormula.
  constructor; intros; simpl; autorewrite with sepFormula.
  auto.
  inversion H18; clear H18; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  constructor; intros; simpl; autorewrite with sepFormula.
  eapply Safety.CallInternal.
  descend.
  simpl.
  match goal with
    | [ |- myFuncs _ ?X = _ ] => change X with x5
  end.
  unfold myFuncs; simpl.
  repeat match goal with
           | [ H : _ = Some _ |- _ ] => rewrite H
         end.
  destruct (weq x5 x5); tauto.
  simpl; autorewrite with sepFormula.
  intros.
  constructor; intros; simpl; autorewrite with sepFormula.
  constructor; intros; simpl; autorewrite with sepFormula.
  change (vs_arg0 "__arg") with (sel vs_arg0 "__arg").
  hnf; simpl; autorewrite with sepFormula; split; simpl; auto.
  rewrite H18; auto.
  inversion H19; clear H19; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  constructor; simpl; autorewrite with sepFormula.
  reflexivity.
  constructor; simpl; autorewrite with sepFormula.
  hnf; simpl; autorewrite with sepFormula; split; simpl; auto.
  rewrite H18; auto.
  inversion H18; clear H18.
  subst v1; subst v0; subst.
  simpl in *; autorewrite with sepFormula in *.
  match goal with
    | [ H : myFuncs _ ?X = _ |- _ ] => change X with x5 in *
  end.
  unfold myFuncs in H29; simpl in H29.
  rewrite H1 in H29; rewrite H7 in H29.
  destruct (weq x5 x5); congruence.
  subst v1; subst v0; subst.
  simpl in *; autorewrite with sepFormula in *.
  match goal with
    | [ H : myFuncs _ ?X = _ |- _ ] => change X with x5 in *
  end.
  unfold myFuncs in H25; simpl in H25.
  rewrite H1 in H25; rewrite H7 in H25.
  destruct (weq x5 x5); try tauto.
  injection H25; clear H25; intros; subst.
  inversion H34; clear H34; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end.
  inversion H20; clear H20; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  inversion H25; clear H25; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *; try discriminate.
  inversion H34; clear H34; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl; autorewrite with sepFormula.
  constructor; intros; simpl; autorewrite with sepFormula.
  constructor; intros; simpl; autorewrite with sepFormula.
  hnf; simpl; autorewrite with sepFormula; split; simpl; auto.
  inversion H18; clear H18; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl; autorewrite with sepFormula.
  constructor; intros; simpl; autorewrite with sepFormula.
  hnf; simpl; autorewrite with sepFormula; split; simpl; auto.
  inversion H17; clear H17; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  match goal with
    | [ H : myFuncs _ ?X = _ |- _ ] => change X with x2 in *
  end.
  unfold myFuncs in H25; simpl in H25.
  rewrite H1 in H25; rewrite H7 in H25.
  destruct (weq x2 x5); try congruence.
  destruct (weq x2 x2); congruence.
  match goal with
    | [ H : myFuncs _ ?X = _ |- _ ] => change X with x2 in *
  end.
  unfold myFuncs in H24; simpl in H24.
  rewrite H1 in H24; rewrite H7 in H24.
  destruct (weq x2 x5).
  exfalso; subst.
  rewrite H12 in H8.
  injection H8; clear H8; intros.
  apply (f_equal (fun f => f (stn, st))) in H8.
  generalize H8; clear; intros.
  apply (f_equal (projx1 _ _ _)) in H8; simpl in H8.
  apply (f_equal (unexX _ _ _)) in H8; simpl in H8.
  apply inj_pair2 in H8.
  apply (f_equal (fun f => f "f")) in H8.
  apply (f_equal (uninjX _ _ _)) in H8; simpl in H8.
  assert ("f" = "f") by auto.
  rewrite H8 in H.
  discriminate.

  destruct (weq x2 x2); try tauto.
  injection H24; clear H24; intros; subst.
  inversion H30; clear H30; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end.
  inversion H19; clear H19; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  inversion H24; clear H24; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *; try discriminate.
  inversion H30; clear H30; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end.
  inversion H19; clear H19; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  inversion H24; clear H24; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end.
  inversion H30; clear H30; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  inversion H19; clear H19; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  inversion H20; clear H20; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  match goal with
    | [ H : myFuncs _ ?X = _ |- _ ] => change X with x5 in *
  end.
  unfold myFuncs in H30; simpl in H30.
  rewrite H1 in H30; rewrite H7 in H30.
  destruct (weq x5 x5); congruence.
  match goal with
    | [ H : myFuncs _ ?X = _ |- _ ] => change X with x5 in *
  end.
  unfold myFuncs in H24; simpl in H24.
  rewrite H1 in H24; rewrite H7 in H24.
  destruct (weq x5 x5); try tauto.
  injection H24; clear H24; intros; subst.
  inversion H36; clear H36; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end.
  inversion H19; clear H19; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  inversion H24; clear H24; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *; try discriminate.
  inversion H36; clear H36; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  inversion H32; clear H32; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end.
  inversion H20; clear H20; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  inversion H36; clear H36; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  constructor; intros; simpl; autorewrite with sepFormula.
  constructor; intros; simpl; autorewrite with sepFormula.
  hnf; simpl; autorewrite with sepFormula; split; simpl; auto.
  inversion H17; clear H17; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  constructor; intros; simpl; autorewrite with sepFormula.
  hnf; simpl; autorewrite with sepFormula; split; simpl; auto.
  (* Done with Safety! *)

  step hints.
  descend; step hints.
  descend; step hints.
  descend; step hints.

  (* Big RunsTo inversion *)
  generalize H18 H1 H7 H8 H12; clear; intros H12 Hg Hf Hgs Hfs.
  inversion H12; clear H12; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end.
  inversion H1; clear H1; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end; simpl in *; autorewrite with sepFormula in *.
  inversion H4; clear H4; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end; simpl in *; autorewrite with sepFormula in *; try discriminate.
  inversion H6; clear H6; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end.
  inversion H1; clear H1; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end; simpl in *; autorewrite with sepFormula in *.
  inversion H4; clear H4; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end.
  inversion H1; clear H1; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end; simpl in *; autorewrite with sepFormula in *.
  inversion H6; clear H6; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end.
  inversion H1; clear H1; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end; simpl in *; autorewrite with sepFormula in *. 
  match goal with
    | [ H : myFuncs _ ?X = _ |- _ ] => change X with x2 in *
  end.
  unfold myFuncs in H8; simpl in H8.
  rewrite Hf in H8; rewrite Hg in H8.
  destruct (weq x2 x5); try congruence.
  destruct (weq x2 x2); congruence.
  match goal with
    | [ H : myFuncs _ ?X = _ |- _ ] => change X with x2 in *
  end.
  unfold myFuncs in H6; simpl in H6.
  rewrite Hf in H6; rewrite Hg in H6.
  destruct (weq x2 x5).
  exfalso; subst.
  rewrite Hfs in Hgs.
  injection Hgs; clear Hgs; intros.
  apply (f_equal (fun f => f (leSettings m, {| Mem := fun _ => None; Regs := fun _ => $0 |}))) in H.
  generalize H; clear; intros.
  apply (f_equal (projx1 _ _ _)) in H; simpl in H.
  apply (f_equal (unexX _ _ _)) in H; simpl in H.
  apply inj_pair2 in H.
  apply (f_equal (fun f => f "f")) in H.
  apply (f_equal (uninjX _ _ _)) in H; simpl in H.
  assert ("f" = "f") by auto.
  rewrite H in H0.
  discriminate.

  destruct (weq x2 x2); try tauto.
  injection H6; clear H6; intros; subst.
  inversion H12; clear H12; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end.
  inversion H1; clear H1; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end; simpl in *; autorewrite with sepFormula in *.
  inversion H6; clear H6.
  simpl in H8.
  rewrite sel_upd_eq' in H8 by auto.
  match goal with
    | [ _ : context[if ?E then _ else _] |- _ ] => change E with false in *
  end.
  discriminate.
  repeat match goal with
           | [ x : _ |- _ ] => subst x
         end; simpl in *; autorewrite with sepFormula in *.
  inversion H12; clear H12; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end.
  inversion H1; clear H1; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end; simpl in *; autorewrite with sepFormula in *.
  inversion H6; clear H6; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end.
  inversion H1; clear H1; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end; simpl in *; autorewrite with sepFormula in *.
  inversion H12; clear H12; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end.
  inversion H1; clear H1; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end; simpl in *; autorewrite with sepFormula in *.
  match goal with
    | [ H : myFuncs _ ?X = _ |- _ ] => change X with x5 in *;
      unfold myFuncs in H; simpl in H;
        rewrite Hf in H; rewrite Hg in H
  end.
  destruct (weq x5 x5); congruence.
  match goal with
    | [ H : myFuncs _ ?X = _ |- _ ] => change X with x5 in *;
      unfold myFuncs in H; simpl in H;
        rewrite Hf in H; rewrite Hg in H
  end.
  destruct (weq x5 x5); try tauto.
  injection H12; clear H12; intros; subst.
  inversion H18; clear H18; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end.
  inversion H1; clear H1; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end; simpl in *; autorewrite with sepFormula in *.
  inversion H12; clear H12; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *; try discriminate.
  inversion H18; clear H18; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  inversion H6; clear H6; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end.
  inversion H2; clear H2; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end; simpl in *; autorewrite with sepFormula in *.
  inversion H18; clear H18; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  inversion H4; clear H4; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end.
  inversion H3; clear H3; repeat match goal with
                                   | [ x : _ |- _ ] => subst x
                                 end; simpl in *; autorewrite with sepFormula in *.
  inversion H18; clear H18; repeat match goal with
                                     | [ x : _ |- _ ] => subst x
                                   end; simpl in *; autorewrite with sepFormula in *.
  hnf; simpl; autorewrite with sepFormula.
  intuition idtac.
  
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
