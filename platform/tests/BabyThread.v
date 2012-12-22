Require Import Thread.


Definition handlerS := SPECthd reserving 14
  PREonly[_] Emp.

Definition mainS := SPEC reserving 23
  PREonly[_] mallocHeap 0.

Definition m := bimport [[ "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS] ]]
  bmodule "test" {{
    tfunctionNoRet "handler"() [handlerS]
      Exit
    end with bfunctionNoRet "main"("sc") [mainS]
      "sc" <-- Call "scheduler"!"init"()
      [PREonly[_, R] sched R * mallocHeap 0];;

      Spawn("sc", "test"!"handler", 16)
      [PREonly[V] sched (V "sc") * mallocHeap 0];;

      Go "sc"
    end
  }}.

Theorem ok : moduleOk m.
  vcgen.

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.

  post.
  evaluate auto_ext.
  descend.

  toFront_conc ltac:(fun P => match P with
                                | starting _ _ _ => idtac
                              end).
  apply starting_intro.
  descend.
  Focus 2.
  sep_auto.
  discriminate.
  eauto.
  unfold threadInvariantCont.
  descend.
  apply andL; apply injL; intro.
  apply andL; apply injL; intro.
  apply andL; apply cptrL; intro.
  apply andL; apply injL; intro.
  eapply existsXR; unfold Subst; simpl.
  eapply existsR.
  apply andR.
  eapply existsXR; unfold Subst; simpl.
  descend.
  apply andL; apply implyR.
  instantiate (1 := fun p => Emp%Sep (fst p) (snd p)).
  instantiate (1 := fun p => sched_ (fst p) (snd p)).
  instantiate (1 := vs).
  clear.
  step auto_ext.
  eapply existsR.
  apply andR.
  apply injR; eauto.
  apply (f_equal (fun f => f (labl "scheduler" "exit"))) in H11.
  etransitivity; eassumption.
  eapply existsXR; unfold Subst; simpl.
  apply andR.
  apply cptrR; eauto.
  apply andL; apply swap; apply implyR.
  rewrite H13; rewrite <- H11; rewrite sepFormula_eq; apply Imply_refl.
  step auto_ext.
  descend; step auto_ext.
  descend; step auto_ext.
  
  sep_auto.
  sep_auto.
  sep_auto.
Qed.
