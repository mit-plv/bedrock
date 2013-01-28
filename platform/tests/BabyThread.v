Require Import Thread0.


Module Make(M : S).
Import M.

Module T := Thread0.Make(M).
Import T.

Definition handlerS := SPEC reserving 19
  PREmain[_] sched * mallocHeap 0.

Definition mainS := SPEC reserving 36
  PREmain[_] globalSched =?> 1 * mallocHeap 0.

Definition m := bimport [[ "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS] ]]
  bmodule "test" {{
    bfunctionNoRet "handler"("xx", "yy") [handlerS]
      Exit 20
    end with bfunctionNoRet "main"("xx", "yy") [mainS]
      Init
      [PREmain[_] sched * mallocHeap 0];;

      Spawn("test"!"handler", 20)
      [PREmain[_] sched * mallocHeap 0];;

      Spawn("test"!"handler", 20)
      [PREmain[_] sched * mallocHeap 0];;

      Go 36
    end
  }}.

Theorem ok : moduleOk m.
  vcgen.

  sep_auto.
  sep_auto.
  sep_auto.

  post; evaluate auto_ext.
  congruence.
  descend.
  Focus 2.

  Opaque mult.

  Lemma exitize_locals : forall xx yy ns vs res sp,
    locals ("rp" :: xx :: yy :: ns) vs res sp ===> Ex vs', locals ("rp" :: "sc" :: "ss" :: nil) (upd vs' "ss" (sel vs yy)) (res + length ns) sp.
    unfold locals; intros.
    simpl; unfold upd; simpl.
    apply Himp_ex_c; exists vs.
    apply Himp_star_frame.
    

    

  change (locals ("rp" :: "xx" :: "yy" :: nil) (upd x0 "yy" 20) 17 (Regs x Sp))
    with (locals ("rp" :: "xx" :: "yy" :: nil) (upd x0 "yy" 20) 17 (Regs x Sp))

  step hints.
  



  vcgen; abstract sep_auto.
Qed.

End Make.
