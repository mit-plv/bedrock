Require Import Thread0 WebServer Bootstrap.


Module Type S.
  Variable heapSize : nat.
End S.

Module Make(M : S).
Import M.

Module M'.
  Definition globalSched : W := (heapSize + 50) * 4.
  Definition globalSock : W := globalSched ^+ $4.
  Definition globalTree : W := globalSched ^+ $8.
  Definition globalPages : W := globalSched ^+ $12.

  Definition port : W := 8080.
  Definition numWorkers : W := 2.

  Definition inbuf_size := 256.

  Theorem inbuf_size_lower : (inbuf_size >= 2)%nat.
    unfold inbuf_size; auto.
  Qed.

  Theorem inbuf_size_upper : (N_of_nat (inbuf_size * 4) < Npow2 32)%N.
    reflexivity.
  Qed.
End M'.

Import M'.

Module E := WebServer.Make(M').
Import E.

Section boot.
  Hypothesis heapSizeLowerBound : (3 <= heapSize)%nat.

  Definition size := heapSize + 50 + 3.

  Hypothesis mem_size : goodSize (size * 4)%nat.

  Let heapSizeUpperBound : goodSize (heapSize * 4).
    goodSize.
  Qed.

  Definition bootS := {|
    Reserved := 49;
    Formals := nil;
    Precondition := fun _ => st ~> Ex n, ![ 0 =?> (heapSize + 50 + 3) * strings n globalPages ] st
  |}.

  Definition boot := bimport [[ "malloc"!"init" @ [Malloc.initS], "web"!"main" @ [E.mainS] ]]
    bmodule "main" {{
      bfunctionNoRet "main"() [bootS]
        Sp <- (heapSize * 4)%nat;;

        Assert [Al n, PREmain[_] 0 =?> heapSize * globalSched =?> 3 * strings n globalPages ];;

        Call "malloc"!"init"(0, heapSize)
        [Al n, PREmain[_] globalSched =?> 1 * globalSock =?> 1 * globalTree =?> 1 * strings n globalPages
          * mallocHeap 0];;

        Goto "web"!"main"
      end
    }}.

  Ltac t := unfold globalSched, localsInvariantMain, M'.globalSock, M'.globalSched, M'.globalTree, M'.globalPages;
    genesis; rewrite natToW_plus; reflexivity.

  Theorem ok0 : moduleOk boot.
    vcgen; abstract t.
  Qed.

  Definition m1 := link boot E.T.m.
  Definition m2 := link Buffers.m m1.
  Definition m3 := link E.MyIo.m m2.
  Definition m4 := link StringDb.m m3.
  Definition m := link E.m m4.

  Lemma ok1 : moduleOk m1.
    link ok0 E.T.ok.
  Qed.

  Lemma ok2 : moduleOk m2.
    link Buffers.ok ok1.
  Qed.

  Lemma ok3 : moduleOk m3.
    link E.MyIo.ok ok2.
  Qed.

  Lemma ok4 : moduleOk m4.
    link StringDb.ok ok3.
  Qed.

  Theorem ok : moduleOk m.
    link E.ok ok4.
  Qed.

  Variable stn : settings.
  Variable prog : program.
  
  Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
    -> Labels stn l2 = Some w
    -> l1 = l2.

  Hypothesis agree : forall l pre bl,
    LabelMap.MapsTo l (pre, bl) (XCAP.Blocks m)
    -> exists w, Labels stn l = Some w
      /\ prog w = Some bl.

  Hypothesis agreeImp : forall l pre, LabelMap.MapsTo l pre (XCAP.Imports m)
    -> exists w, Labels stn l = Some w
      /\ prog w = None.

  Hypothesis omitImp : forall l w,
    Labels stn ("sys", l) = Some w
    -> prog w = None.

  Variable w : W.
  Hypothesis at_start : Labels stn ("main", Global "main") = Some w.

  Variable st : state.

  Hypothesis prec : forall specs, interp specs (Precondition bootS None (stn, st)).

  Import Safety.

  Theorem safe : sys_safe stn prog (w, st).
    eapply safety; try eassumption; [
      link_simp; unfold labelSys, labelSys'; simpl; tauto
      | apply ok
      | apply LabelMap.find_2; link_simp; reflexivity
      | auto ].
  Qed.
End boot.

End Make.
