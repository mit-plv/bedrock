Require Import AutoSep Malloc ReturnZero Bootstrap.


Module Type S.
  Variable heapSize : nat.
End S.

Module Make(M : S).
Import M.

Section boot.
  Hypothesis heapSizeLowerBound : (3 <= heapSize)%nat.

  Definition size := heapSize + 50 + 0.

  Hypothesis mem_size : goodSize (size * 4)%nat.

  Let heapSizeUpperBound : goodSize (heapSize * 4).
    goodSize.
  Qed.

  Definition bootS := bootS heapSize 0.

  Definition boot := bimport [[ "malloc"!"init" @ [Malloc.initS], "top"!"top" @ [topS] ]]
    bmodule "main" {{
      bfunctionNoRet "main"() [bootS]
        Sp <- (heapSize * 4)%nat;;

        Assert [PREonly[_] 0 =?> heapSize];;

        Call "malloc"!"init"(0, heapSize)
        [PREonly[_] mallocHeap 0];;

        Call "top"!"top"()
        [PREonly[_] [| False |] ]
      end
    }}.

  Theorem ok : moduleOk boot.
    vcgen; abstract genesis.
  Qed.

  Definition m0 := link Malloc.m boot.
  Definition m1 := link all m0.

  Lemma ok0 : moduleOk m0.
    link Malloc.ok ok.
  Qed.

  Lemma ok1 : moduleOk m1.
    apply linkOk.
    apply all_ok.
    apply ok0.
    reflexivity.

    simpl Imports.
    Import Wrp.LinkMake.LinkModuleImplsMake.
    unfold CompileModuleMake.mod_name.
    unfold impl_module_name.
    simpl GName.
    simpl append.
    unfold CompileModuleMake.imports.
    unfold Wrp.LinkMake.StubsMake.StubMake.bimports_diff_bexports.
    unfold diff_map.
    simpl List.filter.
    unfold Wrp.LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export.
    unfold Wrp.LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label.
    simpl GName.
    unfold impl_module_name.
    simpl append.
    simpl IsGoodModule.FName.
    link_simp.
    auto.

    simpl Exports.
    unfold CompileModuleMake.mod_name.
    unfold impl_module_name.
    simpl GName.
    simpl append.
    link_simp.
    tauto.

    simpl Imports.
    unfold CompileModuleMake.mod_name.
    unfold impl_module_name.
    simpl GName.
    simpl append.
    unfold CompileModuleMake.imports.
    unfold Wrp.LinkMake.StubsMake.StubMake.bimports_diff_bexports.
    unfold diff_map.
    simpl List.filter.
    unfold Wrp.LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export.
    unfold Wrp.LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label.
    simpl GName.
    unfold impl_module_name.
    simpl append.
    simpl IsGoodModule.FName.
    link_simp.
    auto.
  Qed.

  Variable stn : settings.
  Variable prog : program.
  
  Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
    -> Labels stn l2 = Some w
    -> l1 = l2.

  Hypothesis agree : forall l pre bl,
    LabelMap.MapsTo l (pre, bl) (XCAP.Blocks m1)
    -> exists w, Labels stn l = Some w
      /\ prog w = Some bl.

  Hypothesis agreeImp : forall l pre, LabelMap.MapsTo l pre (XCAP.Imports m1)
    -> exists w, Labels stn l = Some w
      /\ prog w = None.

  Hypothesis omitImp : forall l w,
    Labels stn ("sys", l) = Some w
    -> prog w = None.

  Variable w : W.
  Hypothesis at_start : Labels stn ("main", Global "main") = Some w.

  Variable st : state.

  Hypothesis mem_low : forall n, (n < size * 4)%nat -> st.(Mem) n <> None.
  Hypothesis mem_high : forall w, $(size * 4) <= w -> st.(Mem) w = None.

  Theorem safe : sys_safe stn prog (w, st).
    eapply Safety.safety; try eassumption.

    simpl Imports.
    unfold CompileModuleMake.mod_name.
    unfold impl_module_name.
    simpl GName.
    simpl append.
    unfold CompileModuleMake.imports.
    unfold Wrp.LinkMake.StubsMake.StubMake.bimports_diff_bexports.
    unfold diff_map.
    simpl List.filter.
    unfold Wrp.LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export.
    unfold Wrp.LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label.
    simpl GName.
    unfold impl_module_name.
    simpl append.
    simpl IsGoodModule.FName.
    link_simp.
    unfold Safety.labelSys, Safety.labelSys'.
    simpl.
    tauto.

    apply ok1.

    apply LabelMap.find_2.
    simpl Exports.
    unfold CompileModuleMake.mod_name.
    unfold impl_module_name.
    simpl GName.
    simpl append.
    link_simp.
    reflexivity.

    propxFo.
    apply materialize_allocated.
    assumption.
    assumption.
    assumption.
  Qed.
End boot.

End Make.
