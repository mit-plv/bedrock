Set Implicit Arguments.

Require Import Link.
Require Import ExampleADT ExampleImpl.

Module Import LinkMake := Link.Make ExampleADT ExampleRepInv.

Section TopSection.

  Require Import Notations2.

  Open Scope stmt_scope.

  Notation "$ n" := (natToW n).

  Definition body := 
    "ret" <- $0.

  Require Import SyntaxFunc.
  Require Import List.

  Definition return_zero : Func :=
    {|
      Name := "return_zero";
      Core := 
        {|
          ArgVars := nil;
          RetVar := "ret";
          Body := body
        |}
    |}.

  Require Import SyntaxModule.

  Definition return_zero_m : Module :=
    {|
      Name := "return_zero";
      Functions := return_zero :: nil
    |}.

  Require Import GoodModule.

  Notation MName := SyntaxModule.Name.
  Notation FName := SyntaxFunc.Name.
  Notation Funcs := SyntaxModule.Functions.

  Require Import GoodFunc.

  Require Import Program.Basics.

  Infix "*" := compose.

  Definition IsGoodModule (m : Module) :=
    IsGoodModuleName (MName m) /\
    List.Forall (GoodFunc * Core) (Funcs m) /\
    List.NoDup (List.map FName (Funcs m)).

  Definition to_good_module (m : Module) : IsGoodModule m -> GoodModule.
    intros.
    unfold IsGoodModule in *.
    Require Import GeneralTactics.
    openhyp.
    econstructor.
    eauto.
    Require Import GoodFunction.
    Definition to_good_functions (ls : list Func) : List.Forall (GoodFunc * Core) ls -> list GoodFunction.
      induction ls; simpl; intros.
      eapply nil.
      eapply cons.
      econstructor.
      instantiate (1 := a).
      eapply Forall_forall in H; intuition.
      unfold compose in *.
      eauto.
      eapply IHls.
      eapply Forall_forall.
      intros.
      eapply Forall_forall with (l := a :: ls) in H.
      eauto.
      intuition.
    Defined.
    instantiate (1 := to_good_functions H0).
    Lemma to_good_functions_name : forall ls (h : List.Forall (GoodFunc * Core) ls), map (fun f : GoodFunction => FName f) (to_good_functions h) = map FName ls.
      induction ls; simpl; intros.
      eauto.
      f_equal; eauto.
    Qed.
    rewrite to_good_functions_name.
    eauto.
  Defined.

  Definition to_module (m : GoodModule) : Module := 
    {|
      SyntaxModule.Name := GoodModule.Name m;
      SyntaxModule.Functions := map GoodFunction.Fun (GoodModule.Functions m)
    |}.

  Coercion to_module : GoodModule >-> Module.

  Lemma return_zero_good_module : IsGoodModule return_zero_m.
    admit.
  Qed.

  Definition return_zero_gm := to_good_module return_zero_good_module.

  Import StubsMake StubMake.
  Require Import Label.
  Import Label.LabelMap.

  Definition return_zero_func_spec := func_spec (return_zero_gm :: nil) (empty _) ("return_zero", "return_zero") return_zero.

  Notation extra_stack := 10.

  Definition return_zero_topS := SPEC reserving (2 + extra_stack)
    PRE[_] Emp
    POST[R] [| R = 0 |].

  Definition return_zero_top := bimport [[ ("return_zero", "return_zero", return_zero_func_spec) ]]
    bmodule "return_zero_top" {{
      bfunction "return_zero_top"("extra_stack", "R") [return_zero_topS]
        "extra_stack" <- extra_stack;;
        "R" <-- Call "return_zero"!"return_zero"()
        [PRE[_, R] [| R = 0 |]
         POST[R'] [| R' = R |] ];;
        Return "R"
      end
    }}.

  Theorem return_zero_top_ok : moduleOk return_zero_top.
    vcgen; post; sep_auto.
    instantiate (1 := x5).
    sep_auto.


  