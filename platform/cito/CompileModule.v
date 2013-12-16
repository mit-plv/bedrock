Require Import SyntaxModule.
Require Import List.
Require CompileFunc.
Require Import GoodFunc GoodOptimizer.

Set Implicit Arguments.

Section TopSection.

  Variable module : CitoModule.

  Require Import CompileFuncImpl.
  Record GoodModule module := 
    {
      NoDupFuncNames : NoDup (map Name (Functions module));
      GoodFuncs : List.Forall GoodFunc (Functions module)
    }.

  Hypothesis good_module : GoodModule module.

  Require Import StructuredModule.
  Variable imports : list import.

  Variable optimizer : Optimizer.

  Hypothesis good_optimizer : GoodOptimizer optimizer.

  Definition to_prod_list : forall A P (ls : list A), List.Forall P ls -> list { x | P x }.
    induction ls.
    econstructor 1.
    econstructor 2.
    econstructor; inversion H; subst; eauto.
    eapply IHls; inversion H; subst; eauto.
  Defined.

  Definition compile_func' f (good_func : GoodFunc f) := CompileFunc.compile (ModuleName module) good_func good_optimizer.

  Definition compile_func (p : { f | GoodFunc f }) :=
    match p with
      | exist _ good_func => compile_func' good_func
    end.

  Definition compiled_funcs := map compile_func (to_prod_list (GoodFuncs good_module)).

  Require Import Structured.
  Require Import Wrap.
  Lemma good_vcs : forall ls, vcs (makeVcs imports compiled_funcs (map compile_func ls)).
    induction ls; simpl; eauto; destruct a; simpl; unfold CompileFuncSpec.imply; wrap0.
  Qed.

  Definition compile := StructuredModule.bmodule_ imports compiled_funcs.

  Theorem compileOk : XCAP.moduleOk compile.
    eapply bmoduleOk.
    admit.
    admit.
    eapply good_vcs.
  Qed.

End TopSection.