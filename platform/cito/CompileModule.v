Require Import SyntaxModule.
Require Import List.
Require CompileFunc.
Require Import GoodFunc GoodOptimizer.

Set Implicit Arguments.

Definition GoodFunc := { f | GoodFunc.GoodFunc f }.

Require Import Semantics.
Record GoodModule :=
  {
    Name : string;
    Imports : LabelMap.t Callee;
    Funcs : list GoodFunc
  }.
    
Section TopSection.

  Variable module : GoodModule.

  Require Import StructuredModule.
  Definition imports : list import.
    admit.
  Qed.

  Variable optimizer : Optimizer.

  Hypothesis good_optimizer : GoodOptimizer optimizer.

  Definition compile_func' f (good_func : GoodFunc.GoodFunc f) := CompileFunc.compile (Name module) good_func good_optimizer.

  Definition compile_func (p : GoodFunc) :=
    match p with
      | exist _ good_func => compile_func' good_func
    end.

  Definition compiled_funcs := map compile_func (Funcs module).

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