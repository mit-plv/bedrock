Set Implicit Arguments.

Section TopSection.

  Require Import SyntaxModule.
  Variable module : CitoModule.

  Require Import List.
  Require CompileFunc.
  Record GoodModule := 
    {
      NoSelfImport : ~ In (ModuleName module) (map (@fst _ _) (Imports module));
      NoDupFuncNames : NoDup (map Name (Functions module));
      GoodFuncs : Forall CompileFunc.GoodFunc (Functions module)
    }.

  Hypothesis good_module : GoodModule.

  Require Import StructuredModule.
  Variable imports : list import.

  Definition optimizer : Stmt -> Stmt := id.

  Definition compile_func f := CompileFunc.compile (ModuleName module) f optimizer.

  Definition compiled_funcs := map compile_func (Functions module).

  Require Import Structured.
  Require Import Wrap.
  Lemma good_vcs : forall ls, vcs (makeVcs imports compiled_funcs (map compile_func ls)).
    induction ls; simpl; unfold CompileFunc.imply; wrap0.
  Qed.

  Definition compile := StructuredModule.bmodule_ imports compiled_funcs.

  Theorem compileOk : XCAP.moduleOk compile.
    eapply bmoduleOk.
    admit.
    admit.
    eapply good_vcs.
  Qed.

End TopSection.