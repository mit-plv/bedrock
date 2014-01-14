Require Import SyntaxModule.
Require Import List.
Require CompileFunc.
Require Import GoodFunc GoodOptimizer.
Require Import GoodModule.

Set Implicit Arguments.

Definition NameNotInImports name imports := 
  fold_left
    (fun (b : bool) (p : string * string * assert) =>
       let '(m, _, _) := p in
       (b || (if string_dec m name then true else false))%bool)
    imports false = false.

Definition NoDupFuncNames mod_name funcs :=
  match
    fold_left
      (fun (mOpt : option (LabelMap.t unit))
           (p : string * assert *
                (forall imports : LabelMap.t assert,
                   importsGlobal imports -> cmd imports mod_name)) =>
         let '(modl, _, _) := p in
         match mOpt with
           | Some m =>
             let k := (modl, Local 0) in
             if LabelMap.mem (elt:=unit) k m
             then None
             else Some (LabelMap.add k tt m)
           | None => None
         end) funcs (Some (LabelMap.empty unit))
  with
    | Some _ => True
    | None => False
  end.

Section TopSection.

  Variable module : GoodModule.

  Require Import CompileFuncImpl.
  Require Import StructuredModule.
  Definition imports : list import := nil.

  Variable optimizer : Optimizer.

  Hypothesis good_optimizer : GoodOptimizer optimizer.

  Require Import NameDecoration.
  Definition mod_name := impl_module_name (Name module).

  Definition compile_func' f (good_func : GoodFunc f) := CompileFunc.compile mod_name good_func good_optimizer.

  Definition compile_func (p : GoodFunction.GoodFunction) := compile_func' (GoodFunction.to_func_good p).

  Definition compiled_funcs := map compile_func (Functions module).

  Require Import Structured.
  Require Import Wrap.
  Lemma good_vcs : forall ls, vcs (makeVcs imports compiled_funcs (map compile_func ls)).
    induction ls; simpl; eauto; destruct a; simpl; unfold CompileFuncSpec.imply; wrap0.
  Qed.

  Definition compile := StructuredModule.bmodule_ imports compiled_funcs.

  Lemma module_name_not_in_imports : NameNotInImports mod_name imports.
    unfold NameNotInImports; eauto.
  Qed.

  Lemma no_dup_func_names : NoDupFuncNames compiled_funcs.
    admit.
  Qed.

  Theorem compileOk : XCAP.moduleOk compile.
    eapply bmoduleOk.
    eapply module_name_not_in_imports.
    eapply no_dup_func_names.
    eapply good_vcs.
  Qed.

End TopSection.