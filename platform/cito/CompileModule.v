Require Import SyntaxModule.
Require Import List.
Require CompileFunc.
Require Import GoodFunc GoodOptimizer.

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

  Variable module : CitoModule.

  Require Import CompileFuncImpl.
  Record GoodModule module := 
    {
      NoDupFuncNames_ : NoDup (map Name (Functions module));
      GoodFuncs : List.Forall GoodFunc (Functions module)
    }.

  Hypothesis good_module : GoodModule module.

  Require Import StructuredModule.
  Definition imports : list import := nil.

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

  Lemma module_name_not_in_imports : NameNotInImports (ModuleName module) imports.
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