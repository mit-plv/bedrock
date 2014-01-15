Set Implicit Arguments.

Require Import GoodFunc.
Require Import SyntaxFunc.
Export SyntaxFunc.

Record GoodFunction := 
  {
    Fun : Func;
    NoDupArgVars : NoDup (ArgVars Fun);
    WellFormedBody : WellFormed (Body Fun)
  }.

Coercion Fun : GoodFunction >-> Func.
    
Definition to_good_function (f : Func) : GoodFunc f -> GoodFunction.
    intros.
    destruct H.
    econstructor.
    eauto.
    eauto.
Defined.

Lemma to_good_function_name : forall (f : Func) (H : GoodFunc f), Name (to_good_function f H) = SyntaxFunc.Name f.
  intros.
  destruct H.
  unfold to_good_function.
  eauto.
Qed.

Lemma to_func_good : forall (f : GoodFunction), GoodFunc f.
  intros.
  destruct f.
  split; simpl; eauto.
Qed.    