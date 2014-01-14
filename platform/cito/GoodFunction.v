Set Implicit Arguments.

Require Import GoodFunc.

Record GoodFunction := 
  {
    Name : string;
    ArgVars : list string;
    RetVar : string;
    Body : Stmt;
    NoDupArgVars : NoDup ArgVars;
    WellFormedBody : WellFormed Body
  }.
    
Definition to_good_function f : GoodFunc f -> GoodFunction.
    intros.
    destruct H.
    econstructor.
    eapply (SyntaxFunc.Name f).
    eapply (SyntaxFunc.RetVar f).
    eauto.
    eauto.
Defined.

Lemma to_good_function_name : forall f (H : GoodFunc.GoodFunc f), Name (to_good_function H) = SyntaxFunc.Name f.
  intros.
  destruct H.
  unfold to_good_function.
  eauto.
Qed.

Definition to_func (f : GoodFunction) : SyntaxFunc.Func :=
  {|
    SyntaxFunc.Name := Name f;
    SyntaxFunc.ArgVars := ArgVars f;
    SyntaxFunc.RetVar := RetVar f;
    SyntaxFunc.Body := Body f
  |}.

Lemma to_func_good : forall f, GoodFunc (to_func f).
  intros.
  unfold to_func.
  destruct f.
  split; simpl; eauto.
Qed.    