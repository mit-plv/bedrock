Set Implicit Arguments.

Require Import Platform.Cito.GoodFunction.
Require Import Platform.Cito.NameDecoration.

Record GoodModule :=
  {
    Name : string;
    GoodModuleName : IsGoodModuleName Name;
    Functions : list GoodFunction;
    NoDupFuncNames : NoDup (map (fun (f : GoodFunction) => SyntaxFunc.Name f) Functions)
  }.