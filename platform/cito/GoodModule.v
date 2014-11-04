Set Implicit Arguments.

Require Import GoodFunction.
Require Import NameDecoration.

Record GoodModule :=
  {
    Name : string;
    GoodModuleName : IsGoodModuleName Name;
    Functions : list GoodFunction;
    NoDupFuncNames : NoDup (map (fun (f : GoodFunction) => SyntaxFunc.Name f) Functions)
  }.