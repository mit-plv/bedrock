Set Implicit Arguments.

Require Import GoodFunction.

Definition IsGoodModuleName (s : string) := prefix "_" s = false.

Record GoodModule :=
  {
    Name : string;
    GoodModuleName : IsGoodModuleName Name;
    Functions : list GoodFunction;
    NoDupFuncNames : NoDup (map (fun (f : GoodFunction) => SyntaxFunc.Name f) Functions)
  }.