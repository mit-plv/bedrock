Set Implicit Arguments.

Require Import GoodFunction.

Record GoodModule :=
  {
    Name : string;
    Functions : list GoodFunction;
    NoDupFuncNames : NoDup (map (fun (f : GoodFunction) => SyntaxFunc.Name f) Functions)
  }.