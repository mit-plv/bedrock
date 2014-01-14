Set Implicit Arguments.

Require Import GoodFunction.
Record GoodModule :=
  {
    Name : string;
    Functions : list GoodFunction;
    NoDupFuncNames : NoDup (map GoodFunction.Name Functions)
  }.