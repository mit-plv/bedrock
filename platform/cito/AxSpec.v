Set Implicit Arguments.

Section ADTSection.

  Variable ADTValue : Type.

  Require Import Memory.

  Inductive Value :=
  | SCA : W -> Value
  | ADT : ADTValue -> Value.

  Definition same_type a b := 
    match a, b with
      | ADT _, ADT _ => True
      | SCA _, SCA _ => True
      | _, _ => False
    end.

  Definition same_types ls1 ls2 := List.Forall2 same_type ls1 ls2.

  (* type_conforming precond : any n-length input list satisfying precond must conform to a n-length type signature. But inputs of different lengths can have different type signatures ('type' means ADT vs. scalar).
     This requirement is necessary for semantic-preserving compilation into Cito, which can nondeterministically interpret the inputs to an axiomatic call either as ADTs or as scalars, where the choice of ADT/scalar may not agree with Facade's state. *)
  Definition type_conforming precond := forall inputs1 inputs2, precond inputs1 -> precond inputs2 -> length inputs1 = length inputs2 -> same_types inputs1 inputs2.

  Record AxiomaticSpec :=
    {
      PreCond : list Value -> Prop;
      PostCond : list (Value * option ADTValue) -> Value -> Prop;
      PreCondTypeConform : type_conforming PreCond
    }.

End ADTSection.
