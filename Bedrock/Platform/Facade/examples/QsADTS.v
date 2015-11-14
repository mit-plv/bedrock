Require Import Bedrock.Platform.Facade.Facade.
Require Import Bedrock.Memory.
Require Import Coq.Sets.Ensembles.

Require Import Bedrock.Bedrock.

Inductive ADTValue :=
| Tuple : list W -> ADTValue.

Require Import Bedrock.Platform.Cito.ADT.

Module Adt <: ADT.

  Definition ADTValue := ADTValue.

End Adt.

Require Import Coq.Lists.List Coq.Program.Program.

Definition SCAZero {t} := SCA t (Word.natToWord 32 0).
Definition SCAOne  {t} := SCA t (Word.natToWord 32 1).

Ltac crush_types :=
  unfold type_conforming, same_types, same_type; intros;
  repeat match goal with
           | [ H: exists t, _ |- _ ] => destruct H
         end; repeat progress (subst; intuition).

Section TupleADTSpec.

  Definition Tuple_new : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists len, args = [SCA _ len];
        PostCond := fun args ret => exists len ls, args = [(SCA _ len, None)]
                                                   /\ ret = ADT (Tuple ls)
                                                   /\ length ls = wordToNat len
      |}; crush_types.
  Defined.

  Definition Tuple_delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists ls, args = [ADT (Tuple ls)];
        PostCond := fun args ret => exists ls, args = [(ADT (Tuple ls), None)] /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Tuple_get : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists ls pos,
                       args = [ADT (Tuple ls); SCA _ pos]
                       /\ pos < natToW (length ls);
        PostCond := fun args ret =>
                      exists ls pos,
                        args = [(ADT (Tuple ls), Some (Tuple ls)); (SCA _ pos, None)] /\
                        ret = SCA _ (Array.sel ls pos)
      |}; crush_types.
  Defined.

  Definition Tuple_set : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists ls pos val,
                       args = [ADT (Tuple ls); SCA _ pos; SCA _ val]
                       /\ pos < natToW (length ls);
        PostCond := fun args ret =>
                      exists ls pos val,
                        args = [(ADT (Tuple ls), Some (Tuple (Array.upd ls pos val)));
                                 (SCA _ pos, None); (SCA _ val, None)] /\
                        ret = SCAZero
      |}; crush_types.
  Defined.

End TupleADTSpec.
