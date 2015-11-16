Require Import Bedrock.Platform.Facade.Facade.
Require Import Bedrock.Memory.
Require Import Coq.Sets.Ensembles.

Require Import Bedrock.Bedrock.

Require Import Bedrock.Platform.Facade.examples.TuplesF.

Inductive ADTValue :=
| Tuple (t : tupl)
| List (ts : list tupl)
| Tuples0 (len : W) (ts : tuples)
| Tuples1 (len key : W) (ts : tuples).

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
        PreCond := fun args => exists len, args = [SCA _ len]
                                           /\ len >= $2;
        PostCond := fun args ret => exists len ls, args = [(SCA _ len, None)]
                                                   /\ ret = ADT (Tuple ls)
                                                   /\ length ls = wordToNat len
      |}; crush_types.
  Defined.

  Definition Tuple_delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists ls, args = [ADT (Tuple ls); SCA _ (length ls)];
        PostCond := fun args ret => exists ls, args = [(ADT (Tuple ls), None); (SCA _ (length ls), None)]
                                               /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Tuple_copy : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists ls, args = [ADT (Tuple ls); SCA _ (length ls)]
                                          /\ natToW (length ls) >= $2;
        PostCond := fun args ret => exists ls, args = [(ADT (Tuple ls), Some (Tuple ls)); (SCA _ (length ls), None)]
                                               /\ ret = ADT (Tuple ls)
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

Section ListADTSpec.

  Definition List_new : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => args = [];
        PostCond := fun args ret => args = [] /\ ret = ADT (List [])
      |}; crush_types.
  Defined.

  Definition List_delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => args = [ADT (List nil)];
        PostCond := fun args ret => args = [ (ADT (List nil), None) ]
                                    /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition List_copy : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l len,
                       args = [ADT (List l); SCA _ len]
                       /\ allTuplesLen (wordToNat len) l
                       /\ $2 <= len;
        PostCond := fun args ret =>
                      exists l len,
                        args = [ (ADT (List l), Some (List l)); (SCA _ len, None) ] /\
                        ret = ADT (List l)
      |}; crush_types.
  Defined.

  Definition List_pop : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists h t,
                       args = [ADT (List (h :: t))];
        PostCond := fun args ret =>
                      exists h t,
                        args = [ (ADT (List (h :: t)), Some (List t)) ] /\
                        ret = ADT (Tuple h)
      |}; crush_types.
  Defined.

  Definition List_empty : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (List l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [(ADT (List l), Some (List l))] /\
                        exists w, ret = SCA _ w /\ propToWord (l = nil) w
      |}; crush_types.
  Defined.

  Definition List_push : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l t,
                       args = [ADT (List l); ADT (Tuple t)];
        PostCond := fun args ret =>
                      exists l t,
                        args = [ (ADT (List l), Some (List (t :: l))); (ADT (Tuple t), None) ] /\
                        ret = SCAZero
      |}; crush_types.
  Defined.

  Definition List_rev : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (List l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (List l), Some (List (rev l))) ] /\
                        ret = SCAZero
      |}; crush_types.
  Defined.

  Definition List_length : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (List l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (List l), Some (List l)) ] /\
                        ret = SCA _ (natToWord _ (length l))
      |}; crush_types.
  Defined.

End ListADTSpec.

Section Tuples0ADTSpec.

  Definition Tuples0_new : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists len, args = [SCA _ len]
                                                    /\ len >= $2;
        PostCond := fun args ret => exists len, args = [(SCA _ len, None)]
                                                /\ ret = ADT (Tuples0 len Empty)
      |}; crush_types.
  Defined.

  Definition Tuples0_insert : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len ts t,
                       args = [ADT (Tuples0 len ts); ADT (Tuple t)]
                       /\ bounded ts
                       /\ length t = wordToNat len;
        PostCond := fun args ret =>
                      exists len ts t idx,
                        args = [ (ADT (Tuples0 len ts), Some (Tuples0 len (insertAt ts idx t)));
                                 (ADT (Tuple t), None) ]
                        /\ minFreshIndex ts idx
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Tuples0_enumerate : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len ts,
                       args = [ADT (Tuples0 len ts)];
        PostCond := fun args ret =>
                      exists len ts l,
                        args = [ (ADT (Tuples0 len ts), Some (Tuples0 len ts)) ]
                        /\ ret = ADT (List l)
                        /\ EnsembleIndexedListEquivalence ts l
      |}; crush_types.
  Defined.

End Tuples0ADTSpec.

Section Tuples1ADTSpec.

  Definition Tuples1_new : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists len key, args = [SCA _ len; SCA _ key]
                                               /\ len >= $2
                                               /\ key < len;
        PostCond := fun args ret => exists len key, args = [(SCA _ len, None); (SCA _ key, None)]
                                                    /\ ret = ADT (Tuples1 len key Empty)
      |}; crush_types.
  Defined.

  Definition Tuples1_insert : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key ts t,
                       args = [ADT (Tuples1 len key ts); ADT (Tuple t)]
                       /\ bounded ts
                       /\ length t = wordToNat len;
        PostCond := fun args ret =>
                      exists len key ts t idx,
                        args = [ (ADT (Tuples1 len key ts), Some (Tuples1 len key (insertAt ts idx t)));
                                 (ADT (Tuple t), None) ]
                        /\ minFreshIndex ts idx
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Tuples1_enumerate : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key ts,
                       args = [ADT (Tuples1 len key ts)]
                       /\ functional ts;
        PostCond := fun args ret =>
                      exists len key ts l,
                        args = [ (ADT (Tuples1 len key ts), Some (Tuples1 len key ts)) ]
                        /\ ret = ADT (List l)
                        /\ EnsembleIndexedListEquivalence ts l
      |}; crush_types.
  Defined.

  Definition Tuples1_find : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key ts k,
                       args = [ADT (Tuples1 len key ts); SCA _ k];
        PostCond := fun args ret =>
                      exists len key ts k l,
                        args = [ (ADT (Tuples1 len key ts), Some (Tuples1 len key ts)); (SCA _ k, None) ]
                        /\ ret = ADT (List l)
                        /\ EnsembleIndexedListEquivalence (keepEq ts key k) l
      |}; crush_types.
  Defined.

End Tuples1ADTSpec.
