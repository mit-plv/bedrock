Require Import Bedrock.Platform.Facade.Facade.
Require Import Bedrock.Memory.
Require Import Coq.Sets.Ensembles.

Require Import Bedrock.Bedrock.

Require Import Bedrock.Platform.Facade.examples.TuplesF.

Inductive ADTValue :=
| Tuple (t : tupl)
| WordList (ws : list W)
| TupleList (ts : list tupl)
| Tuples0 (len : W) (ts : tuples)
| Tuples1 (len key : W) (ts : tuples)
| Tuples2 (len key1 key2 : W) (ts : tuples).

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
        PreCond := fun args => exists ls len, args = [ADT (Tuple ls); SCA _ len]
                                              /\ length ls = wordToNat len;
        PostCond := fun args ret => exists ls len, args = [(ADT (Tuple ls), None); (SCA _ len, None)]
                                                   /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Tuple_copy : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists ls len, args = [ADT (Tuple ls); SCA _ len]
                                              /\ length ls = wordToNat len
                                              /\ natToW (length ls) >= $2;
        PostCond := fun args ret => exists ls len, args = [(ADT (Tuple ls), Some (Tuple ls)); (SCA _ len, None)]
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

Section WordListADTSpec.

  Definition WordList_new : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => args = [];
        PostCond := fun args ret => args = [] /\ ret = ADT (WordList [])
      |}; crush_types.
  Defined.

  Definition WordList_delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists l, args = [ADT (WordList l)];
        PostCond := fun args ret => exists l, args = [(ADT (WordList l), None)] /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition WordList_pop : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists h t,
                       args = [ADT (WordList (h :: t))];
        PostCond := fun args ret =>
                      exists h t,
                        args = [ (ADT (WordList (h :: t)), Some (WordList t)) ] /\
                        ret = SCA ADTValue h
      |}; crush_types.
  Defined.

  Definition WordList_empty : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (WordList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [(ADT (WordList l), Some (WordList l))] /\
                        exists w, ret = SCA _ w /\ Bedrock.Programming.propToWord (l = nil) w
      |}; crush_types.
  Defined.

  Definition WordList_push : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l w,
                       args = [ADT (WordList l); SCA _ w];
        PostCond := fun args ret =>
                      exists l w,
                        args = [ (ADT (WordList l), Some (WordList (w :: l))); (SCA _ w, None) ] /\
                        ret = SCAZero
      |}; crush_types.
  Defined.

  Definition WordList_copy : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (WordList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (WordList l), Some (WordList l)) ] /\
                        ret = ADT (WordList l)
      |}; crush_types.
  Defined.

  Definition WordList_rev : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (WordList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (WordList l), Some (WordList (rev l))) ] /\
                        ret = SCAZero
      |}; crush_types.
  Defined.

  Definition WordList_length : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (WordList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (WordList l), Some (WordList l)) ] /\
                        ret = SCA _ (Word.natToWord _ (length l))
      |}; crush_types.
  Defined.

End WordListADTSpec.

Section TupleListADTSpec.

  Definition TupleList_new : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => args = [];
        PostCond := fun args ret => args = [] /\ ret = ADT (TupleList [])
      |}; crush_types.
  Defined.

  Definition TupleList_delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => args = [ADT (TupleList nil)];
        PostCond := fun args ret => args = [ (ADT (TupleList nil), None) ]
                                    /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition TupleList_copy : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l len,
                       args = [ADT (TupleList l); SCA _ len]
                       /\ allTuplesLen (wordToNat len) l
                       /\ $2 <= len;
        PostCond := fun args ret =>
                      exists l len,
                        args = [ (ADT (TupleList l), Some (TupleList l)); (SCA _ len, None) ] /\
                        ret = ADT (TupleList l)
      |}; crush_types.
  Defined.

  Definition TupleList_pop : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists h t,
                       args = [ADT (TupleList (h :: t))];
        PostCond := fun args ret =>
                      exists h t,
                        args = [ (ADT (TupleList (h :: t)), Some (TupleList t)) ] /\
                        ret = ADT (Tuple h)
      |}; crush_types.
  Defined.

  Definition TupleList_empty : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (TupleList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [(ADT (TupleList l), Some (TupleList l))] /\
                        exists w, ret = SCA _ w /\ propToWord (l = nil) w
      |}; crush_types.
  Defined.

  Definition TupleList_push : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l t,
                       args = [ADT (TupleList l); ADT (Tuple t)];
        PostCond := fun args ret =>
                      exists l t,
                        args = [ (ADT (TupleList l), Some (TupleList (t :: l))); (ADT (Tuple t), None) ] /\
                        ret = SCAZero
      |}; crush_types.
  Defined.

  Definition TupleList_rev : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (TupleList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (TupleList l), Some (TupleList (rev l))) ] /\
                        ret = SCAZero
      |}; crush_types.
  Defined.

  Definition TupleList_length : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (TupleList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (TupleList l), Some (TupleList l)) ] /\
                        ret = SCA _ (natToWord _ (length l))
      |}; crush_types.
  Defined.

End TupleListADTSpec.

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
                     exists len ts t idx,
                       args = [ADT (Tuples0 len ts); ADT (Tuple t)]
                       /\ minFreshIndex ts idx
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
                        /\ ret = ADT (TupleList l)
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
                     exists len key ts t idx,
                       args = [ADT (Tuples1 len key ts); ADT (Tuple t)]
                       /\ minFreshIndex ts idx
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
                        /\ ret = ADT (TupleList l)
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
                        /\ ret = ADT (TupleList l)
                        /\ EnsembleIndexedListEquivalence (keepEq ts key k) l
      |}; crush_types.
  Defined.
End Tuples1ADTSpec.

Section Tuples2ADTSpec.

  Definition Tuples2_new : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists len key1 key2,
                                 args = [SCA _ len; SCA _ key1; SCA _ key2]
                                 /\ len >= $2
                                 /\ key1 < len
                                 /\ key2 < len;
        PostCond := fun args ret => exists len key1 key2,
                                      args = [(SCA _ len, None); (SCA _ key1, None); (SCA _ key2, None)]
                                      /\ ret = ADT (Tuples2 len key1 key2 Empty)
      |}; crush_types.
  Defined.

  Definition Tuples2_insert : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key1 key2 ts t idx,
                       args = [ADT (Tuples2 len key1 key2 ts); ADT (Tuple t)]
                       /\ minFreshIndex ts idx
                       /\ length t = wordToNat len;
        PostCond := fun args ret =>
                      exists len key1 key2 ts t idx,
                        args = [ (ADT (Tuples2 len key1 key2 ts), Some (Tuples2 len key1 key2 (insertAt ts idx t)));
                                 (ADT (Tuple t), None) ]
                        /\ minFreshIndex ts idx
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Tuples2_enumerate : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key1 key2 ts,
                       args = [ADT (Tuples2 len key1 key2 ts)]
                       /\ functional ts;
        PostCond := fun args ret =>
                      exists len key1 key2 ts l,
                        args = [ (ADT (Tuples2 len key1 key2 ts), Some (Tuples2 len key1 key2 ts)) ]
                        /\ ret = ADT (TupleList l)
                        /\ EnsembleIndexedListEquivalence ts l
      |}; crush_types.
  Defined.

  Definition Tuples2_findBoth : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key1 key2 ts k1 k2,
                       args = [ADT (Tuples2 len key1 key2 ts); SCA _ k1; SCA _ k2];
        PostCond := fun args ret =>
                      exists len key1 key2 ts k1 k2 l,
                        args = [ (ADT (Tuples2 len key1 key2 ts), Some (Tuples2 len key1 key2 ts)); (SCA _ k1, None); (SCA _ k2, None) ]
                        /\ ret = ADT (TupleList l)
                        /\ EnsembleIndexedListEquivalence (keepEq (keepEq ts key1 k1) key2 k2) l
      |}; crush_types.
  Defined.

  Definition Tuples2_findFirst : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key1 key2 ts k,
                       args = [ADT (Tuples2 len key1 key2 ts); SCA _ k]
                       /\ functional ts;
        PostCond := fun args ret =>
                      exists len key1 key2 ts k l,
                        args = [ (ADT (Tuples2 len key1 key2 ts), Some (Tuples2 len key1 key2 ts)); (SCA _ k, None) ]
                        /\ ret = ADT (TupleList l)
                        /\ EnsembleIndexedListEquivalence (keepEq ts key1 k) l
      |}; crush_types.
  Defined.

  Definition Tuples2_findSecond : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key1 key2 ts k,
                       args = [ADT (Tuples2 len key1 key2 ts); SCA _ k]
                       /\ functional ts;
        PostCond := fun args ret =>
                      exists len key1 key2 ts k l,
                        args = [ (ADT (Tuples2 len key1 key2 ts), Some (Tuples2 len key1 key2 ts)); (SCA _ k, None) ]
                        /\ ret = ADT (TupleList l)
                        /\ EnsembleIndexedListEquivalence (keepEq ts key2 k) l
      |}; crush_types.
  Defined.

End Tuples2ADTSpec.
