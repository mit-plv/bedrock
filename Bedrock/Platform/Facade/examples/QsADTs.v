Require Import Bedrock.Platform.Facade.Facade.
Require Import Bedrock.Memory.
Require Import Coq.Sets.Ensembles.

Require Import Bedrock.Bedrock.

Require Import Bedrock.Platform.Facade.examples.TuplesF.

Definition WS := (sum W string).
Definition WSTupl := GenericTuple WS.
Definition WSTuplSet := GenericTuples WS.

Inductive ADTValue :=
| Tuple (t : tupl)
| WordList (ws : list W)
| TupleList (ts : list tupl)
| Tuples0 (len : W) (ts : tuples)
| Tuples1 (len key : W) (ts : tuples)
| Tuples2 (len key1 key2 : W) (ts : tuples)
| WSTuple (t : WSTupl)
| WSTupleList (ts : list WSTupl)
| ADTString (s: string)
| WSTrie (len keyIndex : W) (tuples : WSTuplSet)
| BagOfWSTuples1 (len keyIndex : W) (tuples : WSTuplSet).

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

Module Type TupleListADTSpecParams.
  Parameter FieldType : Type.
  Parameter TupleConstructor : forall (t: GenericTuple FieldType), ADTValue.
  Parameter ListConstructor : forall (ls: list (GenericTuple FieldType)), ADTValue.
End TupleListADTSpecParams.

Module TupleListADTSpec (Params: TupleListADTSpecParams).
  Import Params.

  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => args = [];
        PostCond := fun args ret => args = [] /\ ret = ADT (ListConstructor [])
      |}; crush_types.
  Defined.

  Definition Delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => args = [ADT (ListConstructor nil)];
        PostCond := fun args ret => args = [ (ADT (ListConstructor nil), None) ]
                                    /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Copy : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l len,
                       args = [ADT (ListConstructor l); SCA _ len]
                       /\ allTuplesLen (wordToNat len) l
                       /\ $2 <= len;
        PostCond := fun args ret =>
                      exists l len,
                        args = [ (ADT (ListConstructor l), Some (ListConstructor l)); (SCA _ len, None) ] /\
                        ret = ADT (ListConstructor l)
      |}; crush_types.
  Defined.

  Definition Pop : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists h t,
                       args = [ADT (ListConstructor (h :: t))];
        PostCond := fun args ret =>
                      exists h t,
                        args = [ (ADT (ListConstructor (h :: t)), Some (ListConstructor t)) ] /\
                        ret = ADT (TupleConstructor h)
      |}; crush_types.
  Defined.

  Definition Empty : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (ListConstructor l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [(ADT (ListConstructor l), Some (ListConstructor l))] /\
                        exists w, ret = SCA _ w /\ propToWord (l = nil) w
      |}; crush_types.
  Defined.

  Definition Push : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l t,
                       args = [ADT (ListConstructor l); ADT (Tuple t)];
        PostCond := fun args ret =>
                      exists l t,
                        args = [ (ADT (ListConstructor l), Some (ListConstructor (t :: l)));
                                 (ADT (TupleConstructor t), None) ] /\
                        ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Rev : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (ListConstructor l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (ListConstructor l), Some (ListConstructor (rev l))) ] /\
                        ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Length : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (ListConstructor l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (ListConstructor l), Some (ListConstructor l)) ] /\
                        ret = SCA _ (natToWord _ (length l))
      |}; crush_types.
  Defined.
End TupleListADTSpec.

Module WTupleListADTSpecParams : TupleListADTSpecParams.
  Definition FieldType := W.
  Definition TupleConstructor := Tuple.
  Definition ListConstructor := TupleList.
End WTupleListADTSpecParams.

Module WTupleListSpec := TupleListADTSpec (WTupleListADTSpecParams).

Module WSTupleListADTSpecParams : TupleListADTSpecParams.
  Definition FieldType := sum W string.
  Definition TupleConstructor := WSTuple.
  Definition ListConstructor := WSTupleList.
End WSTupleListADTSpecParams.

Module WSTupleListSpec := TupleListADTSpec (WSTupleListADTSpecParams).

Print Module WTupleListSpec.
Print Module WSTupleListSpec.

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

Module Type IndexedBag1ADTSpecParams.
  Parameter KeyType : Type.
  Parameter FieldType : Type.
  Parameter DefaultField : FieldType.
  Parameter KeyConstructor : forall (k: KeyType), Value ADTValue.
  Parameter KeyConstructor_SameTypes : forall x y, is_same_type (KeyConstructor x) (KeyConstructor y) = true.
  Parameter MatchingFunction : forall (f: FieldType) (k: KeyType), Prop.
  Parameter TupleConstructor : forall (t: GenericTuple FieldType), ADTValue.
  Parameter TupleListConstructor : forall (ls: list (GenericTuple FieldType)), ADTValue.
  Parameter BagConstructor : forall (len keyIndex : W) (tuples : GenericTuples FieldType), ADTValue.
End IndexedBag1ADTSpecParams.

Module IndexedBag1ADTSpec (Params : IndexedBag1ADTSpecParams).
  Import Params.

  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists len key, args = [SCA _ len; SCA _ key]
                                               /\ len >= $2
                                               /\ key < len;
        PostCond := fun args ret => exists len key, args = [(SCA _ len, None); (SCA _ key, None)]
                                                    /\ ret = ADT (BagConstructor len key Empty)
      |}; crush_types.
  Defined.

  Definition Insert : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key ts t idx,
                       args = [ADT (BagConstructor len key ts); ADT (TupleConstructor t)]
                       /\ minFreshIndex ts idx
                       /\ length t = wordToNat len;
        PostCond := fun args ret =>
                      exists len key ts t idx,
                        args = [ (ADT (BagConstructor len key ts), Some (BagConstructor len key (insertAt ts idx t)));
                                 (ADT (TupleConstructor t), None) ]
                        /\ minFreshIndex ts idx
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Enumerate : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key ts,
                       args = [ADT (BagConstructor len key ts)]
                       /\ functional ts;
        PostCond := fun args ret =>
                      exists len key ts l,
                        args = [ (ADT (BagConstructor len key ts), Some (BagConstructor len key ts)) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence ts l
      |}; crush_types.
  Defined.

  Definition Find : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key ts k,
                       args = [ADT (BagConstructor len key ts); KeyConstructor k];
        PostCond := fun args ret =>
                      exists len keyIndex ts k l,
                        args = [ (ADT (BagConstructor len keyIndex ts), Some (BagConstructor len keyIndex ts));
                                 (KeyConstructor k, None) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence (keepEq MatchingFunction ts DefaultField keyIndex k) l
      |}; crush_types; compute; rewrite KeyConstructor_SameTypes; reflexivity.
  Defined.
End IndexedBag1ADTSpec.

Module WBag1ADTSpecParams : IndexedBag1ADTSpecParams.
  Definition KeyType := W.
  Definition FieldType := W.
  Definition DefaultField := wzero 32.
  Definition KeyConstructor := SCA ADTValue.
  Definition KeyConstructor_SameTypes := fun _ _ : KeyType => @eq_refl bool true.
  Definition MatchingFunction := @eq W.
  Definition TupleConstructor := Tuple.
  Definition TupleListConstructor := TupleList.
  Definition BagConstructor := Tuples1.
End WBag1ADTSpecParams.

Module Tuples1ADTSpec := IndexedBag1ADTSpec (WBag1ADTSpecParams).

Module WSBag1ADTSpecParams : IndexedBag1ADTSpecParams.
  Definition KeyType := W.
  Definition FieldType := sum W string.
  Definition DefaultField := @inl W string (wzero 32).
  Definition KeyConstructor := SCA ADTValue.
  Definition KeyConstructor_SameTypes := fun _ _ : KeyType => @eq_refl bool true.
  Definition MatchingFunction := fun (field: FieldType) key => match field with inl f => f = key | _ => False end.
  Definition TupleConstructor := WSTuple.
  Definition TupleListConstructor := WSTupleList.
  Definition BagConstructor := BagOfWSTuples1.
End WSBag1ADTSpecParams.

Module WSBag1ADTSpec := IndexedBag1ADTSpec (WSBag1ADTSpecParams).

Module WSTrieADTSpecParams : IndexedBag1ADTSpecParams.
  Definition KeyType := string.
  Definition FieldType := sum W string.
  Definition DefaultField := @inr W string "".
  Definition KeyConstructor := (fun x => ADT (ADTString x)).
  Definition KeyConstructor_SameTypes := fun _ _ : KeyType => @eq_refl bool true.
  Definition MatchingFunction := fun (field: FieldType) key => match field with inr f => f = key | _ => False end.
  Definition TupleConstructor := WSTuple.
  Definition TupleListConstructor := WSTupleList.
  Definition BagConstructor := WSTrie.
End WSTrieADTSpecParams.

Module WSTrieADTSpec := IndexedBag1ADTSpec (WSTrieADTSpecParams).

Print Module Tuples1ADTSpec.
Print Module WSBag1ADTSpec.
Print Module WSTrieADTSpec.

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
