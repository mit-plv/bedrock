Require Import Bedrock.Platform.Facade.Facade.
Require Import Bedrock.Memory.
Require Import Coq.Sets.Ensembles.

Require Import Bedrock.Bedrock.

Require Import Bedrock.Platform.Facade.examples.TuplesF.

Notation byte := (Word.word 8).
Notation byteString := (list byte).

Inductive WS :=
| WSWord (w: W)
| WSBytes (capacity: W) (s: byteString).

Definition WSTupl := GenericTuple WS.
Definition WSTuplSet := GenericTuples WS.

Inductive ADTValue :=
| WTuple (t : tupl)
| WordList (ws : list W)
| WTupleList (ts : list tupl)
| WTuples0 (len : W) (ts : tuples)
| WTuples1 (len key : W) (ts : tuples)
| WTuples2 (len key1 key2 : W) (ts : tuples)
| WSTuple (t : WSTupl)
| WSTupleList (ts : list WSTupl)
| Bytes (capacity: W) (bs: byteString)
| WSTrie (len keyIndex : W) (tuples : WSTuplSet)
| BagOfWSTuples1 (len keyIndex : W) (tuples : WSTuplSet)
| NestedWSTrieBagOfWSTuples1 (len keyIndex1 keyIndex2 : W) (tuples : WSTuplSet).

Require Import Bedrock.Platform.Cito.ADT.

Module Adt <: ADT.
  Definition ADTValue := ADTValue.
End Adt.

Require Import Coq.Lists.List Coq.Program.Program.

Definition SCAZero {t} := SCA t (Word.natToWord 32 0).
Definition SCAOne  {t} := SCA t (Word.natToWord 32 1).

Create HintDb crush_types_db.

Ltac crush_types :=
  unfold type_conforming, same_types, same_type; intros;
  repeat match goal with
         | [ H: exists t, _ |- _ ] => destruct H
         end;
  repeat progress (subst; intuition);
  try (compute; autorewrite with crush_types_db; reflexivity).

Module Type TupleADTSpecParams.
  Parameter FieldType : Type.
  Parameter ValueConstructor : forall (t: option FieldType), Value ADTValue.
  Parameter TupleConstructor : forall (t: GenericTuple FieldType), ADTValue.
End TupleADTSpecParams.

Module TupleADTSpec (Params: TupleADTSpecParams).
  Export Params.

  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists len, args = [SCA _ len]
                                           /\ len >= $2;
        PostCond := fun args ret => exists len ls, args = [(SCA _ len, None)]
                                                   /\ ret = ADT (TupleConstructor ls)
                                                   /\ length ls = wordToNat len
      |}; crush_types.
  Defined.

  Definition Delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists ls len, args = [ADT (TupleConstructor ls); SCA _ len]
                                              /\ length ls = wordToNat len;
        PostCond := fun args ret => exists ls len, args = [(ADT (TupleConstructor ls), None); (SCA _ len, None)]
                                                   /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Copy : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists ls len,
                       args = [ADT (TupleConstructor ls); SCA _ len]
                       /\ length ls = wordToNat len
                       /\ natToW (length ls) >= $2;
        PostCond := fun args ret => exists ls len,
                        args = [(ADT (TupleConstructor ls), Some (TupleConstructor ls)); (SCA _ len, None)]
                        /\ ret = ADT (TupleConstructor ls)
      |}; crush_types.
  Defined.

  Definition Get : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists ls pos,
                       args = [ADT (TupleConstructor ls); SCA _ pos]
                       /\ pos < natToW (length ls);
        PostCond := fun args ret =>
                      exists ls pos,
                        args = [(ADT (TupleConstructor ls), Some (TupleConstructor ls)); (SCA _ pos, None)]
                        /\ ret = ValueConstructor (List.nth_error ls (Word.wordToNat pos))
      |}; crush_types.
  Defined.
End TupleADTSpec.

Module WTupleADTSpecParams <: TupleADTSpecParams.
  Definition FieldType := W.
  Definition TupleConstructor := WTuple.
  Definition ListConstructor := WTupleList.
  Definition ValueConstructor (x: option FieldType) :=
    SCA ADTValue (match x with
                  | Some w => w
                  | _ => wzero _
                  end).
End WTupleADTSpecParams.

Module WTupleADTSpec.
  Include (TupleADTSpec WTupleADTSpecParams).

  Definition Put : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists ls pos val,
                       args = [ADT (TupleConstructor ls); SCA _ pos; SCA _ val]
                       /\ pos < natToW (length ls);
        PostCond := fun args ret =>
                      exists ls pos val,
                        args = [(ADT (TupleConstructor ls), Some (TupleConstructor (Array.upd ls pos val)));
                                (SCA _ pos, None); (SCA _ val, None)]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.
End WTupleADTSpec.

Module WSTupleADTSpecParams <: TupleADTSpecParams.
  Definition FieldType := WS.
  Definition TupleConstructor := WSTuple.
  Definition ListConstructor := WSTupleList.
  Definition ValueConstructor (x: option FieldType) :=
    match x with
    | Some (WSWord w) => SCA ADTValue w
    | Some (WSBytes c s) => ADT (Bytes c s)
    | _ => SCA ADTValue (wzero _)
    end.
End WSTupleADTSpecParams.

Fixpoint PutAt {A} seq offset (val: A) :=
  match seq, offset with
  | nil, _ => nil
  | _ :: t, 0 => val :: t
  | h :: t, S offset' => h :: (PutAt t offset' val)
  end.

Module WSTupleADTSpec.
  Include (TupleADTSpec WSTupleADTSpecParams).

  Definition PutW : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists ls pos val,
                       args = [ADT (TupleConstructor ls); SCA _ pos; SCA _ val]
                       /\ pos < natToW (length ls);
        PostCond := fun args ret =>
                      exists ls pos val,
                        args = [(ADT (TupleConstructor ls),
                                 Some (TupleConstructor (PutAt ls pos (WSWord val))));
                                (SCA _ pos, None); (SCA _ val, None)]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition PutString : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists ls pos capacity string,
                       args = [ADT (TupleConstructor ls); SCA _ pos; ADT (Bytes capacity string)]
                       /\ pos < natToW (length ls);
        PostCond := fun args ret =>
                      exists ls pos capacity string,
                        args = [(ADT (TupleConstructor ls),
                                 Some (TupleConstructor (PutAt ls pos (WSBytes capacity string))));
                                (SCA _ pos, None); (ADT (Bytes capacity string), None)]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.
End WSTupleADTSpec.

Module WordListADTSpec.
  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => args = [];
        PostCond := fun args ret => args = [] /\ ret = ADT (WordList [])
      |}; crush_types.
  Defined.

  Definition Delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists l, args = [ADT (WordList l)];
        PostCond := fun args ret => exists l, args = [(ADT (WordList l), None)] /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Pop : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists h t,
                       args = [ADT (WordList (h :: t))];
        PostCond := fun args ret =>
                      exists h t,
                        args = [ (ADT (WordList (h :: t)), Some (WordList t)) ]
                        /\ ret = SCA ADTValue h
      |}; crush_types.
  Defined.

  Definition Empty : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (WordList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [(ADT (WordList l), Some (WordList l))]
                        /\ exists w, ret = SCA _ w /\ Bedrock.Programming.propToWord (l = nil) w
      |}; crush_types.
  Defined.

  Definition Push : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l w,
                       args = [ADT (WordList l); SCA _ w];
        PostCond := fun args ret =>
                      exists l w,
                        args = [ (ADT (WordList l), Some (WordList (w :: l))); (SCA _ w, None) ]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Copy : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (WordList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (WordList l), Some (WordList l)) ]
                        /\ ret = ADT (WordList l)
      |}; crush_types.
  Defined.

  Definition Rev : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (WordList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (WordList l), Some (WordList (rev l))) ]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Length : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (WordList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (WordList l), Some (WordList l)) ]
                        /\ ret = SCA _ (Word.natToWord _ (length l))
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
                        args = [ (ADT (ListConstructor l),
                                  Some (ListConstructor l)); (SCA _ len, None) ]
                        /\ ret = ADT (ListConstructor l)
      |}; crush_types.
  Defined.

  Definition Pop : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists h t,
                       args = [ADT (ListConstructor (h :: t))];
        PostCond := fun args ret =>
                      exists h t,
                        args = [ (ADT (ListConstructor (h :: t)), Some (ListConstructor t)) ]
                        /\ ret = ADT (TupleConstructor h)
      |}; crush_types.
  Defined.

  Definition Empty : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (ListConstructor l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [(ADT (ListConstructor l), Some (ListConstructor l))]
                        /\ exists w, ret = SCA _ w /\ propToWord (l = nil) w
      |}; crush_types.
  Defined.

  Definition Push : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l t,
                       args = [ADT (ListConstructor l); ADT (TupleConstructor t)];
        PostCond := fun args ret =>
                      exists l t,
                        args = [ (ADT (ListConstructor l), Some (ListConstructor (t :: l)));
                                 (ADT (TupleConstructor t), None) ]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Rev : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (ListConstructor l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (ListConstructor l), Some (ListConstructor (rev l))) ]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Length : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (ListConstructor l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (ListConstructor l), Some (ListConstructor l)) ]
                        /\ ret = SCA _ (natToWord _ (length l))
      |}; crush_types.
  Defined.
End TupleListADTSpec.

Module WTupleListADTSpecParams <: TupleListADTSpecParams.
  Definition FieldType := W.
  Definition TupleConstructor := WTuple.
  Definition ListConstructor := WTupleList.
End WTupleListADTSpecParams.

Module WTupleListSpec := TupleListADTSpec (WTupleListADTSpecParams).

Module WSTupleListADTSpecParams <: TupleListADTSpecParams.
  Definition FieldType := WS.
  Definition TupleConstructor := WSTuple.
  Definition ListConstructor := WSTupleList.
End WSTupleListADTSpecParams.

Module WSTupleListSpec := TupleListADTSpec (WSTupleListADTSpecParams).

Print Module WTupleListSpec.
Print Module WSTupleListSpec.

Module Type IndexedBag0ADTSpecParams.
  Parameter FieldType : Type.
  Parameter TupleConstructor : forall (t: GenericTuple FieldType), ADTValue.
  Parameter TupleListConstructor : forall (ls: list (GenericTuple FieldType)), ADTValue.
  Parameter TreeConstructor : forall (len: W) (elems: GenericTuples FieldType), ADTValue.
End IndexedBag0ADTSpecParams.

Module IndexedBag0ADTSpec (Params : IndexedBag0ADTSpecParams).
  Import Params.

  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists len, args = [SCA _ len]
                                           /\ len >= $2;
        PostCond := fun args ret => exists len, args = [(SCA _ len, None)]
                                                /\ ret = ADT (TreeConstructor len Empty)
      |}; crush_types.
  Defined.

  Definition Insert : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len ts t idx,
                       args = [ADT (TreeConstructor len ts); ADT (TupleConstructor t)]
                       /\ minFreshIndex ts idx
                       /\ length t = wordToNat len;
        PostCond := fun args ret =>
                      exists len ts t idx,
                        args = [ (ADT (TreeConstructor len ts),
                                  Some (TreeConstructor len (insertAt ts idx t)));
                                 (ADT (TupleConstructor t), None) ]
                        /\ minFreshIndex ts idx
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Enumerate : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len ts,
                       args = [ADT (TreeConstructor len ts)];
        PostCond := fun args ret =>
                      exists len ts l,
                        args = [ (ADT (TreeConstructor len ts), Some (TreeConstructor len ts)) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence ts l
      |}; crush_types.
  Defined.
End IndexedBag0ADTSpec.

Module Tuples0ADTSpecParams <: IndexedBag0ADTSpecParams.
  Definition FieldType := W.
  Definition TupleConstructor := WTuple.
  Definition TupleListConstructor := WTupleList.
  Definition TreeConstructor := WTuples0.
End Tuples0ADTSpecParams.

Module Tuples0ADTSpec := IndexedBag0ADTSpec Tuples0ADTSpecParams.
Print Module Tuples0ADTSpec.

Module Type IndexedBag1ADTSpecParams.
  Parameter KeyType : Type.
  Parameter FieldType : Type.
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
                        args = [ (ADT (BagConstructor len key ts),
                                  Some (BagConstructor len key (insertAt ts idx t)));
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

  Hint Rewrite KeyConstructor_SameTypes : crush_types_db.
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
                        /\ EnsembleIndexedListEquivalence (keepEq MatchingFunction ts keyIndex k) l
      |}; crush_types.
  Defined.
End IndexedBag1ADTSpec.

Module WBag1ADTSpecParams <: IndexedBag1ADTSpecParams.
  Definition KeyType := W.
  Definition FieldType := W.
  Definition KeyConstructor := SCA ADTValue.
  Definition KeyConstructor_SameTypes := fun _ _ : KeyType => @eq_refl bool true.
  Definition MatchingFunction := @eq W.
  Definition TupleConstructor := WTuple.
  Definition TupleListConstructor := WTupleList.
  Definition BagConstructor := WTuples1.
End WBag1ADTSpecParams.

Module Tuples1ADTSpec := TupleADTSpec WSTupleADTSpecParams.

Definition ByteToAscii (w8: byte) : Ascii.ascii :=
  match w8 with
  | Word.WO => Ascii.zero
  | Word.WS b7 _ w7 =>
    match w7 with
    | Word.WO => Ascii.zero
    | Word.WS b6 _ w6 =>
      match w6 with
      | Word.WO => Ascii.zero
      | Word.WS b5 _ w5 =>
        match w5 with
        | Word.WO => Ascii.zero
        | Word.WS b4 _ w4 =>
          match w4 with
          | Word.WO => Ascii.zero
          | Word.WS b3 _ w3 =>
            match w3 with
            | Word.WO => Ascii.zero
            | Word.WS b2 _ w2 =>
              match w2 with
              | Word.WO => Ascii.zero
              | Word.WS b1 _ w1 =>
                match w1 with
                | Word.WO => Ascii.zero
                | Word.WS b0 _ w0 =>
                  Ascii.Ascii b7 b6 b5 b4 b3 b2 b1 b0
                end
              end
            end
          end
        end
      end
    end
  end.

Lemma ByteToAscii_correct_wrt_nat :
  forall n: nat, (n <= 255)%nat -> Ascii.nat_of_ascii (ByteToAscii (Word.natToWord 8 n)) = n.
Proof.
  intros; repeat (destruct n; [ reflexivity | ]).
  apply (Minus.minus_le_compat_r _ _ 255) in H; inversion H.
Qed.

Fixpoint BytesToString bytes :=
  match bytes with
  | nil => ""%string
  | cons a bb => String (ByteToAscii a) (BytesToString bb)
  end.

Definition WS_StringPrefixB ws key :=
  match ws with
  | WSBytes c s => prefix (BytesToString key) (BytesToString s)
  | _ => false
  end.

Definition WS_WordEqB ws key :=
  match ws with
  | WSWord w => Word.weqb w key
  | _ => false
  end.

Module WSBag1ADTSpecParams <: IndexedBag1ADTSpecParams.
  Definition KeyType := W.
  Definition FieldType := WS.
  Definition KeyConstructor := SCA ADTValue.
  Definition KeyConstructor_SameTypes := fun _ _ : KeyType => @eq_refl bool true.
  Definition MatchingFunction ws key := WS_WordEqB ws key = true.
  Definition TupleConstructor := WSTuple.
  Definition TupleListConstructor := WSTupleList.
  Definition BagConstructor := BagOfWSTuples1.
End WSBag1ADTSpecParams.

Module WSBag1ADTSpec := IndexedBag1ADTSpec (WSBag1ADTSpecParams).

Module WSTrieADTSpecParams <: IndexedBag1ADTSpecParams.
  Definition KeyType := (nat * byteString)%type.
  Definition FieldType := WS.
  Definition KeyConstructor := (fun cbs: KeyType => ADT (let (c, bs) := cbs in Bytes c bs)).
  Definition KeyConstructor_SameTypes := fun _ _ : KeyType => @eq_refl bool true.
  Definition MatchingFunction ws (key: KeyType) := WS_StringPrefixB ws (snd key) = true.
  Definition TupleConstructor := WSTuple.
  Definition TupleListConstructor := WSTupleList.
  Definition BagConstructor := WSTrie.
End WSTrieADTSpecParams.

Module WSTrieADTSpec := IndexedBag1ADTSpec (WSTrieADTSpecParams).

Print Module Tuples1ADTSpec.
Print Module WSBag1ADTSpec.
Print Module WSTrieADTSpec.

Module Type IndexedBag2ADTSpecParams.
  Parameter KeyType1 KeyType2 : Type.
  Parameter FieldType : Type.
  Parameter KeyConstructor1 : forall (k: KeyType1), Value ADTValue.
  Parameter KeyConstructor2 : forall (k: KeyType2), Value ADTValue.
  Parameter KeyConstructor1_SameTypes : forall x y, is_same_type (KeyConstructor1 x) (KeyConstructor1 y) = true.
  Parameter KeyConstructor2_SameTypes : forall x y, is_same_type (KeyConstructor2 x) (KeyConstructor2 y) = true.
  Parameter MatchingFunction1 : forall (f: FieldType) (k: KeyType1), Prop.
  Parameter MatchingFunction2 : forall (f: FieldType) (k: KeyType2), Prop.
  Parameter TupleConstructor : forall (t: GenericTuple FieldType), ADTValue.
  Parameter TupleListConstructor : forall (ls: list (GenericTuple FieldType)), ADTValue.
  Parameter BagConstructor : forall (len keyIndex1 keyIndex2 : W) (tuples : GenericTuples FieldType), ADTValue.
End IndexedBag2ADTSpecParams.

Module IndexedBag2ADTSpec (Params: IndexedBag2ADTSpecParams).
  Import Params.

  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists len keyIndex1 keyIndex2,
                       args = [SCA _ len; SCA _ keyIndex1; SCA _ keyIndex2]
                       /\ len >= $2
                       /\ keyIndex1 < len
                       /\ keyIndex2 < len;
        PostCond := fun args ret => exists len keyIndex1 keyIndex2,
                        args = [(SCA _ len, None); (SCA _ keyIndex1, None); (SCA _ keyIndex2, None)]
                        /\ ret = ADT (BagConstructor len keyIndex1 keyIndex2 Empty)
      |}; crush_types.
  Defined.

  Definition Insert : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len keyIndex1 keyIndex2 ts t idx,
                       args = [ADT (BagConstructor len keyIndex1 keyIndex2 ts); ADT (TupleConstructor t)]
                       /\ minFreshIndex ts idx
                       /\ length t = wordToNat len;
        PostCond := fun args ret =>
                      exists len keyIndex1 keyIndex2 ts t idx,
                        args = [ (ADT (BagConstructor len keyIndex1 keyIndex2 ts),
                                  Some (BagConstructor len keyIndex1 keyIndex2 (insertAt ts idx t)));
                                 (ADT (TupleConstructor t), None) ]
                        /\ minFreshIndex ts idx
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Enumerate : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len keyIndex1 keyIndex2 ts,
                       args = [ADT (BagConstructor len keyIndex1 keyIndex2 ts)]
                       /\ functional ts;
        PostCond := fun args ret =>
                      exists len keyIndex1 keyIndex2 ts l,
                        args = [ (ADT (BagConstructor len keyIndex1 keyIndex2 ts),
                                  Some (BagConstructor len keyIndex1 keyIndex2 ts)) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence ts l
      |}; crush_types.
  Defined.

  Hint Rewrite KeyConstructor1_SameTypes : crush_types_db.
  Hint Rewrite KeyConstructor2_SameTypes : crush_types_db.

  Definition FindBoth : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len keyIndex1 keyIndex2 ts k1 k2,
                       args = [ADT (BagConstructor len keyIndex1 keyIndex2 ts);
                               KeyConstructor1 k1; KeyConstructor2 k2];
        PostCond := fun args ret =>
                      exists len keyIndex1 keyIndex2 ts k1 k2 l,
                        args = [ (ADT (BagConstructor len keyIndex1 keyIndex2 ts),
                                  Some (BagConstructor len keyIndex1 keyIndex2 ts));
                                 (KeyConstructor1 k1, None); (KeyConstructor2 k2, None) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence
                             (keepEq MatchingFunction2 (keepEq MatchingFunction1 ts keyIndex1 k1) keyIndex2 k2)
                             l
      |}; crush_types.
  Defined.

  Definition FindFirst : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len keyIndex1 keyIndex2 ts k,
                       args = [ADT (BagConstructor len keyIndex1 keyIndex2 ts); KeyConstructor1 k]
                       /\ functional ts;
        PostCond := fun args ret =>
                      exists len keyIndex1 keyIndex2 ts k l,
                        args = [ (ADT (BagConstructor len keyIndex1 keyIndex2 ts),
                                  Some (BagConstructor len keyIndex1 keyIndex2 ts));
                                 (KeyConstructor1 k, None) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence (keepEq MatchingFunction1 ts keyIndex1 k) l
      |}; crush_types.
  Defined.

  Definition FindSecond : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len keyIndex1 keyIndex2 ts k,
                       args = [ADT (BagConstructor len keyIndex1 keyIndex2 ts); KeyConstructor2 k]
                       /\ functional ts;
        PostCond := fun args ret =>
                      exists len key1 keyIndex2 ts k l,
                        args = [ (ADT (BagConstructor len key1 keyIndex2 ts),
                                  Some (BagConstructor len key1 keyIndex2 ts));
                                 (KeyConstructor2 k, None) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence (keepEq MatchingFunction2 ts keyIndex2 k) l
      |}; crush_types.
  Defined.
End IndexedBag2ADTSpec.

Check prefix.

Module WBag2ADTSpecParams <: IndexedBag2ADTSpecParams.
  Definition KeyType1 := W.
  Definition KeyType2 := W.
  Definition FieldType := W.
  Definition KeyConstructor1 := SCA ADTValue.
  Definition KeyConstructor2 := SCA ADTValue.
  Definition KeyConstructor1_SameTypes := fun _ _ : KeyType1 => @eq_refl bool true.
  Definition KeyConstructor2_SameTypes := fun _ _ : KeyType2 => @eq_refl bool true.
  Definition MatchingFunction1 := @eq KeyType1.
  Definition MatchingFunction2 := @eq KeyType2.
  Definition TupleConstructor := WTuple.
  Definition TupleListConstructor := WTupleList.
  Definition BagConstructor := WTuples2.
End WBag2ADTSpecParams.

Module Tuples2ADTSpec := IndexedBag2ADTSpec WBag2ADTSpecParams.
Print Module Tuples2ADTSpec.

Module WSTrieWBagADTSpecParams <: IndexedBag2ADTSpecParams.
  Definition KeyType1 := (nat * byteString)%type.
  Definition KeyType2 := W.
  Definition FieldType := WS.
  Definition KeyConstructor1 := (fun (cbs: KeyType1) => ADT (let (c, bs) := cbs in Bytes c bs)).
  Definition KeyConstructor2 := SCA ADTValue.
  Definition KeyConstructor1_SameTypes := fun _ _ : KeyType1 => @eq_refl bool true.
  Definition KeyConstructor2_SameTypes := fun _ _ : KeyType2 => @eq_refl bool true.
  Definition MatchingFunction1 ws (key: KeyType1) := WS_StringPrefixB ws (snd key) = true.
  Definition MatchingFunction2 ws key := WS_WordEqB ws key = true.
  Definition TupleConstructor := WSTuple.
  Definition TupleListConstructor := WSTupleList.
  Definition BagConstructor := NestedWSTrieBagOfWSTuples1.
End WSTrieWBagADTSpecParams.

Module WSTrieWBagADTSpec := IndexedBag2ADTSpec WSTrieWBagADTSpecParams.
Print Module WSTrieWBagADTSpec.

Definition ByteToWord (b: byte) : W :=
  (* FIXME are these zero bits on the correct side? *)
  b~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.

Module BytesADTSpec.
  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists capacity, args = [SCA _ capacity];
        PostCond := fun args ret => exists capacity, args = [(SCA _ capacity, None)]
                                                     /\ ret = ADT (Bytes capacity nil)
      |}; crush_types.
  Defined.

  Definition Delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists capacity bytes,
                       (length bytes < wordToNat capacity)%nat
                       /\ args = [ADT (Bytes capacity bytes)];
        PostCond := fun args ret => exists capacity bytes,
                        args = [(ADT (Bytes capacity bytes), None)]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Push : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists capacity bytes byte,
                       (S (length bytes) < wordToNat capacity)%nat
                       /\ args = [ADT (Bytes capacity bytes); SCA _ (ByteToWord byte)];
        PostCond := fun args ret =>
                      exists capacity bytes byte,
                        args = [(ADT (Bytes capacity bytes), Some (Bytes capacity (bytes ++ [byte])));
                                (SCA _ (ByteToWord byte), None)]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Put : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists capacity bytes index byte,
                       ((length bytes) < wordToNat capacity)%nat
                       /\ (wordToNat index < (length bytes))%nat
                       /\ args = [ADT (Bytes capacity bytes); SCA _ index; SCA _ (ByteToWord byte)];
        PostCond := fun args ret =>
                      exists capacity bytes index byte,
                        args = [(ADT (Bytes capacity bytes),
                                 Some (Bytes capacity (PutAt bytes (wordToNat index) byte)));
                                (SCA _ index, None); (SCA _ (ByteToWord byte), None)]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Get : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists capacity bytes index,
                       ((length bytes) < wordToNat capacity)%nat
                       /\ (wordToNat index < (length bytes))%nat
                       /\ args = [ADT (Bytes capacity bytes); SCA _ index];
        PostCond := fun args ret =>
                      exists capacity bytes index,
                        args = [(ADT (Bytes capacity bytes), Some (Bytes capacity bytes));
                                (SCA _ index, None)]
                        /\ ret = SCA _ (ByteToWord (nth (wordToNat index) bytes (wzero _)))
      |}; crush_types.
  Defined.
End BytesADTSpec.

