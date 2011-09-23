
Module Type SepLog.
  
  Parameter addr : Type.
  Parameter byte : Type.

  Parameter Mem : addr -> byte.
End SepLog.

Module Make (M : SepLog).
  Import M.

  Definition smem := addr -> option byte.

  Definition hprop : Type := smem -> Prop.

  Definition disjoint (m1 m2 : smem) : Prop :=
    forall x, m1 x = None \/ m2 x = None.

  Definition join (m1 m2 : smem) : smem :=
    fun x => match m1 x with
               | None => m2 x
               | v => v
             end.

  Definition split (m ml mr : smem) : Prop :=
    disjoint ml mr /\
    forall a, m a = join ml mr a.

  Definition semp : hprop := 
    fun h => forall x, h x = None.

  Definition ex (T : Type) (p : T -> hprop) : hprop :=
    fun v => exists x, p x v.

  Definition ptsTo (a : addr) (b : byte) : hprop :=
    fun h => forall x, (a = x -> h a = Some b)
                    /\ (a <> x -> h a = None).

  (** separation logic theory **)
End Make.

  