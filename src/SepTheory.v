Require Import List.
Require Import PropX.

Module Type SepLog.
  
  Parameter addr : Type.
  Parameter byte : Type.

  Parameter addr_dec : forall a b : addr, {a = b} + {a <> b}.

End SepLog.

Module Make (M : SepLog).
  Import M.

  Definition smem := list (addr * byte).

  Definition hprop : Type := smem -> Prop.

  Fixpoint smem_lookup (p : addr) (m : smem) : option byte :=
    match m with
      | nil => None
      | a :: b => if addr_dec (fst a) p then Some (snd a) else smem_lookup p b
    end.

  Fixpoint disjoint (m1 m2 : smem) : Prop :=
    match m1 with
      | nil => True
      | a :: b => smem_lookup (fst a) m2 = None /\ disjoint b m2
    end.

  Definition join (m1 m2 : smem) : smem := m1 ++ m2.

  Definition split (m ml mr : smem) : Prop :=
    disjoint ml mr /\
    forall a, smem_lookup a m = smem_lookup a (join ml mr).

  Definition semp : hprop := 
    fun h => h = nil.

  Definition ptsTo (a : addr) (b : byte) : hprop :=
    fun h => h = (a,b) :: nil.

  Definition ex (T : Type) (p : T -> hprop) : hprop :=
    fun v => exists x, p x v.


  (** separation logic theory **)
  (** I need to denote this in terms of PropX **)
End Make.

  