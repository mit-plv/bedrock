Definition heap := nat -> option nat.
Definition sprop : Type := heap -> Prop.

Parameter star : sprop -> sprop -> sprop.
Definition semp : sprop := 
  fun h => forall x, h x = None.