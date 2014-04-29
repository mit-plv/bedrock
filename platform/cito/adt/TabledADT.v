Set Implicit Arguments.

Require Import ADT.

Require Import String.

Inductive ADTScheme :=
| Primitive : string -> ADTScheme
| Product : ADTScheme -> ADTScheme -> ADTScheme.

Require Import StringMap.
Import StringMap.

Definition ADT_Table := t Type.

Section TableSection.

  Variable adt_table : ADT_Table.

  Fixpoint interp (ty : ADTScheme) : Type :=
    match ty with
      | Primitive name => 
        match find name adt_table with
          | Some type => type
          | None => Empty_set
        end
      | Product a b => (interp a * interp b)%type
    end.

  Record ADTValue :=
    {
      Ty : ADTScheme;
      Value : interp Ty
    }.

End TableSection.

Module Type ADTTable.

  Parameter adt_table : ADT_Table.

End ADTTable.

Module TabledADT (Import T : ADTTable) <: ADT.

  Definition ADTValue := ADTValue adt_table.

End TabledADT.
