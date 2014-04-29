Set Implicit Arguments.

Require Import String.

Inductive ADTScheme :=
| Primitive : string -> ADTScheme
| Product : ADTScheme -> ADTScheme -> ADTScheme.

Require Import StringMap.
Import StringMap.

Definition ADT_Table := t Type.

Section TableSection.

  Variable adt_table : ADT_Table.

  Fixpoint interp_adt (ty : ADTScheme) : Type :=
    match ty with
      | Primitive name => 
        match find name adt_table with
          | Some type => type
          | None => Empty_set
        end
      | Product a b => (interp_adt a * interp_adt b)%type
    end.

  Record ADTValue :=
    {
      Ty : ADTScheme;
      Value : interp_adt Ty
    }.

End TableSection.

Module Type ADTTable.

  Parameter adt_table : ADT_Table.

End ADTTable.

Require Import ADT.

Module TabledADT (Import T : ADTTable) <: ADT.

  Definition ADTValue := ADTValue adt_table.

End TabledADT.
