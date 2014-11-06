Require Import Facade.
Require Import Memory.

Inductive FacadeADT :=
  | List : list W -> FacadeADT
  | Junk : False -> FacadeADT.

Require Import List Program.

Definition SCAZero {t} := SCA t (Word.natToWord 32 0).
Definition SCAOne  {t} := SCA t (Word.natToWord 32 1).

Ltac crush_types :=
  unfold type_conforming, same_types, same_type; intros; 
  repeat match goal with
           | [ H: exists t, _ |- _ ] => destruct H
         end; subst;
  intuition.

Definition List_new : AxiomaticSpec FacadeADT.
  refine {|
      PreCond := fun args => args = [];
      PostCond := fun args ret => args = [] /\ ret = ADT (List [])
    |}; crush_types.
Defined.

Definition List_delete : AxiomaticSpec FacadeADT.
  refine {|
      PreCond := fun args => exists l, args = [ADT (List l)];
      PostCond := fun args ret => exists l, args = [(ADT (List l), None)] /\ ret = SCAZero
    |}; crush_types.
Defined.

Definition List_pop : AxiomaticSpec FacadeADT.
  refine {|
      PreCond := fun args => 
                   exists h t, 
                     args = [ADT (List (h :: t))];
      PostCond := fun args ret => 
                    exists h t, 
                      args = [ (ADT (List (h :: t)), Some (List t)) ] /\ 
                      ret = SCA FacadeADT h
    |}; crush_types.
Defined.

Definition List_empty : AxiomaticSpec FacadeADT. 
  refine {|
      PreCond := fun args => 
                   exists l, 
                     args = [ADT (List l)];
      PostCond := fun args ret => 
                    exists l, 
                    args = [(ADT (List l), Some (List l))] /\ 
                    ((ret = SCAZero /\ l <> nil) \/ (ret = SCAOne /\ l = nil))
    |}; crush_types.
Defined.

Definition List_push : AxiomaticSpec FacadeADT.
  refine {|
      PreCond := fun args => 
                   exists l w, 
                     args = [ADT (List l); SCA _ w];
      PostCond := fun args ret => 
                    exists l w, 
                      args = [ (ADT (List l), Some (List (w :: l))); (SCA _ w, None) ] /\ 
                      ret = SCAZero
    |}; crush_types.
Defined.

Definition List_copy : AxiomaticSpec FacadeADT.
  refine {|
      PreCond := fun args => 
                   exists l, 
                     args = [ADT (List l)];
      PostCond := fun args ret => 
                    exists l, 
                      args = [ (ADT (List l), Some (List l)) ] /\ 
                      ret = ADT (List l)
    |}; crush_types.
Defined.

