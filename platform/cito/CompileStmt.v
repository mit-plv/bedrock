Set Implicit Arguments.

Require Import ADT.
Require Import RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import PostOk.
  Module Import PostOkMake := Make E M.
  Require Import VerifCondOk.
  Module Import VerifCondOkMake := Make E M.
  Import CompileStmtSpecMake.
  Import InvMake.
  Import Semantics.
  Import SemanticsMake.
  Import InvMake2.

  Section TopSection.

    Require Import AutoSep.

    Variable vars : list string.

    Variable temp_size : nat.

    Variable imports : LabelMap.t assert.

    Variable imports_global : importsGlobal imports.

    Variable modName : string.

    Require Import Syntax.

    Variable rv_postcond : W -> vals -> Prop.

    Notation do_compile := (CompileStmtImplMake.compile vars temp_size rv_postcond imports_global modName).

    Variable s k : Stmt.

    Require Import Wrap.
    Definition compile : cmd imports modName.
      refine (
          Wrap imports imports_global modName 
               (do_compile s k) 
               (fun _ => postcond vars temp_size k rv_postcond) 
               (verifCond vars temp_size s k rv_postcond) 
               _ _).
      eapply post_ok.
      eapply verifCond_ok.
    Defined.

  End TopSection.

End Make.