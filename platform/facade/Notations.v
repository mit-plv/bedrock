Set Implicit Arguments.

Require Import Facade.
Require Import NotationsExpr.
Export NotationsExpr.

Local Open Scope expr_scope.

Require Import Memory IL.

Coercion natToW : nat >-> W.

Require Import AutoSep.

Infix ";;" := Seq : facade_scope.

Delimit Scope facade_scope with facade.
Local Open Scope facade_scope.

Infix ";;" := Facade.Seq : facade_scope.

Notation "'skip'" := Facade.Skip : facade_scope.

Notation "'If' cond { trueStmt } 'else' { falseStmt }" := (Facade.If cond%expr trueStmt falseStmt) : facade_scope.

Notation "'While' c { b }" := (Facade.While c%expr b) (no associativity, at level 95, c at level 0) : facade_scope.

Notation "x <- e" := (Facade.Assign x e%expr) : facade_scope.

Definition DirectCall x f args := Facade.Label "_f" f ;; Facade.Call x "_f" args.

Notation "'DCall' f ()" := (DirectCall "_tmp" f nil)
  (no associativity, at level 95, f at level 0) : facade_scope.

Notation "'DCall' f ( x1 , .. , xN )" := (DirectCall "_tmp" f (cons x1 (.. (cons xN nil) ..))%expr) (no associativity, at level 95, f at level 0) : facade_scope.

Notation "x <-- 'DCall' f ()" := (DirectCall x f nil)
  (no associativity, at level 95, f at level 0) : facade_scope.

Notation "x <-- 'DCall' f ( x1 , .. , xN )" := (DirectCall x f (cons x1 (.. (cons xN nil) ..))%expr) (no associativity, at level 95, f at level 0) : facade_scope.

Notation "a ! b" := (a, b) (only parsing) : facade_scope.

Definition test_stmt :=
  "x" <- 1 ;;
  "y" <- 2 ;;
  If ("x" < "y") {
    "x" <- "y" ;;
    "y" <- "y" * 2
  } 
  else {
    skip
  } ;;
  While ("x" <> 0) {
    "y" <- "y" + 1 ;;
    "x" <- "x" - 1
  } ;;
  "ret" <-- DCall "m"!"f" ("x", "y").

Require Import List.
Import ListNotations.
Local Open Scope list_scope.
Require Import ListNotationsFix.
Export ListNotationsFix.
Require Import FModule.

Notation "'ffunction' name () b 'end'" :=
  (name, Build_FFunction (Build_OperationalSpec nil "ret" b eq_refl eq_refl eq_refl) eq_refl) (no associativity, at level 95, name at level 0, only parsing) : facade_scope.

Notation "'ffunction' name ( x , .. , y ) b 'end'" :=
  (pair name (Build_FFunction (Build_OperationalSpec (cons x (.. (cons y nil) ..)) "ret" b eq_refl eq_refl eq_refl) eq_refl)) (no associativity, at level 95, name at level 0, only parsing) : facade_scope.

Definition test_f := 
  ffunction "return_zero"()
    "ret" <- 0
  end.

Notation "{{ x 'with' .. 'with' y }}" := (cons x .. (cons y nil) ..) (only parsing) : facade_scope.

Notation "name @ [ p ]" := (name, p) (only parsing) : facade_scope.

Require Import StringMapFacts.
Require Import GLabelMapFacts.

Notation "'fmodule' name 'import' imps 'define' fs" := 
  (pair name (Build_FModule (GLabelMapFacts.of_list imps) (StringMapFacts.of_list fs))) (no associativity, at level 95, name at level 0, only parsing) : facade_scope.

Section Test.
  
  Variable ADTValue : Type.
  Variables ArraySeq_newSpec ListSet_deleteSpec : AxiomaticSpec ADTValue.

  Definition test_m := 
    fmodule "return_zero"
    import [[ 
      "ADT"!"ArraySeq_new" @ [ArraySeq_newSpec],
      "ADT"!"ListSet_delete" @ [ListSet_deleteSpec]
    ]]
    define {{
      ffunction "return_zero1"()
        "ret" <- 0
      end with
      ffunction "return_zero2"()
        "ret" <- 0
      end with
      test_f with
      ffunction "return_zero3"()
        test_stmt
      end
    }}.

End Test.