Set Implicit Arguments.

Require Import Facade.
Require Import NotationsExpr.
Export NotationsExpr.

Require Import Memory IL.

Coercion natToW : nat >-> W.

Require Import AutoSep.

(* for free-standing stmt seq *)
Infix ";;" := Facade.Seq : facade_scope.

(* for stmt list *)
Notation " { } " := (Facade.Skip) (only parsing) : facade_scope.
Notation " { x ; .. ; y } " := (Facade.Seq x .. (Facade.Seq y Facade.Skip) ..) (only parsing) : facade_scope.

(* make sure we don't mess up with record syntax *)
Record test_record := { AAA : nat; BBB : nat ; CCC : nat}.

Delimit Scope facade_scope with facade.
Local Open Scope facade_scope.

Notation "'skip'" := Facade.Skip : facade_scope.

Notation if_ := Facade.If.

Notation while_ := Facade.While.

Notation "x <- e" := (Facade.Assign x e) : facade_scope.

Definition DirectCall x f args := Facade.Label "_f" f ;; Facade.Call x "_f" args.

Notation "'call_' f ()" := (DirectCall "_tmp" f nil)
  (no associativity, at level 95, f at level 0) : facade_scope.

Notation "'call_' f ( x1 , .. , xN )" := (DirectCall "_tmp" f (cons x1 (.. (cons xN nil) ..))) (no associativity, at level 95, f at level 0) : facade_scope.

Notation "x <-- 'call_' f ()" := (DirectCall x f nil)
  (no associativity, at level 95, f at level 0) : facade_scope.

Notation "x <-- 'call_' f ( x1 , .. , xN )" := (DirectCall x f (cons x1 (.. (cons xN nil) ..))) (no associativity, at level 95, f at level 0) : facade_scope.

Notation "a ! b" := (a, b) (only parsing) : facade_scope.

Local Open Scope expr_scope.

(* can mix { a ; b } and ( a ;; b ) *)
Definition test_stmt :=
  "x" <- 1;;
  "y" <- 2;;
  if_ ("x" < "y") {
    "x" <- "y";
    "y" <- "y" * 2
  }{
    skip
  };;
  while_ ("x" <> 0) (
    "y" <- "y" + 1 ;;
    "x" <- "x" - 1
  );;
  "ret" <-- call_ "m"!"f" ("x", "y").

Require Import List.
Import ListNotations.
Local Open Scope list_scope.
Require Import ListNotationsFix.
Export ListNotationsFix.
Require Import FModule.

Local Open Scope facade_scope.

Notation "'func' () b" :=
  (Build_FFunction (Build_OperationalSpec nil "ret" b eq_refl eq_refl eq_refl) eq_refl) (no associativity, at level 95, only parsing) : facade_scope.

Notation "'func' ( x , .. , y ) b" :=
  (Build_FFunction (Build_OperationalSpec (cons x (.. (cons y nil) ..)) "ret" b eq_refl eq_refl eq_refl) eq_refl) (no associativity, at level 95, only parsing) : facade_scope.

Definition test_f := 
  func(){
    "ret" <- 0
  }.

(* notations for pairs *)
Notation "'def' name = v" := (pair name v) (no associativity, at level 95, name at level 0, only parsing) : facade_scope.
Infix "==>" := pair (no associativity, at level 95, only parsing) : facade_scope.
Infix "::=" := pair (no associativity, at level 95, only parsing) : facade_scope.

(* notations for lists *)
Notation "{{ x 'with' .. 'with' y }}" := (cons x .. (cons y nil) ..) (only parsing) : facade_scope.
Notation " { } " := (@nil _) (only parsing) : list_scope.
Notation " { x ; .. ; y } " := (cons x .. (cons y nil) ..) (only parsing) : list_scope.

Definition test_name_f := 
  def "test" = func(){
    "ret" <- 0
  }.

Require Import StringMapFacts.
Require Import GLabelMapFacts.

Notation "'module' 'import' imps 'define' fs" := 
  (Build_FModule (GLabelMapFacts.of_list imps) (StringMapFacts.of_list fs)) (no associativity, at level 95, only parsing) : facade_scope.

Section Test.
  
  Variable ADTValue : Type.
  Variables ArraySeq_newSpec ListSet_deleteSpec : AxiomaticSpec ADTValue.

  Definition test_m := 
    module 
    import {
      "ADT"!"ArraySeq_new" ==> ArraySeq_newSpec;
      "ADT"!"ListSet_delete" ==> ListSet_deleteSpec
    }
    define {
      def "f1" = func(){
        "ret" <- 0
      };
      def "f2" = func("a", "b"){
        "x" <- 2;
        "y" <- "b";
        if_ ("x" < "y") {
          "x" <- "y";
          "y" <- "y" * 2
        }{
          skip
        };
        while_ ("x" <> 0) {
          "y" <- "y" + 1 ;;
          "x" <- "x" - 1
        };
        "ret" <-- call_ "m"!"f" ("x", "y")
      };
      def "f3" = test_f;
      test_name_f;
      "f5" ::= func(){
        test_stmt
      }
    }.

  Definition test_ms := {
    def "m1" = test_m;
    def "m2" = test_m
  }%list.

End Test.