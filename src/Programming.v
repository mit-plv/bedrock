(* Final syntax for structured programming *)

Require Import NArith Bool String.

Require Import Word PropX PropXTac IL LabelMap XCAP Structured StructuredModule Linker.

Set Implicit Arguments.



(** * The type of context-independent structured program chunks *)

Inductive chunk :=
| StraightLine : list instr -> chunk
| Structured : list instr -> (forall im mn, importsGlobal im -> cmd im mn) -> chunk.

Definition toCmd (ch : chunk) im mn (H : importsGlobal im) : cmd im mn :=
  match ch with
    | StraightLine is => Straightline_ im mn is
    | Structured nil c => c im mn H
    | Structured is c => Seq_ H (Straightline_ im mn is) (c im mn H)
  end.

Definition Seq (ch1 ch2 : chunk) : chunk :=
  match ch1, ch2 with
    | StraightLine is1, StraightLine is2 => StraightLine (is1 ++ is2)
    | StraightLine is1, Structured is2 c => Structured (is1 ++ is2) c
    | Structured is1 c1, _ => Structured is1 (fun im mn H => Seq_ H (c1 im mn H) (toCmd ch2 mn H))
  end.

Definition Instr (i : instr) : chunk :=
  StraightLine (i :: nil).

Definition Diverge : chunk :=
  Structured nil (fun im mn _ => Diverge_ im mn).

Definition Fail : chunk :=
  Structured nil (fun im mn _ => Fail_ im mn).

Definition Skip : chunk :=
  Structured nil (fun im mn _ => Skip_ im mn).

Definition Use_ (lemma : settings -> state -> Prop) (pf : forall stn st, lemma stn st) : chunk :=
  Structured nil (fun im mn _ => Use_ im mn lemma pf).

Record condition := {
  COperand1 : rvalue;
  CTest : test;
  COperand2 : rvalue
}.

Definition If_ (c : condition) (Then Else : chunk) : chunk :=
  Structured nil (fun im mn H => If_ H (COperand1 c) (CTest c) (COperand2 c) (toCmd Then mn H) (toCmd Else mn H)).

Definition While_ (inv : assert) (c : condition) (Body : chunk) : chunk :=
  Structured nil (fun im mn H => While_ H inv (COperand1 c) (CTest c) (COperand2 c) (toCmd Body mn H)).

Definition Goto (rv : rvalue) : chunk :=
  Structured nil (fun im mn H => match rv with
                                   | RvLabel f => Goto_ H mn f
                                   | _ => IGoto im mn rv
                                 end).

Definition Call_ (f : label) (afterCall : assert) : chunk :=
  Structured nil (fun im mn H => Call_ H mn f afterCall).


(** * Modules *)

Definition bmodule_ (im : list import) (mn : string)
  (fs : list (string * assert * chunk)) : module :=
  bmodule_ im (List.map (fun p => let '(f, pre, ch) := p in (f, pre, fun im' H => toCmd ch mn H)) fs).

Definition compile (m : module) : list (label * block) := List.map (fun x => let '(k, (_, b)) := x in (k, b)) (LabelMap.elements (XCAP.Blocks m)).


(** * Notations *)

(** ** Expressions *)

Infix "+" := Indir : loc_scope.
Delimit Scope loc_scope with loc.

Notation "$[ v ]" := (LvMem v%loc) (at level 0, n at level 0) : SP_scope.

Coercion natToW: nat >-> W.

Definition NToW (n : N) : W := NToWord _ n.
Coercion NToW : N >-> W.

Definition labl (mod func : string) : label := (mod, Global func).

Infix "!" := labl (at level 0, only parsing) : SP_scope.

Delimit Scope SP_scope with SP.


(** ** Instructions *)

Inductive rhs :=
| Rvalue : rvalue -> rhs
| Bop : rvalue -> binop -> rvalue -> rhs.

Coercion Rvalue : rvalue >-> rhs.

Definition RvImm' (n : nat) := RvImm ($ n).

Coercion RvImm' : nat >-> rvalue.

Notation "x + y" := (Bop x Plus y) : SP_scope.
Notation "x - y" := (Bop x Minus y) : SP_scope.
Notation "x * y" := (Bop x Times y) : SP_scope.

Notation "x = y" := {| COperand1 := x; CTest := Eq; COperand2 := y |} : SP_scope.
Notation "x <> y" := {| COperand1 := x; CTest := Ne; COperand2 := y |} : SP_scope.
Notation "x < y" := {| COperand1 := x; CTest := Lt; COperand2 := y |} : SP_scope.
Notation "x <= y" := {| COperand1 := x; CTest := Le; COperand2 := y |} : SP_scope.
Notation "x > y" := {| COperand1 := y; CTest := Lt; COperand2 := x |} : SP_scope.
Notation "x >= y" := {| COperand1 := y; CTest := Le; COperand2 := x |} : SP_scope.

Definition Assign' (lv : lvalue) (rh : rhs) :=
  Instr (match rh with
           | Rvalue rv => Assign lv rv
           | Bop rv1 bo rv2 => Binop lv rv1 bo rv2
         end).

Infix "<-" := Assign' (no associativity, at level 90) : SP_scope.


(** ** Commands *)

Infix ";;" := Seq (right associativity, at level 95) : SP_scope.

Notation "'Use' [ pf ]" := (Use_ _ (fun _ _ => pf%nat)) (no associativity, at level 95) : SP_scope.
Notation "'Use' st [ pf ]" := (Use_ _ (fun _ st => pf%nat)) (no associativity, at level 95) : SP_scope.

Notation "'If' c { b1 } 'else' { b2 }" := (If_ c b1 b2)
  (no associativity, at level 95, c at level 0) : SP_scope.

Notation "[ p ] 'While' c { b }" := (While_ p c b)
  (no associativity, at level 95, c at level 0) : SP_scope.

Notation "'Call' f [ p ]" := (Call_ f p)
  (no associativity, at level 95) : SP_scope.


(** ** Modules *)

Notation "'bfunction' name [ p ] { b }" := (name, p, b%SP)
  (no associativity, at level 95, only parsing) : SPfuncs_scope.
Delimit Scope SPfuncs_scope with SPfuncs.

Notation "{{ x 'with' .. 'with' y }}" := (cons x .. (cons y nil) ..) (only parsing) : SPfuncs_scope.
Delimit Scope SPfuncs_scope with SPfuncs.

Notation "'bmodule' name fs" := (bmodule_ nil name fs%SPfuncs) (no associativity, at level 95, name at level 0, only parsing).

Notation "x ! y" := (x, y) (only parsing) : SPimps_scope.
Notation "name @ [ p ]" := (let (x, y) := name in (x, y, p)) (at level 0, only parsing) : SPimps_scope.
Notation "[[ x , .. , y ]]" := (cons x .. (cons y nil) ..) (only parsing) : SPimps_scope.

Delimit Scope SPimps_scope with SPimps.

Notation "'bimport' is 'bmodule' name fs" := (bmodule_ is%SPimps name fs%SPfuncs) (no associativity, at level 95, name at level 0, only parsing).


(** ** Specs *)

Notation "st ~> p" := (fun st : settings * state => p%PropX%nat) (at level 100, only parsing).

Notation "st # r" := (Regs (snd st) r) (no associativity, at level 0).
Notation "st .[ a ]" := (ReadWord (fst st) (Mem (snd st)) a) (no associativity, at level 0).



(** * Tactics *)

Ltac conditions := unfold evalCond in *; simpl in *; unfold weqb, wneb, wltb, wleb in *; simpl in *; try discriminate;
  repeat match goal with
           | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
           | [ H : (if ?E then _ else _) = _ |- _ ] => destruct E; try discriminate; clear H
           | [ _ : context[inBounds_dec ?X ?Y] |- _ ] => destruct (inBounds_dec X Y); [ | try tauto ]; try discriminate
         end; simpl.

Ltac structured := apply bmoduleOk; [ exact (refl_equal false) | exact I |
  simpl; repeat (apply List.Forall_nil || apply List.Forall_cons);
    (try match goal with
           | [ |- context[toCmd _ _ (im := ?im) ?Him _] ] => generalize Him; intro;
             let im' := eval hnf in im in let im' := eval simpl in im' in change im with im' in *
         end; simpl; propxFo; conditions) ].

Ltac link t1 t2 := apply linkOk; [ apply t1 | apply t2
  | exact (refl_equal false) | repeat split | repeat split | exact I ].

Ltac ho := autorewrite with IL in *;
  repeat match goal with
           | [ |- ex _ ] => eexists
           | [ |- _ /\ _ ] => split
         end; eauto; cbv zeta; simpl; intros;
  repeat match goal with
           | [ H : ?X = Some _ |- ?X = Some (fun x => ?g x) ] => apply H
           | [ H : forall x, interp _ (_ --> ?p x) |- interp _ (?p _) ] => apply (Imply_sound (H _)); propxFo
           | [ |- interp _ _ ] => propxFo
         end; autorewrite with IL in *.

Ltac withLabel := eexists; split; [
  match goal with
    | [ |- ?E = _ ] => let E' := eval compute in E in change E with E'
  end; eauto | intros ].

Ltac equate x y := let H := fresh in assert (H : x = y) by reflexivity; clear H.

Ltac safety mok lab := eapply safety; [ exact (refl_equal 0) | exact (refl_equal Datatypes.Lt) | apply mok
  | match goal with
      | [ |- LabelMap.find ?l _ = _ ] => equate l lab
    end; match goal with
           | [ |- ?E = _ ] => let E' := eval compute in E in change E with E'
         end; reflexivity
  | reflexivity
  | propxFo ].


(** * Executing a program *)

Section exec.
  Variable stn : settings.
  Variable prog : program.

  Fixpoint exec (n : nat) (st : state') : option state' :=
    match n with
      | O => Some st
      | S n' => match step stn prog st with
                  | None => None
                  | Some st => exec n' st
                end
    end.
End exec.

Global Opaque natToWord.
