Require Import XmlLang.
Export XmlLang.


Coercion XmlLang.Cdata : string >-> XmlLang.pat.
Notation "$ x" := (XmlLang.Var x) (at level 0) : pat_scope.
Infix "/" := XmlLang.Tag : pat_scope.
Infix "&" := XmlLang.Both (at level 41, right associativity) : pat_scope.
Infix ";;" := XmlLang.Ordered : pat_scope.
Delimit Scope pat_scope with pat.

Coercion XCdata : string >-> xml.
Notation "$ x" := (XVar x) : out_scope.
Notation "^ x" := (XColumn x) (at level 0) : out_scope.
Definition xcons (x : xml) (xs : list xml) : list xml := x :: xs.
Notation "<*> tag </> x1 , .. , xN </>" := (XTag tag (xcons x1 .. (xcons xN nil) ..))
  (tag at level 0) : out_scope.
Delimit Scope out_scope with out.

Coercion Const : string >-> exp.
Notation "$ x" := (Input x) : exp_scope.
Delimit Scope exp_scope with exp.

Notation "col = e" := ((col, e%exp) :: nil) : condition_scope.
Infix "&&" := app : condition_scope.
Delimit Scope condition_scope with condition.

Definition econs (x : exp) (xs : list exp) : list exp := x :: xs.
Notation "'Insert' t ( e1 , .. , eN )" := (XmlLang.Insert t (econs e1%exp .. (econs eN%exp nil) ..))
  (at level 0, t at level 0) : action_scope.
Notation "'Write' o" := (Output o%out) (at level 0, o at level 0) : action_scope.
Notation "'From' tab 'Where' cond 'Write' o" :=
  (SelectOutput tab cond%condition o%out)
  (at level 0, tab at level 0, cond at level 0, o at level 0) : action_scope.
Infix ";;" := Seq : action_scope.
Delimit Scope action_scope with action.

Notation "'Match' p 'Do' a 'end'" := {| Pattern := p%pat; Action := a%action |}.

Ltac wf := split; simpl; intuition (try (congruence || reflexivity || NoDup));
  match goal with
      | [ |- Logic.ex _ ] =>
        match goal with
          | [ |- context[?e = _] ] => exists e
        end; unfold ewfs; simpl; intuition;
        repeat match goal with
                 | [ |- List.Forall _ _ ] => constructor
               end; simpl; auto
    | _ =>
      repeat match goal with
               | [ H : List.Exists _ _ |- _ ] => inversion H; clear H; subst
             end; simpl in *; tauto
  end; repeat constructor.

Ltac goodSchema := repeat constructor.
