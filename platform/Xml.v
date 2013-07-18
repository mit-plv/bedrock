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
Definition xcons (x : xml) (xs : list xml) : list xml := x :: xs.
Notation "<*> tag </> x1 , .. , xN </>" := (XTag tag (xcons x1 .. (xcons xN nil) ..))
  (tag at level 0) : out_scope.
Delimit Scope out_scope with out.

Notation "'Write' o" := (Output o%out) (at level 0, o at level 0) : action_scope.
Infix ";;" := Seq : action_scope.
Delimit Scope action_scope with action.

Notation "'Match' p 'Do' a 'end'" := {| Pattern := p%pat; Action := a%action |}.

Ltac wf := split; simpl; intuition (try (congruence || reflexivity)).
