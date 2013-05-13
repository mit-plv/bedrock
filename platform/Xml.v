Require Import XmlLang.
Export XmlLang.


Coercion XmlLang.Cdata : string >-> XmlLang.pat.
Notation "$ x" := (XmlLang.Var x) (at level 0) : pat_scope.
Infix "/" := XmlLang.Tag : pat_scope.
Infix "&" := XmlLang.Both (at level 41, right associativity) : pat_scope.
Infix ";;" := XmlLang.Ordered : pat_scope.
Delimit Scope pat_scope with pat.

Coercion XmlOutput.Cdata : string >-> XmlOutput.xml.
Notation "$ x" := (XmlOutput.Var (x ++ "_start")%string (x ++ "_len")%string) : out_scope.
Definition xcons (x : XmlOutput.xml) (xs : list XmlOutput.xml) : list XmlOutput.xml := x :: xs.
Notation "<*> tag </> x1 , .. , xN </>" := (XmlOutput.Tag tag (xcons x1 .. (xcons xN nil) ..))
  (tag at level 0) : out_scope.
Delimit Scope out_scope with out.

Notation "'Match' p 'Do' o 'end'" := {| Pattern := p%pat; Output := o%out |}.

Ltac wf :=
  repeat split; repeat constructor; simpl in *; intuition (try congruence);
    match goal with
      | [ H : (_, _) = (_, _) |- _ ] => injection H; clear H; intros; subst
    end;
    match goal with
      | [ |- context[_ = ?s] ] => solve [ exists s; intuition ]
    end.

