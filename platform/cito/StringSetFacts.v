Set Implicit Arguments.

Require Import StringSet.
Import StringSet.

Local Hint Constructors List.NoDup.

Lemma In_InA : forall A (x : A) ls,
  List.In x ls
  -> SetoidList.InA (@Logic.eq A) x ls.
  induction ls; simpl; intuition.
Qed.

Lemma NoDupA_NoDup : forall A ls,
  SetoidList.NoDupA (@Logic.eq A) ls
  -> List.NoDup ls.
  induction 1; intuition auto using In_InA.
Qed.

Lemma NoDup_elements : forall s, List.NoDup (elements s).
  intros.
  apply NoDupA_NoDup.
  apply elements_3w.
Qed.
