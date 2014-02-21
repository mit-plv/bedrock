Set Implicit Arguments.

Require Import FreeVars.
Require Import StringSet.
Import StringSet.

Definition get_local_vars stmt arg_vars ret_var := 
  let vars := free_vars stmt in
  let vars := add ret_var vars in
  let vars := List.fold_left (fun acc x => remove x acc) arg_vars vars in
  elements vars.

Lemma InA_In : forall A (x : A) ls,
  SetoidList.InA (@Logic.eq A) x ls
  -> List.In x ls.
  induction 1; simpl; intuition.
Qed.

Lemma keep_it : forall r arg_vars acc,
  ~List.In r arg_vars
  -> In r acc
  -> List.In r
  (elements
    (List.fold_left (fun (acc : t) (x : elt) => remove x acc) arg_vars acc)).
  induction arg_vars; simpl; intuition.
  apply InA_In.
  apply StringFacts.elements_iff; auto.
  apply IHarg_vars; auto.
  apply StringFacts.remove_iff; intuition.
Qed.

Lemma ret_in_vars : forall arg_vars s r, List.In r (arg_vars ++ get_local_vars s arg_vars r).
  intros; apply List.in_or_app.
  destruct (List.In_dec String.string_dec r arg_vars); intuition.
  right.
  unfold get_local_vars; simpl.
  apply keep_it; auto.
  apply StringFacts.add_iff; auto.
Qed.
