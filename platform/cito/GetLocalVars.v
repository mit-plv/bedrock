Set Implicit Arguments.

Require Import FreeVars.
Require Import StringSet.

Definition get_local_vars stmt arg_vars ret_var := 
  let vars := free_vars stmt in
  let vars := add ret_var vars in
  let vars := List.fold_left (fun acc x => remove x acc) arg_vars vars in
  elements vars.

Lemma ret_in_vars : forall arg_vars s r, List.In r (arg_vars ++ get_local_vars s arg_vars r).
  admit.
Qed.