Set Implicit Arguments.

Module Type KEY.
  Parameter key : Type.
  Parameter eq_dec : forall x y : key, {x = y} + {x <> y}.
End KEY.

Module Type DATA.
  Parameter data : Type.
End DATA.

Module Dict (MKey : KEY) (MData : DATA).

  Import MKey MData.

  Definition dict := key -> data.

  Definition upd (m : dict) key value k :=
    if eq_dec k key then
      value
      else
        m k.

  Lemma sel_upd_eq : forall m k v k', k' = k ->  upd m k v k' = v.
    intros; unfold upd; destruct (eq_dec k' k); intuition.
  Qed.

  Lemma sel_upd_ne : forall m k v k', k' <> k -> upd m k v k' = m k'.
    intros; unfold upd; destruct (eq_dec k' k); intuition.
  Qed.

End Dict.

