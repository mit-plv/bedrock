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
  Definition map := key -> data.

  Definition dict := (list key * map)%type.

  Definition upd_map (m : map) k v k' :=
    if eq_dec k' k then v else m k'.

  Require Import List.

  Definition sel (d : dict) (k : key) : option data.
    admit.
  Defined.

  Definition upd (d : dict) k v := ((k :: fst d), upd_map (snd d) k v).

  Definition keys (d : dict) : list key.
    admit.
  Defined.

  Definition remove (d : dict) (k : key) : dict.
    admit.
  Defined.

  Lemma sel_upd_eq : forall m k v k', k' = k ->  sel (upd m k v) k' = Some v.
    admit. (*intros; unfold upd; destruct (eq_dec k' k); intuition.*)
  Qed.

  Lemma sel_upd_ne : forall m k v k', k' <> k -> sel (upd m k v) k' = sel m k'.
    admit. (*intros; unfold upd; destruct (eq_dec k' k); intuition.*)
  Qed.

End Dict.

