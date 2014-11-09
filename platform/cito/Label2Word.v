Set Implicit Arguments.

Require Import IL Memory Word.
Require Import GLabel ConvertLabel.

Section stn.

  Variable Domain : glabel -> Prop.

  Variable stn : settings.

  Definition stn_injective :=
    forall lbl1 lbl2 p, 
      Domain lbl1 -> 
      Domain lbl2 -> 
      Labels stn lbl1 = Some p -> 
      Labels stn lbl2 = Some p -> 
      lbl1 = lbl2.

  Definition labels (lbl : glabel) : option W := Labels stn lbl.
  
  Definition is_label_map_to_word lbl p :=
    match labels lbl with
      | Some p' => 
        if weq p p' then
          true
        else
          false
      | None => false
    end.

  Definition is_label_map_to_word' A p (x : glabel * A) := is_label_map_to_word (fst x) p.

  Definition find_by_word A m (p : W) : option A :=
    match List.find (is_label_map_to_word' p) m with
      | Some (_, a) => Some a
      | None => None
    end.

End stn.