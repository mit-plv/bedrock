Require Import Word.

Definition B := word 8.
Definition W := word 32.

Definition mem_get_word addr mem footprint_w (mem_get : mem -> addr -> option B) (implode : B * B * B * B -> W) (p : addr) (m : mem)
    : option W :=
    let '(a,b,c,d) := footprint_w p in
    match mem_get m a , mem_get m b , mem_get m c , mem_get m d with
      | Some a , Some b , Some c , Some d =>
        Some (implode (a,b,c,d))
      | _ , _ , _ , _ => None
    end.

Definition mem_set_word addr mem footprint_w (mem_set : mem -> addr -> B -> mem) (explode : W -> B * B * B * B) (p : addr) (v : W)
    (m : mem) : mem :=
    let '(a,b,c,d) := footprint_w p in
    let '(av,bv,cv,dv) := explode v in
    mem_set (mem_set (mem_set (mem_set m d dv) c cv) b bv) a av.
