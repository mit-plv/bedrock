Require Import AutoSep.
Require Import Malloc Sets.

Set Implicit Arguments.

(*
Local Hint Extern 3 (himp _ _ _) => apply himp_star_frame.
Local Hint Extern 3 (himp _ _ _) => apply himp_star_frame_comm.
*)

Inductive tree :=
| Leaf
| Node : tree -> tree -> tree.

Module Type BST.
  Parameter bst' : set -> tree -> W -> HProp.
  Parameter bst : set -> W -> HProp.

  Axiom bst'_extensional : forall s t p, HProp_extensional (bst' s t p).
  Axiom bst_extensional : forall s p, HProp_extensional (bst s p).

  Axiom bst'_set_extensional : forall t s s' p, s %= s' -> bst' s t p ===> bst' s' t p.

  Axiom bst_fwd : forall s p, bst s p ===> [| freeable p 2 |]
    * Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r.
  Axiom bst_bwd : forall s p, ([| freeable p 2 |]
    * Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r) ===> bst s p.

  Axiom nil_fwd : forall s t (p : W), p = 0 -> bst' s t p ===> [| s %= empty /\ t = Leaf |].
  Axiom nil_bwd : forall s t (p : W), p = 0 -> [| s %= empty /\ t = Leaf |] ===> bst' s t p.

  Axiom cons_fwd : forall s t (p : W), p <> 0 -> bst' s t p ===>
    Ex t1, Ex t2, Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2) * bst' (s %< v) t1 p1* bst' (s %> v) t2 p2
    * [| freeable p 3 /\ t = Node t1 t2 /\ v %in s |].

  Axiom cons_bwd : forall s t (p : W), p <> 0 ->
    (Ex t1, Ex t2, Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2) * bst' (s %< v) t1 p1* bst' (s %> v) t2 p2
      * [| freeable p 3 /\ t = Node t1 t2 /\ v %in s |]) ===> bst' s t p.
End BST.

Declare Module Bst : BST.

Import Bst.
Export Bst.
Hint Immediate bst_extensional bst'_extensional.

Definition hints : TacPackage.
 idtac "tree-set:prepare1". Time 
  prepare auto_ext tt tt  (bst_fwd, nil_fwd, cons_fwd) (bst_bwd, nil_bwd, cons_bwd).
 Time Defined.

Lemma exhausted_cases : forall a b : W, a <> b
  -> ~(a < b)
  -> a > b.
  intros.
  assert (wordToN a <> wordToN b) by (generalize wordToN_inj; firstorder).
  nomega.
Qed.

Local Hint Resolve exhausted_cases.
Local Hint Extern 5 (@eq W _ _) => words.
Local Hint Extern 3 (himp _ _ _) => apply bst'_set_extensional.


Goal forall (stn_st : settings * state) (specs : codeSpec W (settings * state)),
   interp specs
     ([|False|]%PropX \/
      ((Ex st' : state,
        (((Ex st'0 : state,
           ((ExX  : ST.settings * smem,
             (Ex s : set,
              (Ex t : tree,
               (Ex p : W,
                (Ex w : W,
                 ![star
                     (star
                        (star
                           (star (Regs st'0 Sp =*> p)
                              ((Regs st'0 Sp ^+ $ (4)) =*> w)) 
                           ^[bst' s t p]) ^[mallocHeap])
                     (fun (stn : ST.settings) (sm : smem) => Var0 (stn, sm))]
                   (fst stn_st, st'0) /\
                 (ExX  : ST.settings * state,
                  Cptr (Regs st'0 Rp) #0 /\
                  (Al st0 : settings * state,
                   [|(st0) # (Sp) = Regs st'0 Sp /\ w %in s \is (st0) # (Rv)|] /\
                   ![star
                       (star
                          (star
                             ^[star (Ex v : W, Regs st'0 Sp =*> v)
                                 (star
                                    (Ex v : W, (Regs st'0 Sp ^+ $ (4)) =*> v)
                                    Emp)] ^[bst' s t p]) 
                          ^[mallocHeap])
                       (fun (stn : ST.settings) (sm : smem) =>
                        Lift (Var0 (stn, sm)))] st0 ---> 
                   Var0 st0))))))) /\
            [|evalCond $[ Sp]%SP Ne 0 (fst stn_st) st'0 = Some true|]) /\
           [|evalInstrs (fst stn_st) st'0 (Assign Rv $[ Sp]%SP :: nil) =
             Some st'|]) /\
          [|evalCond $[ Rv + 4]%SP IL.Eq $[ Sp + 4]%SP (fst stn_st) st' =
            Some false|]) /\
         [|evalCond $[ Sp + 4]%SP IL.Lt $[ Rv + 4]%SP (fst stn_st) st' =
           Some true|]) /\
        [|evalInstrs (fst stn_st) st' (Assign $[ Sp]%SP $[ Rv]%SP :: nil) =
          Some (snd stn_st)|]) \/
       (Ex st' : state,
        (((Ex st'0 : state,
           ((ExX  : ST.settings * smem,
             (Ex s : set,
              (Ex t : tree,
               (Ex p : W,
                (Ex w : W,
                 ![star
                     (star
                        (star
                           (star (Regs st'0 Sp =*> p)
                              ((Regs st'0 Sp ^+ $ (4)) =*> w)) 
                           ^[bst' s t p]) ^[mallocHeap])
                     (fun (stn : ST.settings) (sm : smem) => Var0 (stn, sm))]
                   (fst stn_st, st'0) /\
                 (ExX  : ST.settings * state,
                  Cptr (Regs st'0 Rp) #0 /\
                  (Al st0 : settings * state,
                   [|(st0) # (Sp) = Regs st'0 Sp /\ w %in s \is (st0) # (Rv)|] /\
                   ![star
                       (star
                          (star
                             ^[star (Ex v : W, Regs st'0 Sp =*> v)
                                 (star
                                    (Ex v : W, (Regs st'0 Sp ^+ $ (4)) =*> v)
                                    Emp)] ^[bst' s t p]) 
                          ^[mallocHeap])
                       (fun (stn : ST.settings) (sm : smem) =>
                        Lift (Var0 (stn, sm)))] st0 ---> 
                   Var0 st0))))))) /\
            [|evalCond $[ Sp]%SP Ne 0 (fst stn_st) st'0 = Some true|]) /\
           [|evalInstrs (fst stn_st) st'0 (Assign Rv $[ Sp]%SP :: nil) =
             Some st'|]) /\
          [|evalCond $[ Rv + 4]%SP IL.Eq $[ Sp + 4]%SP (fst stn_st) st' =
            Some false|]) /\
         [|evalCond $[ Sp + 4]%SP IL.Lt $[ Rv + 4]%SP (fst stn_st) st' =
           Some false|]) /\
        [|evalInstrs (fst stn_st) st' (Assign $[ Sp]%SP $[ Rv + 8]%SP :: nil) =
          Some (snd stn_st)|]))%PropX) ->
   interp specs
     (ExX  : ST.settings * smem,
      (Ex s : set,
       (Ex t : tree,
        (Ex p : W,
         (Ex w : W,
          ![star
              (star
                 (star
                    (star ((stn_st) # (Sp) =*> p)
                       (((stn_st) # (Sp) ^+ $ (4)) =*> w)) 
                    ^[bst' s t p]) ^[mallocHeap])
              (fun (stn : ST.settings) (sm : smem) => Var0 (stn, sm))] stn_st /\
          (ExX  : ST.settings * state,
           Cptr (stn_st) # (Rp) #0 /\
           (Al st0 : settings * state,
            [|(st0) # (Sp) = (stn_st) # (Sp) /\ w %in s \is (st0) # (Rv)|] /\
            ![star
                (star
                   (star
                      ^[star (Ex v : W, (stn_st) # (Sp) =*> v)
                          (star (Ex v : W, ((stn_st) # (Sp) ^+ $ (4)) =*> v)
                             Emp)] ^[bst' s t p]) ^[mallocHeap])
                (fun (stn : ST.settings) (sm : smem) => Lift (Var0 (stn, sm)))]
              st0 ---> Var0 st0))))))%PropX).
Proof.
  sep hints.
Admitted.



Goal forall (stn_st : settings * state) (specs : codeSpec W (settings * state)),
   interp specs
     ([|False|]%PropX \/
      (Ex st' : state,
       (((Ex st'0 : state,
          ((ExX  : ST.settings * smem,
            (Ex s : set,
             (Ex t : tree,
              (Ex ans : W,
               (Ex w : W,
                (Ex rp : W,
                 (Ex p : W,
                  (Ex v : W,
                   ![star
                       (star
                          (star
                             (star
                                (star (Regs st'0 Sp =*> p)
                                   (star ((Regs st'0 Sp ^+ $ (4)) =*> w)
                                      (star ((Regs st'0 Sp ^+ $ (8)) =*> rp)
                                         (star
                                            ((Regs st'0 Sp ^+ $ (12)) =*> ans)
                                            ((Regs st'0 Sp ^+ $ (16)) =*> v)))))
                                (ans =*> p)) ^[bst' s t p]) 
                          ^[mallocHeap])
                       (fun (stn : ST.settings) (sm : smem) => Var0 (stn, sm))]
                     (fst stn_st, st'0) /\
                   (ExX  : ST.settings * state,
                    Cptr rp #0 /\
                    (Al st0 : settings * state,
                     [|(st0) # (Sp) = Regs st'0 Sp|] /\
                     (Ex t' : tree,
                      (Ex p' : W,
                       ![star
                           (star
                              (star
                                 (star
                                    ^[star (Ex v0 : W, Regs st'0 Sp =*> v0)
                                        (star
                                           (Ex v0 : W,
                                            (Regs st'0 Sp ^+ $ (4)) =*> v0)
                                           (star
                                              (Ex v0 : W,
                                               (Regs st'0 Sp ^+ $ (8)) =*> v0)
                                              (star
                                                 (Ex v0 : W,
                                                  (Regs st'0 Sp ^+ $ (12)) =*>
                                                  v0)
                                                 (star
                                                  (Ex v0 : W,
                                                  (Regs st'0 Sp ^+ $ (16)) =*>
                                                  v0) 
                                                  Emp))))] 
                                    (ans =*> p')) ^[bst' (s %+ w) t' p'])
                              ^[mallocHeap])
                           (fun (stn : ST.settings) (sm : smem) =>
                            Lift (Var0 (stn, sm)))] st0)) ---> 
                     Var0 st0)))))))))) /\
           [|evalCond $[ Sp]%SP Ne 0 (fst stn_st) st'0 = Some true|]) /\
          [|evalInstrs (fst stn_st) st'0 (Assign Rv $[ Sp]%SP :: nil) =
            Some st'|]) /\
         [|evalCond $[ Rv + 4]%SP IL.Eq $[ Sp + 4]%SP (fst stn_st) st' =
           Some false|]) /\
        [|evalCond $[ Sp + 4]%SP IL.Lt $[ Rv + 4]%SP (fst stn_st) st' =
          Some true|] \/
        (Ex st'0 : state,
         (((Ex st'1 : state,
            ((ExX  : ST.settings * smem,
              (Ex s : set,
               (Ex t : tree,
                (Ex ans : W,
                 (Ex w : W,
                  (Ex rp : W,
                   (Ex p : W,
                    (Ex v : W,
                     ![star
                         (star
                            (star
                               (star
                                  (star (Regs st'1 Sp =*> p)
                                     (star ((Regs st'1 Sp ^+ $ (4)) =*> w)
                                        (star
                                           ((Regs st'1 Sp ^+ $ (8)) =*> rp)
                                           (star
                                              ((Regs st'1 Sp ^+ $ (12)) =*>
                                               ans)
                                              ((Regs st'1 Sp ^+ $ (16)) =*> v)))))
                                  (ans =*> p)) ^[bst' s t p]) 
                            ^[mallocHeap])
                         (fun (stn : ST.settings) (sm : smem) =>
                          Var0 (stn, sm))] (fst stn_st, st'1) /\
                     (ExX  : ST.settings * state,
                      Cptr rp #0 /\
                      (Al st0 : settings * state,
                       [|(st0) # (Sp) = Regs st'1 Sp|] /\
                       (Ex t' : tree,
                        (Ex p' : W,
                         ![star
                             (star
                                (star
                                   (star
                                      ^[star (Ex v0 : W, Regs st'1 Sp =*> v0)
                                          (star
                                             (Ex v0 : W,
                                              (Regs st'1 Sp ^+ $ (4)) =*> v0)
                                             (star
                                                (Ex v0 : W,
                                                 (Regs st'1 Sp ^+ $ (8)) =*>
                                                 v0)
                                                (star
                                                  (Ex v0 : W,
                                                  (Regs st'1 Sp ^+ $ (12)) =*>
                                                  v0)
                                                  (star
                                                  (Ex v0 : W,
                                                  (Regs st'1 Sp ^+ $ (16)) =*>
                                                  v0) 
                                                  Emp))))] 
                                      (ans =*> p')) 
                                   ^[bst' (s %+ w) t' p']) 
                                ^[mallocHeap])
                             (fun (stn : ST.settings) (sm : smem) =>
                              Lift (Var0 (stn, sm)))] st0)) ---> 
                       Var0 st0)))))))))) /\
             [|evalCond $[ Sp]%SP Ne 0 (fst stn_st) st'1 = Some true|]) /\
            [|evalInstrs (fst stn_st) st'1 (Assign Rv $[ Sp]%SP :: nil) =
              Some st'0|]) /\
           [|evalCond $[ Rv + 4]%SP IL.Eq $[ Sp + 4]%SP (fst stn_st) st'0 =
             Some false|]) /\
          [|evalCond $[ Sp + 4]%SP IL.Lt $[ Rv + 4]%SP (fst stn_st) st'0 =
            Some false|]) /\
         [|evalInstrs (fst stn_st) st'0 (Binop Rv Rv Plus 8 :: nil) =
           Some st'|])) /\
       [|evalInstrs (fst stn_st) st'
           (Assign $[ Sp + 12]%SP Rv :: Assign $[ Sp]%SP $[ Rv]%SP :: nil) =
         Some (snd stn_st)|])%PropX) ->
   interp specs
     (ExX  : ST.settings * smem,
      (Ex s : set,
       (Ex t : tree,
        (Ex ans : W,
         (Ex w : W,
          (Ex rp : W,
           (Ex p : W,
            (Ex v : W,
             ![star
                 (star
                    (star
                       (star
                          (star ((stn_st) # (Sp) =*> p)
                             (star (((stn_st) # (Sp) ^+ $ (4)) =*> w)
                                (star (((stn_st) # (Sp) ^+ $ (8)) =*> rp)
                                   (star
                                      (((stn_st) # (Sp) ^+ $ (12)) =*> ans)
                                      (((stn_st) # (Sp) ^+ $ (16)) =*> v)))))
                          (ans =*> p)) ^[bst' s t p]) 
                    ^[mallocHeap])
                 (fun (stn : ST.settings) (sm : smem) => Var0 (stn, sm))]
               stn_st /\
             (ExX  : ST.settings * state,
              Cptr rp #0 /\
              (Al st0 : settings * state,
               [|(st0) # (Sp) = (stn_st) # (Sp)|] /\
               (Ex t' : tree,
                (Ex p' : W,
                 ![star
                     (star
                        (star
                           (star
                              ^[star (Ex v0 : W, (stn_st) # (Sp) =*> v0)
                                  (star
                                     (Ex v0 : W,
                                      ((stn_st) # (Sp) ^+ $ (4)) =*> v0)
                                     (star
                                        (Ex v0 : W,
                                         ((stn_st) # (Sp) ^+ $ (8)) =*> v0)
                                        (star
                                           (Ex v0 : W,
                                            ((stn_st) # (Sp) ^+ $ (12)) =*>
                                            v0)
                                           (star
                                              (Ex v0 : W,
                                               ((stn_st) # (Sp) ^+ $ (16)) =*>
                                               v0) 
                                              Emp))))] 
                              (ans =*> p')) ^[bst' (s %+ w) t' p'])
                        ^[mallocHeap])
                     (fun (stn : ST.settings) (sm : smem) =>
                      Lift (Var0 (stn, sm)))] st0)) ---> 
               Var0 st0)))))))))%PropX).
Proof.
  post.
  evaluate hints.
  descend.
  Print Ltac step.
(*  clear H13 H14 H15 H20 H21  H22 H23 H24. *)
  Time let ext := hints in
  match goal with
  | |- _ _ = Some _ => solve [ eauto    ]
  | |- interp _ (![_] _) => idtac "1" ; cancel ext
  | |- interp _ (![_]%PropX _ ---> ![_]%PropX _) => idtac "2" ; cancel ext
  | |- himp _ _ _ => idtac "3" ; progress cancel ext
  | |- interp _ (_ _ _ ?x ---> (_ _ _ ?y ---> _ ?x)%PropX) =>
        match y with
        | x => fail 1
        | _ => apply implyR
        end
  | _ => idtac "ho" ; ho
  end.
Admitted.


Goal forall (stn_st : settings * state) (specs : codeSpec W (settings * state)),
   interp specs
     ((Ex st' : state,
       ((Ex st'0 : state,
         ((ExX  : ST.settings * smem,
           (Ex s : set,
            (Ex t : tree,
             (Ex p : W,
              (Ex pointerHere : W,
               [|p <> 0|] /\
               ![star
                   (star
                      (star
                         (star
                            (star
                               (star (Regs st'0 Sp =*> p)
                                  ((Regs st'0 Sp ^+ $ (4)) =*> pointerHere))
                               ^[star
                                   (Ex v : W, (Regs st'0 Sp ^+ $ (8)) =*> v)
                                   (star
                                      (Ex v : W,
                                       (Regs st'0 Sp ^+ $ (8) ^+ $ (4)) =*> v)
                                      Emp)]) (pointerHere =*> p))
                         ^[bst' s t p]) ^[mallocHeap])
                   (fun (stn : ST.settings) (sm : smem) => Var0 (stn, sm))]
                 (fst stn_st, st'0) /\
               (ExX  : ST.settings * state,
                Cptr (Regs st'0 Rp) #0 /\
                (Al st0 : settings * state,
                 [|(st0) # (Sp) = Regs st'0 Sp /\
                   (st0) # (Rv) %in s /\ s %< (st0) # (Rv) %= empty|] /\
                 (Ex t' : tree,
                  (Ex p' : W,
                   ![star
                       (star
                          (star
                             (star
                                ^[star (Ex v : W, Regs st'0 Sp =*> v)
                                    (star
                                       (Ex v : W,
                                        (Regs st'0 Sp ^+ $ (4)) =*> v)
                                       (star
                                          (Ex v : W,
                                           (Regs st'0 Sp ^+ $ (8)) =*> v)
                                          (star
                                             (Ex v : W,
                                              (Regs st'0 Sp ^+ $ (12)) =*> v)
                                             Emp)))] 
                                (pointerHere =*> p'))
                             ^[bst' (s %- (st0) # (Rv)) t' p']) 
                          ^[mallocHeap])
                       (fun (stn : ST.settings) (sm : smem) =>
                        Lift (Var0 (stn, sm)))] st0)) ---> 
                 Var0 st0))))))) /\
          [|evalCond 1 IL.Eq 1 (fst stn_st) st'0 = Some true|]) /\
         [|evalInstrs (fst stn_st) st'0 (Assign Rv $[ Sp]%SP :: nil) =
           Some st'|]) /\
        [|evalCond $[ Rv]%SP Ne 0 (fst stn_st) st' = Some true|]) /\
       [|evalInstrs (fst stn_st) st'
           (Assign $[ Sp + 4]%SP Rv :: Assign $[ Sp]%SP $[ Rv]%SP :: nil) =
         Some (snd stn_st)|])%PropX \/ [|False|]%PropX) ->
   interp specs
     (ExX  : ST.settings * smem,
      (Ex s : set,
       (Ex t : tree,
        (Ex p : W,
         (Ex pointerHere : W,
          [|p <> 0|] /\
          ![star
              (star
                 (star
                    (star
                       (star
                          (star ((stn_st) # (Sp) =*> p)
                             (((stn_st) # (Sp) ^+ $ (4)) =*> pointerHere))
                          ^[star (Ex v : W, ((stn_st) # (Sp) ^+ $ (8)) =*> v)
                              (star
                                 (Ex v : W,
                                  ((stn_st) # (Sp) ^+ $ (8) ^+ $ (4)) =*> v)
                                 Emp)]) (pointerHere =*> p)) 
                    ^[bst' s t p]) ^[mallocHeap])
              (fun (stn : ST.settings) (sm : smem) => Var0 (stn, sm))] stn_st /\
          (ExX  : ST.settings * state,
           Cptr (stn_st) # (Rp) #0 /\
           (Al st0 : settings * state,
            [|(st0) # (Sp) = (stn_st) # (Sp) /\
              (st0) # (Rv) %in s /\ s %< (st0) # (Rv) %= empty|] /\
            (Ex t' : tree,
             (Ex p' : W,
              ![star
                  (star
                     (star
                        (star
                           ^[star (Ex v : W, (stn_st) # (Sp) =*> v)
                               (star
                                  (Ex v : W, ((stn_st) # (Sp) ^+ $ (4)) =*> v)
                                  (star
                                     (Ex v : W,
                                      ((stn_st) # (Sp) ^+ $ (8)) =*> v)
                                     (star
                                        (Ex v : W,
                                         ((stn_st) # (Sp) ^+ $ (12)) =*> v)
                                        Emp)))] (pointerHere =*> p'))
                        ^[bst' (s %- (st0) # (Rv)) t' p']) 
                     ^[mallocHeap])
                  (fun (stn : ST.settings) (sm : smem) =>
                   Lift (Var0 (stn, sm)))] st0)) ---> 
            Var0 st0))))))%PropX).
Admitted.