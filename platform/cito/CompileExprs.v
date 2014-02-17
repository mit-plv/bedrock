Require Import AutoSep.
Require Import SyntaxExpr.

Set Implicit Arguments. 

Section TopLevel.

  Variable vars : list string.

  Variable temp_size : nat.

  Variable exprs : list Expr.

  Variable base dst : nat.

  Definition is_state sp vs temps dst dst_buf : HProp :=
    (locals vars vs 0 (sp ^+ $8) *
     array temps (sp ^+ $8 ^+ $(4 * length vars)) *
     array dst_buf (sp ^+ $ dst))%Sep.

  Definition new_pre : assert := 
    x ~> ExX, Ex vs, Ex temps, Ex dst_buf,
    ![^[is_state x#Sp vs temps dst dst_buf] * #0]x /\
    [| length temps = temp_size /\
       length exprs = length dst_buf |].

  Require Import SemanticsExpr.
  Require Import DepthExpr.
  Require Import Max.

  Definition depth := max_list (map depth exprs) 0.

  Require CompileExpr.
  Require Import ListFacts.

  Local Open Scope nat.

  Definition runs_to x_pre x := 
    forall specs other vs temps dst_buf,
      interp specs (![is_state x_pre#Sp vs temps dst dst_buf * other ] x_pre)
      -> length temps = temp_size
      -> length exprs = length dst_buf
      -> Regs x Sp = x_pre#Sp /\
      exists changed,
        interp specs (![is_state (Regs x Sp) vs (upd_sublist temps base changed) dst (map (eval vs) exprs) * other ] (fst x_pre, x)) /\
        length changed <= depth.

  Definition post (pre : assert) := 
    st ~> Ex st_pre, 
    pre (fst st, st_pre) /\
    [| runs_to (fst st, st_pre) (snd st) |].

  Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

  Require Import FreeVarsExpr.
  Require Import StringSet.
  Import StringSet.
  Require Import SetUtil.
  Require Import Union.

  Definition syn_req exprs base := 
    Subset (union_list (map free_vars exprs)) (to_set vars) /\
    base + depth <= temp_size /\
    List.Forall (fun e => DepthExpr.depth e < depth) exprs.

  Definition verifCond base pre := imply pre new_pre :: syn_req exprs base :: nil.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Definition Seq2 := @Seq_ _ imports_global modName.

  Definition Skip := Straightline_ imports modName nil.

  Fixpoint Seq ls :=
    match ls with
      | nil => Skip
      | a :: ls' => Seq2 a (Seq ls')
    end.

  Definition Strline := Straightline_ imports modName.

  Definition SaveRv lv := Strline (IL.Assign lv (RvLval (LvReg Rv)) :: nil).

  Definition stack_slot (n : nat) := LvMem (Sp + n)%loc.

  Print CompileExpr.compile.
  
  Definition compile_expr e n := CompileExpr.compile vars temp_size imports_global modName e n.

  Fixpoint do_compile exprs base dst :=
    match exprs with
      | nil => nil
      | x :: xs => 
        compile_expr x base 
          :: SaveRv (stack_slot dst) 
          :: do_compile xs base (4 + dst)
    end.

  Definition body := Seq (do_compile exprs base dst).

  Require Import Wrap.

  Opaque mult.

  Definition compile : cmd imports modName.
    refine (Wrap imports imports_global modName body post (verifCond base) _ _).

    Lemma postOk : forall specs exprs base dst pre x,
      interp specs (Postcondition (Seq (do_compile exprs base dst) pre) x)
      -> imply pre (x ~> ExX, Ex vs, Ex temps, Ex dst_buf,
        ![^[is_state x#Sp vs temps dst dst_buf] * #0]x /\
        [| length temps = temp_size /\
          length exprs = length dst_buf |])
      -> syn_req exprs base
      -> exists x0, interp specs (pre (fst x, x0))
        /\ forall specs other vs temps dst_buf,
          interp specs (![is_state (Regs x0 Sp) vs temps dst dst_buf * other ] (fst x, x0))
          -> length temps = temp_size
          -> length exprs = length dst_buf
          -> Regs (snd x) Sp = Regs x0 Sp /\
          exists changed,
            interp specs (![is_state (Regs (snd x) Sp) vs (upd_sublist temps base changed) dst (map (eval vs) exprs) * other ] (fst x, snd x)) /\
            length changed <= depth.
      induction exprs0; post.

      clear_fancy.
      Transparent evalInstrs.
      simpl in H3.
      Opaque evalInstrs.
      injection H3; clear H3; intros; subst.
      descend.
      eauto.
      descend.
      instantiate (1 := nil); simpl.
      destruct dst_buf; simpl in *; auto.
      discriminate.
      simpl; auto.

      apply IHexprs0 in H; clear IHexprs0; auto.
      Focus 2.
      hnf; post.
      apply H0 in H3; clear H0; post.
      unfold is_state in H2.
      assert (interp specs0
        (![locals vars x4 0 (Regs x2 Sp ^+ $ (8)) *
          array x5 (Regs x2 Sp ^+ $ (8) ^+ $ (4 * Datatypes.length vars)) *
          (array x6 (Regs x2 Sp ^+ $ (dst0)) *
          ![fun m : ST.settings * smem => x3 m]) ] 
        (fst x0, x2))).
      clear H; clear_fancy.
      step auto_ext.
      clear H2.
      apply H5 in H3; clear H5; post.
      unfold stack_slot in H4.
      clear H; clear_fancy.

      Lemma array_out : forall a p,
        length a > 0
        -> array a p ===> p =*> Array.selN a 0 * array (tl a) (p ^+ $4).
        clear_fancy; destruct a; unfold array; simpl; intros.
        inversion H.
        destruct a.
        sepLemma.
        apply Himp_star_frame; try apply Himp_refl.
        eapply Himp_trans; [ apply ptsto32m_shift_base' | ].
        instantiate (1 := 4); auto.
        apply Himp_refl.
      Qed.

      Lemma change_hyp : forall P Q specs st,
        interp specs (![P] st)
        -> P ===> Q
        -> interp specs (![Q] st).
        intros.
        eapply Imply_sound.
        rewrite sepFormula_eq.
        apply H0.
        rewrite sepFormula_eq in *; auto.
      Qed.

      eapply change_hyp in H5.
      Focus 2.
      apply Himp_star_frame; [ apply Himp_refl | ].
      apply Himp_star_frame; [ | apply Himp_refl ].
      apply array_out; omega.
      destruct x6; simpl in *; try discriminate.
      evaluate auto_ext.
      destruct x0; simpl in *.
      descend.
      replace (Regs x2 Sp ^+ natToW dst0 ^+ natToW 4) with (Regs x2 Sp ^+ natToW (S (S (S (S dst0)))))
        in H9.
      unfold is_state.
      unfold CompileExpr.is_state in H9.
      step auto_ext.
      rewrite H.
      step auto_ext.
      rewrite <- H3.
      step auto_ext.
      rewrite <- wplus_assoc.
      unfold natToW.
      rewrite <- natToWord_plus.
      repeat f_equal.
      omega.
      rewrite length_upd_sublist; auto.
      auto.

      post.
      post.
      eexists; split; eauto.
      intros.
      clear H2.
      unfold is_state in H.
      assert (interp specs0
        (![CompileExpr.is_state vars (Regs x2 Sp) vs temps
          * (array dst_buf (Regs x2 Sp ^+ $ (dst0)) * other ) ] 
        (fst x, x2))).
      unfold CompileExpr.is_state.
      clear H0; clear_fancy.
      step auto_ext.
      clear H.
      apply H5 in H2; clear H5.
      generalize H6; intro Hs.
      apply H2 in Hs; clear H2.
      destruct x; simpl in *.
      destruct Hs as [ ? [ ? [ ? [ ? [ ] ] ] ] ].
      simpl in *.
      eapply change_hyp in H2.
      Focus 2.
      apply Himp_star_frame; [ apply Himp_refl | ].
      apply Himp_star_frame; [ | apply Himp_refl ].
      apply array_out; omega.
      unfold stack_slot in H4.
      clear H0; clear_fancy.
      evaluate auto_ext.
      destruct dst_buf; simpl in *; try discriminate.
      assert (interp specs0
        (![is_state (Regs x0 Sp) vs (upd_sublist temps base0 x) (S (S (S (S dst0)))) dst_buf *
          ((Regs x2 Sp ^+ natToW dst0) =*> Regs x1 Rv * other)] (s, x0))).
      unfold is_state.
      unfold CompileExpr.is_state in H9.
      step auto_ext.
      rewrite <- H0.
      unfold natToW.
      rewrite H.
      rewrite <- H0.
      step auto_ext.
      rewrite <- wplus_assoc.
      unfold natToW.
      rewrite <- natToWord_plus.
      replace (dst0 + 4) with (S (S (S (S dst0)))) by omega.
      step auto_ext.
      clear H9.
      apply H3 in H10; clear H3; auto.
      post.
      congruence.

      assert (length (upd_sublist (upd_sublist temps base0 x) base0 x3)
        = length temps).
      repeat rewrite length_upd_sublist; reflexivity.
      eapply CompileExpr.get_changed in H9.
      post.
      descend.
      rewrite <- H12.
      Focus 3.
      instantiate (1 := base0 + max (length x) (length x3)).
      omega.
      Focus 2.
      destruct H1.
      destruct (NPeano.Nat.max_spec (length x) (length x3)); intuition.
      inversion_clear H16.
      omega.
      unfold is_state in *.
      eapply change_hyp.
      Focus 2.
      apply Himp_star_frame; [ | eapply Himp_refl ].
      apply Himp_star_frame; [ eapply Himp_refl | ].

      Lemma array_in : forall a p,
        length a > 0
        -> p =*> Array.selN a 0 * array (tl a) (p ^+ $4) ===> array a p.
        clear_fancy; destruct a; unfold array; simpl; intros.
        inversion H.
        destruct a.
        sepLemma.
        apply Himp_star_frame; try apply Himp_refl.
        eapply Himp_trans; [ | apply ptsto32m_shift_base ].
        instantiate (1 := 4); auto.
        apply Himp_refl.
        auto.
      Qed.

      apply array_in; simpl; auto.
      simpl.
      replace (Regs s0 Sp ^+ $ (dst0) ^+ $ (4))
        with (Regs s0 Sp ^+ ($ (dst0) ^+ $ (4))) by words.
      rewrite <- natToWord_plus.
      replace (dst0 + 4) with (S (S (S (S dst0)))) by omega.
      generalize dependent (map (eval vs) exprs0); intros.
      step auto_ext.
      replace (Regs x2 Sp) with (Regs s0 Sp) by congruence.
      step auto_ext.

      intros.
      repeat rewrite CompileExpr.upd_sublist_unchanged by auto; reflexivity.

      intros.
      generalize (Max.le_max_l (length x) (length x3)).
      generalize (Max.le_max_r (length x) (length x3)); intros.
      repeat rewrite CompileExpr.upd_sublist_unchanged_high by auto; reflexivity.

      rewrite length_upd_sublist; auto.
      unfold syn_req in *; intuition.
      hnf; intros.
      apply H2.
      simpl.
      unfold union_list.
      simpl.

      Lemma In_union_list : forall x exprs0 acc acc',
        In x (fold_left union (map free_vars exprs0) acc)
        -> Subset acc acc'
        -> In x (fold_left union (map free_vars exprs0) acc').
        induction exprs0; simpl; intros.
        apply H0; auto.
        eapply IHexprs0; eauto.
        hnf; intros.
        apply StringFacts.union_iff.
        apply StringFacts.union_iff in H1.
        intuition.
      Qed.

      eapply In_union_list; eauto.
      hnf; intros.
      apply StringFacts.empty_iff in H5; tauto.
      inversion H4; auto.
    Qed.

    abstract (unfold verifCond; wrap0;
      match goal with
        | [ H : interp _ _ |- _ ] => eapply postOk in H; post; descend; eauto
      end).

    admit.
  Defined.

End TopLevel.