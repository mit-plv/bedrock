Set Implicit Arguments.

Require Import DecidableTypeEx.
Require Import FMapInterface.

Module UWFacts_fun (E : UsualDecidableType) (Import M : WSfun E).

  Require Import ListFacts1.

  Require Import FMapFacts1.
  Module Import UWFacts := UWFacts_fun E M.
  Import WFacts.
  Import P.
  Import F.

  Module FMapNotations.
    Infix "==" := (@Equal _) (at level 70) : fmap_scope.
    Notation "{}" := (@empty _) : fmap_scope.
    Infix "-" := (@diff _) : fmap_scope.
    Infix "+" := (@update _) : fmap_scope.
    Delimit Scope fmap_scope with fmap.
  End FMapNotations.

  Section TopSection.

    Require Import GeneralTactics.
    Require Import GeneralTactics2.
    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap_scope.

    Hint Extern 1 => reflexivity.

    Section Elt.

      Variable elt:Type.

      Implicit Types m : t elt.
      Implicit Types x y z k : key.
      Implicit Types e v : elt.
      Implicit Types ls : list (key * elt).

      Notation eqke := (@eq_key_elt elt).
      Notation eqk := (@eq_key elt).
      
      Lemma In_MapsTo : forall k m, In k m -> exists v, MapsTo k v m.
        unfold In; eauto.
      Qed.

      Lemma not_in_find : forall k m, ~ In k m -> find k m = None.
        intros; eapply not_find_in_iff; eauto.
      Qed.

      Lemma of_list_empty : of_list [] == @empty elt.
        eauto.
      Qed.
      
      (* update *)

      Lemma update_o_1 : forall k m1 m2, ~ In k m2 -> find k (m1 + m2) = find k m1.
        intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H0; eapply update_mapsto_iff in H0; openhyp.
        eapply MapsTo_In in H0; intuition.
        eapply find_1; eauto.
        eapply find_2 in H0.
        eapply find_1; eapply update_mapsto_iff; eauto.
      Qed.

      Lemma update_o_2 : forall k m1 m2, In k m2 -> find k (m1 + m2) = find k m2.
        intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H0; eapply update_mapsto_iff in H0; openhyp.
        eapply find_1; eauto.
        intuition.
        eapply find_2 in H0.
        eapply find_1; eapply update_mapsto_iff; eauto.
      Qed.

      Lemma update_empty_1 : forall m, {} + m == m.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H.
        eapply update_mapsto_iff in H; openhyp.
        eapply find_1; eauto.
        eapply empty_mapsto_iff in H; intuition.
        eapply find_2 in H.
        eapply find_1; eapply update_mapsto_iff; eauto.
      Qed.

      Lemma update_empty_2 : forall m, m + {} == m.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H.
        eapply update_mapsto_iff in H; openhyp.
        eapply empty_mapsto_iff in H; intuition.
        eapply find_1; eauto.
        eapply find_2 in H.
        eapply find_1; eapply update_mapsto_iff.
        right; split; eauto.
        intuition.
        eapply empty_in_iff; eauto.
      Qed.

      Lemma update_assoc : forall m1 m2 m3, m1 + m2 + m3 == m1 + (m2 + m3).
        intros.
        unfold Equal.
        intros.
        eapply option_univalence.
        split; intros.
        eapply find_2 in H.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        left.
        eapply update_mapsto_iff.
        eauto.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        left.
        eapply update_mapsto_iff.
        eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        not_not.
        eapply update_in_iff in H2.
        intuition.

        eapply find_2 in H.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        eapply update_mapsto_iff.
        eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        not_not.
        eapply update_in_iff.
        eauto.
        not_not.
        eapply update_in_iff.
        eauto.
      Qed.

      Lemma update_self : forall m, m + m == m.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H; eapply update_mapsto_iff in H; openhyp.
        eapply find_1; eauto.
        eapply MapsTo_In in H; intuition.
        eapply find_2 in H.
        eapply find_1; eapply update_mapsto_iff; eauto.
      Qed.

      Lemma update_same : forall m1 m2, m1 == m2 -> m1 + m2 == m1.
        intros.
        rewrite H.
        eapply update_self.
      Qed.

      Lemma update_diff_same : forall m1 m2 m3, m1 - m3 + (m2 - m3) == m1 + m2 - m3.
        intros.
        unfold Equal.
        intros.
        eapply option_univalence.
        split; intros.
        eapply find_2 in H.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply diff_mapsto_iff in H.
        openhyp.
        eapply find_1.
        eapply diff_mapsto_iff.
        split; eauto.
        eapply update_mapsto_iff.
        eauto.
        eapply diff_mapsto_iff in H.
        openhyp.
        eapply find_1.
        eapply diff_mapsto_iff.
        split; eauto.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        not_not.
        eapply diff_in_iff; eauto.
        
        eapply find_2 in H.
        eapply diff_mapsto_iff in H.
        openhyp.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        left.
        eapply diff_mapsto_iff; eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split.
        eapply diff_mapsto_iff; eauto.
        not_not.
        eapply diff_in_iff in H2.
        intuition.
      Qed.

      Lemma Disjoint_diff_update_comm : forall m1 m2 m3, Disjoint m2 m3 -> m1 - m2 + m3 == m1 + m3 - m2.
        intros.
        unfold Equal.
        intros.
        eapply option_univalence.
        split; intros.
        eapply find_2 in H0.
        eapply update_mapsto_iff in H0.
        openhyp.
        eapply find_1.
        eapply diff_mapsto_iff.
        split.
        eapply update_mapsto_iff.
        eauto.
        unfold Disjoint in *.
        intuition.
        eapply H.
        split; eauto.
        eapply MapsTo_In; eauto.
        eapply diff_mapsto_iff in H0.
        openhyp.
        eapply find_1.
        eapply diff_mapsto_iff.
        split; eauto.
        eapply update_mapsto_iff.
        eauto.

        eapply find_2 in H0.
        eapply diff_mapsto_iff in H0.
        openhyp.
        eapply update_mapsto_iff in H0.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        eapply diff_mapsto_iff.
        eauto.
      Qed.

      (* update_all *)

      Definition update_all ms := List.fold_left (fun acc m => update acc m) ms (@empty elt).

      Lemma update_all_nil : update_all [] == {}.
        eauto.
      Qed.

      Lemma update_all_single : forall m, update_all [m] == m.
        intros.
        unfold update_all; simpl.
        eapply update_empty_1.
      Qed.

      Definition update_all' m ms := fold_left (fun acc m0 : t elt => acc + m0) ms m.

      Lemma update_all'_m' : forall ms m1 m2, m1 == m2 -> update_all' m1 ms == update_all' m2 ms.
        unfold update_all'.
        induction ms; simpl; intros.
        eauto.
        erewrite IHms.
        eauto.
        rewrite H.
        eauto.
      Qed.

      Global Add Morphism update_all'
          with signature Equal ==> Logic.eq ==> Equal as update_all'_m.
        intros; eapply update_all'_m'; eauto.
      Qed.

      Lemma update_all_cons : forall ms m, update_all (m :: ms) == m + (update_all ms).
        induction ms; simpl; intros.
        rewrite update_all_nil.
        rewrite update_all_single.
        rewrite update_empty_2.
        eauto.
        unfold update_all in *.
        simpl in *.
        rewrite IHms.
        replace (fold_left (fun acc m0 : t elt => acc + m0) ms ({} + m + a)) with (update_all' ({} + m + a) ms) by reflexivity.
        rewrite update_assoc.
        unfold update_all'.
        rewrite IHms.
        rewrite update_assoc.
        eauto.
      Qed.

      Lemma update_all_Equal : forall ms1 ms2, List.Forall2 (@Equal elt) ms1 ms2 -> update_all ms1 == update_all ms2.
        induction 1; simpl; intros.
        eauto.
        repeat rewrite update_all_cons.
        rewrite H.
        rewrite IHForall2.
        eauto.
      Qed.

      Lemma app_all_update_all : forall lsls, @NoDupKey elt (app_all lsls) -> of_list (app_all lsls) == update_all (List.map (@of_list _) lsls).
        induction lsls; simpl; intros.
        eauto.
        rewrite update_all_cons.
        rewrite of_list_app; eauto.
        rewrite IHlsls; eauto.
        eapply NoDupKey_unapp2; eauto.
      Qed.

      Lemma update_all_elim : forall ms k v, MapsTo k v (update_all ms) -> exists m, List.In m ms /\ MapsTo k v m.
        induction ms; simpl; intros.
        rewrite update_all_nil in H.
        eapply empty_mapsto_iff in H; intuition.
        rewrite update_all_cons in H.
        eapply update_mapsto_iff in H; openhyp.
        eapply IHms in H; openhyp.
        eexists; split; eauto.
        eexists; split; eauto.
      Qed.

      (* diff *)

      Lemma diff_empty : forall m, diff m {} == m.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply find_1; eauto.
        eapply find_2 in H.
        eapply find_1.
        eapply diff_mapsto_iff; split; eauto.
        intuition; eapply empty_in_iff; eauto.
      Qed.

      Lemma empty_diff : forall m, {} - m == {}.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply empty_mapsto_iff in H; intuition.
        eapply find_2 in H; eapply empty_mapsto_iff in H; intuition.
      Qed.

      Lemma diff_same : forall m, m - m == {}.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply MapsTo_In in H; intuition.
        eapply find_2 in H; eapply empty_mapsto_iff in H; intuition.
      Qed.

      Lemma diff_update : forall m1 m2 m3, m1 - (m2 + m3) == m1 - m2 - m3.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply find_1.
        eapply diff_mapsto_iff; split.
        eapply diff_mapsto_iff; split; eauto.
        not_not; eapply update_in_iff; eauto.
        not_not; eapply update_in_iff; eauto.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply diff_mapsto_iff in H; openhyp.
        eapply find_1.
        eapply diff_mapsto_iff; split; eauto.
        not_not; eapply update_in_iff in H2; intuition.
      Qed.

      Lemma diff_diff_sym : forall m1 m2 m3, m1 - m2 - m3 == m1 - m3 - m2.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply diff_mapsto_iff in H; openhyp.
        eapply find_1.
        eapply diff_mapsto_iff; split; eauto.
        eapply diff_mapsto_iff; split; eauto.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply diff_mapsto_iff in H; openhyp.
        eapply find_1.
        eapply diff_mapsto_iff; split; eauto.
        eapply diff_mapsto_iff; split; eauto.
      Qed.

      Lemma diff_o : forall k m1 m2, ~ In k m2 -> find k (m1 - m2) = find k m1.
        intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H0; eapply diff_mapsto_iff in H0; openhyp.
        eapply find_1; eauto.
        eapply find_2 in H0.
        eapply find_1; eapply diff_mapsto_iff; split; eauto.
      Qed.

      Lemma diff_o_none : forall k m1 m2, In k m2 -> find k (m1 - m2) = None.
        intros.
        eapply not_in_find.
        intuition.
        eapply diff_in_iff in H0.
        intuition.
      Qed.

      (* Compat *)

      Definition Compat m1 m2 := forall k, In k m1 -> In k m2 -> find k m1 = find k m2.

      Lemma Compat_sym : forall m1 m2, Compat m1 m2 -> Compat m2 m1.
        unfold Compat; intros; symmetry; eauto.
      Qed.

      Lemma Compat_refl : forall m, Compat m m.
        unfold Compat; intros; eauto.
      Qed.

      Global Add Parametric Relation : (t elt) Compat
          reflexivity proved by Compat_refl
          symmetry proved by Compat_sym
            as Compat_rel.

      Global Add Morphism Compat
          with signature Equal ==> Equal ==> iff as Compat_m.
        unfold Compat; intros.
        intuition.
        rewrite <- H in *.
        rewrite <- H0 in *.
        eauto.
        rewrite H in *.
        rewrite H0 in *.
        eauto.
      Qed.

      Lemma Compat_diff : forall m1 m2 m, Compat m1 m2 -> Compat (m1 - m) m2.
        unfold Compat; intros.
        rewrite <- H; eauto.
        rewrite diff_o; eauto.
        eapply diff_in_iff in H0; intuition.
        eapply diff_in_iff in H0; intuition.
      Qed.

      Lemma Compat_empty : forall m, Compat m {}.
        unfold Compat; intros.
        eapply empty_in_iff in H0; intuition.
      Qed.

      Lemma Compat_update : forall m1 m2 m3, Compat m1 m2 -> Compat m1 m3 -> Compat m1 (m2 + m3).
        unfold Compat; intros.
        destruct (In_dec m3 k).
        rewrite update_o_2; eauto.
        rewrite update_o_1; eauto.
        eapply H; eauto.
        eapply update_in_iff in H2; intuition.
      Qed.

      Lemma Compat_update_sym : forall m1 m2, Compat m1 m2 -> m1 + m2 == m2 + m1.
        unfold Compat; intros.
        unfold Equal; intros.
        destruct (In_dec m1 y); destruct (In_dec m2 y).
        rewrite update_o_2 by eauto.
        rewrite update_o_2 by eauto.
        symmetry; eauto.
        rewrite update_o_1 by eauto.
        rewrite update_o_2 by eauto.
        eauto.
        rewrite update_o_2 by eauto.
        rewrite update_o_1 by eauto.
        eauto.
        rewrite update_o_1 by eauto.
        rewrite update_o_1 by eauto.
        repeat rewrite not_in_find; eauto.
      Qed.

      Lemma Compat_update_all : forall ms m, List.Forall (Compat m) ms -> Compat m (update_all ms).
        induction ms; simpl; intros.
        unfold update_all; simpl.
        eapply Compat_empty.
        rewrite update_all_cons.
        inversion H; subst.
        eapply Compat_update; eauto.
      Qed.

      Lemma Compat_add_not_In : forall k v m1 m2, Compat (add k v m1) m2 -> ~ In k m1 -> Compat m1 m2.
        intros.
        unfold Compat in *.
        intros.
        erewrite <- H; eauto.
        rewrite add_neq_o; eauto.
        not_not.
        subst; eauto.
        eapply add_in_iff; eauto.
      Qed.

      Lemma Compat_eq : forall k v1 v2 m1 m2, Compat m1 m2 -> find k m1 = Some v1 -> find k m2 = Some v2 -> v1 = v2.
        intros.
        unfold Compat in *.
        erewrite H in H0.
        congruence.
        eapply find_2 in H0.
        eapply MapsTo_In; eauto.
        eapply find_2 in H1.
        eapply MapsTo_In; eauto.
      Qed.

      Lemma Compat_MapsTo : forall m1 m2, Compat m1 m2 -> forall k v1 v2, MapsTo k v1 m1 -> MapsTo k v2 m2 -> v1 = v2.
        intros.
        generalize H0; intro.
        generalize H1; intro.
        eapply find_1 in H0.
        eapply find_1 in H1.
        rewrite H in H0.
        rewrite H0 in H1.
        injection H1; intros; eauto.
        eapply MapsTo_In; eauto.
        eapply MapsTo_In; eauto.
      Qed.

      Definition AllCompat := ForallOrdPairs Compat.

      Lemma update_all_intro : forall ms, AllCompat ms -> forall k v m, List.In m ms -> MapsTo k v m -> MapsTo k v (update_all ms).
        induction 1; simpl; intros.
        intuition.
        openhyp.
        subst.
        rewrite update_all_cons.
        destruct (In_dec (update_all l) k).
        eapply In_MapsTo in i.
        openhyp.
        eapply Compat_update_all in H.
        eapply Compat_MapsTo in H; eauto.
        subst.
        eapply update_mapsto_iff; eauto.
        eapply update_mapsto_iff; eauto.
        rewrite update_all_cons.
        eapply update_mapsto_iff; eauto.
      Qed.

      (* Disjoint *)

      Global Add Parametric Relation : (t elt) (@Disjoint elt)
          symmetry proved by (@Disjoint_sym elt)
            as Disjoint_rel.

      Lemma Disjoint_Compat : forall m1 m2, Disjoint m1 m2 -> Compat m1 m2.
        unfold Disjoint, Compat; intros; firstorder.
      Qed.

      Lemma Disjoint_empty : forall m, Disjoint m {}.
        unfold Disjoint; intros.
        intuition.
        eapply empty_in_iff in H1; intuition.
      Qed.

      Lemma Disjoint_update : forall m1 m2 m3, Disjoint m1 m2 -> Disjoint m1 m3 -> Disjoint m1 (m2 + m3).
        unfold Disjoint; intros.
        intuition.
        eapply update_in_iff in H3; firstorder.
      Qed.

      Lemma Disjoint_update_sym : forall m1 m2, Disjoint m1 m2 -> update m1 m2 == update m2 m1.
        intros.
        eapply Compat_update_sym.
        eapply Disjoint_Compat; eauto.
      Qed.

      Lemma Disjoint_diff : forall m1 m2 m3, Disjoint m1 m2 -> Disjoint m1 (m2 - m3).
        unfold Disjoint; intros.
        intuition.
        eapply diff_in_iff in H2; firstorder.
      Qed.

      Lemma Disjoint_after_diff : forall m1 m2, Disjoint (m1 - m2) m2.
        unfold Disjoint; intros.
        intuition.
        eapply diff_in_iff in H0; firstorder.
      Qed.

      Lemma Disjoint_diff_no_effect : forall m1 m2, Disjoint m1 m2 -> m1 - m2 == m1.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H0; eapply diff_mapsto_iff in H0; openhyp.
        eapply find_1; eauto.
        eapply find_2 in H0.
        eapply find_1; eapply diff_mapsto_iff; split; eauto.
        intuition; eapply H; split; eauto.
        eapply MapsTo_In; eauto.
      Qed.

      Lemma Disjoint_update_all : forall ms m, List.Forall (Disjoint m) ms -> Disjoint m (update_all ms).
        induction ms; simpl; intros.
        unfold update_all; simpl.
        eapply Disjoint_empty.
        rewrite update_all_cons.
        inversion H; subst.
        eapply Disjoint_update; eauto.
      Qed.

      (* map *)

      Lemma map_empty : forall B (f : elt -> B), map f {} == {}.
        unfold Equal; intros.
        rewrite map_o.
        repeat rewrite empty_o.
        eauto.
      Qed.

      Lemma map_add : forall B (f : _ -> B) k v m, map f (add k v m) == add k (f v) (map f m).
        unfold Equal; intros.
        rewrite map_o.
        repeat rewrite add_o.
        destruct (eq_dec k y).
        eauto.
        rewrite map_o.
        eauto.
      Qed.

      Lemma map_update : forall B (f : _ -> B) m1 m2, map f (m1 + m2) == map f m1 + map f m2.
        unfold Equal; intros.
        eapply option_univalence.
        split; intros.
        eapply find_2 in H.
        eapply map_mapsto_iff in H.
        openhyp.
        subst.
        eapply update_mapsto_iff in H0.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        left.
        eapply map_mapsto_iff.
        eexists; eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split.
        eapply map_mapsto_iff.
        eexists; eauto.
        not_not.
        eapply map_in_iff; eauto.

        eapply find_2 in H.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply map_mapsto_iff in H.
        openhyp.
        subst.
        eapply find_1.
        eapply map_mapsto_iff.
        eexists; split; eauto.
        eapply update_mapsto_iff.
        eauto.
        eapply map_mapsto_iff in H.
        openhyp.
        subst.
        eapply find_1.
        eapply map_mapsto_iff.
        eexists; split; eauto.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        not_not.
        eapply map_in_iff; eauto.
      Qed.

      Lemma map_of_list : forall B (f : elt -> B) ls, map f (of_list ls) == of_list (List.map (fun p => (fst p, f (snd p))) ls).
        induction ls; simpl; intros.
        eapply map_empty.
        unfold uncurry; simpl in *.
        rewrite <- IHls.
        destruct a; simpl in *.
        eapply map_add.
      Qed.

      (* mapi *)

      Global Add Parametric Morphism elt' : (@mapi elt elt')
          with signature Logic.eq ==> Equal ==> Equal as mapi_m.
        intros; subst; eauto.
        unfold Equal; intros.
        repeat rewrite mapi_o.
        rewrite H; eauto.
        intros; subst; eauto.
        intros; subst; eauto.
      Qed.

      Lemma find_mapi :
        forall B (f : _ -> _ -> B) k v m,
          find k m = Some v ->
          find k (mapi f m) = Some (f k v).
        intros.
        rewrite mapi_o.
        rewrite H.
        eauto.
        intros; subst; eauto.
      Qed.

      Lemma mapi_empty : forall B (f : _ -> elt -> B), mapi f {} == {}.
        unfold Equal; intros.
        rewrite mapi_o.
        repeat rewrite empty_o.
        eauto.
        intros.
        subst.
        eauto.
      Qed.

      Lemma mapi_add : forall B (f : _ -> _ -> B) k v m, mapi f (add k v m) == add k (f k v) (mapi f m).
        unfold Equal; intros.
        rewrite mapi_o.
        repeat rewrite add_o.
        destruct (eq_dec k y).
        subst.
        eauto.
        rewrite mapi_o.
        eauto.
        intros; subst; eauto.
        intros; subst; eauto.
      Qed.

      Lemma mapi_of_list : forall B (f : _ -> _ -> B) ls, mapi f (of_list ls) == of_list (List.map (fun p => (fst p, f (fst p) (snd p))) ls).
        induction ls; simpl; intros.
        eapply mapi_empty.
        unfold uncurry; simpl in *.
        rewrite <- IHls.
        destruct a; simpl in *.
        eapply mapi_add.
      Qed.

      Lemma mapi_update : forall B (f : _ -> _ -> B) m1 m2, mapi f (m1 + m2) == mapi f m1 + mapi f m2.
        unfold Equal; intros.
        eapply option_univalence.
        split; intros.
        eapply find_2 in H.
        eapply mapi_mapsto_iff in H.
        openhyp.
        subst.
        eapply update_mapsto_iff in H0.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        left.
        eapply mapi_mapsto_iff.
        intros; subst; eauto.
        eexists; eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split.
        eapply mapi_mapsto_iff.
        intros; subst; eauto.
        eexists; eauto.
        not_not.
        eapply mapi_in_iff; eauto.
        intros; subst; eauto.

        eapply find_2 in H.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply mapi_mapsto_iff in H.
        openhyp.
        subst.
        eapply find_1.
        eapply mapi_mapsto_iff.
        intros; subst; eauto.
        eexists; split; eauto.
        eapply update_mapsto_iff.
        eauto.
        intros; subst; eauto.
        eapply mapi_mapsto_iff in H.
        openhyp.
        subst.
        eapply find_1.
        eapply mapi_mapsto_iff.
        intros; subst; eauto.
        eexists; split; eauto.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        not_not.
        eapply mapi_in_iff; eauto.
        intros; subst; eauto.
      Qed.

      Lemma NoDupKey_app_all_elim : forall lsls, NoDupKey (app_all lsls) -> forall ls, List.In ls lsls -> NoDupKey ls.
        induction lsls; simpl; intuition.
        subst.
        eapply NoDupKey_unapp1; eauto.
        eapply IHlsls; eauto.
        eapply NoDupKey_unapp2; eauto.
      Qed.

      Lemma NoDupKey_app_all_AllCompat : forall lsls, NoDupKey (app_all lsls) -> AllCompat (List.map (@of_list _) lsls).
        induction lsls; simpl; intuition.
        econstructor.
        econstructor.
        eapply Forall_forall.
        intros.
        eapply in_map_iff in H0; openhyp; subst.
        eapply Disjoint_Compat.
        unfold Disjoint.
        intros.
        nintro.
        openhyp.
        eapply In_of_list in H0.
        eapply In_of_list in H2.
        generalize H; intros.
        eapply NoDupKey_app_DisjointKey in H.
        eapply H.
        split; eauto.
        unfold InKey in *.
        rewrite map_app_all.
        eapply In_app_all_intro; eauto.
        eapply in_map; eauto.
        eapply NoDupKey_unapp2 in H.
        eapply NoDupKey_app_all_elim; eauto.
        eapply NoDupKey_unapp1; eauto.
        eapply IHlsls.
        eapply NoDupKey_unapp2; eauto.
      Qed.

    End Elt.

    Lemma map_update_all_comm : forall elt B (f : elt -> B) ms, map f (update_all ms) == update_all (List.map (map f) ms).
      induction ms; simpl; intros.
      repeat rewrite update_all_nil.
      rewrite map_empty.
      eauto.
      repeat rewrite update_all_cons.
      rewrite map_update.
      rewrite IHms.
      eauto.
    Qed.


    Lemma mapi_update_all_comm : forall elt B (f : _ -> elt -> B) ms, mapi f (update_all ms) == update_all (List.map (mapi f) ms).
      induction ms; simpl; intros.
      repeat rewrite update_all_nil.
      rewrite mapi_empty; eauto.
      eauto.
      repeat rewrite update_all_cons.
      rewrite mapi_update.
      rewrite IHms.
      eauto.
    Qed.

  End TopSection.

End UWFacts_fun.
