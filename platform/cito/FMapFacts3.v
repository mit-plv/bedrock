Set Implicit Arguments.

Require Import DecidableTypeEx.
Require Import FMapInterface.

Module UWFacts_fun (E : UsualDecidableType) (Import M : WSfun E).

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

  Section Elt.

    Require Import GeneralTactics.
    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap_scope.

    Definition update_all elt maps := List.fold_left (fun acc m => update acc m) maps (@empty elt).

    Lemma update_all_cons : forall elt m ms, @update_all elt (m :: ms) == update m (update_all ms).
      admit.
    Qed.

    Variable elt:Type.

    Implicit Types m : t elt.
    Implicit Types x y z k : key.
    Implicit Types e v : elt.
    Implicit Types ls : list (key * elt).

    Notation eqke := (@eq_key_elt elt).
    Notation eqk := (@eq_key elt).
    
    Hint Extern 1 => reflexivity.

    Lemma of_list_empty : of_list [] == @empty elt.
      admit.
    Qed.
    
    Lemma diff_empty : forall m, diff m {} == {}.
      admit.
    Qed.

    Definition Compat m1 m2 := forall k, In k m1 -> In k m2 -> find k m1 = find k m2.

    Add Morphism Compat
        with signature Equal ==> Equal ==> iff as Compat_m.
      admit.
    Qed.

    Lemma Compat_sym : forall m1 m2, Compat m1 m2 -> Compat m2 m1.
      admit.
    Qed.

    Lemma Compat_refl : forall m, Compat m m.
      admit.
    Qed.

    Add Parametric Relation : (t elt) Compat
        reflexivity proved by Compat_refl
        symmetry proved by Compat_sym
          as CompatReflSym.

    Lemma Disjoint_update_sym : forall m1 m2, Disjoint m1 m2 -> update m1 m2 == update m2 m1.
      admit.
    Qed.

    Lemma diff_update : forall m1 m2 m3, m1 - (m2 + m3) == m1 - m2 - m3.
      admit.
    Qed.

    Lemma diff_diff_sym : forall m1 m2 m3, m1 - m2 - m3 == m1 - m3 - m2.
      admit.
    Qed.

    Lemma update_same : forall m1 m2, m1 == m2 -> m1 + m2 == m1.
      admit.
    Qed.

    Lemma Compat_diff : forall m1 m2 m, Compat m1 m2 -> Compat (m1 - m) m2.
      admit.
    Qed.

    Lemma Compat_empty : forall m, Compat m {}.
      admit.
    Qed.

    Lemma Compat_update : forall m1 m2 m3, Compat m1 m2 -> Compat m1 m3 -> Compat m1 (m2 + m3).
      admit.
    Qed.

    Lemma Compat_update_all : forall ms m, List.Forall (Compat m) ms -> Compat m (update_all ms).
      induction ms; simpl; intros.
      unfold update_all; simpl.
      eapply Compat_empty.
      rewrite update_all_cons.
      inversion H; subst.
      eapply Compat_update; eauto.
    Qed.

    Lemma Disjoint_empty : forall m, Disjoint m {}.
      admit.
    Qed.

    Lemma Disjoint_update : forall m1 m2 m3, Disjoint m1 m2 -> Disjoint m1 m3 -> Disjoint m1 (m2 + m3).
      admit.
    Qed.

    Lemma In_MapsTo : forall k m, In k m -> exists v, MapsTo k v m.
      unfold In; eauto.
    Qed.

    Lemma Disjoint_Compat : forall m1 m2, Disjoint m1 m2 -> Compat m1 m2.
      admit.
    Qed.

    Lemma Disjoint_diff_update_comm : forall m1 m2 m3, Disjoint m2 m3 -> m1 - m2 + m3 = m1 + m3 - m2.
      admit.
    Qed.

    Lemma update_diff_same : forall m1 m2 m3, m1 - m3 + (m2 - m3) = m1 + m2 - m3.
      admit.
    Qed.

    Lemma Compat_update_sym : forall m1 m2, Compat m1 m2 -> m1 + m2 = m2 + m1.
      admit.
    Qed.

    Lemma Disjoint_diff : forall m1 m2 m3, Disjoint m1 m2 -> Disjoint m1 (m2 - m3).
      admit.
    Qed.

    Lemma Disjoint_after_diff : forall m1 m2, Disjoint (m1 - m2) m2.
      admit.
    Qed.

    Add Parametric Relation : (t elt) (@Disjoint elt)
        symmetry proved by (@Disjoint_sym elt)
          as Disjoint_m.

    Require Import ListFacts2.

    Lemma map_empty : forall B (f : elt -> B), map f {} == {}.
      admit.
    Qed.

    Lemma map_add : forall B (f : _ -> B) k v m, map f (add k v m) == add k (f v) (map f m).
      admit.
    Qed.

    Lemma update_all_nil : forall elt, @update_all elt [] == {}.
      eauto.
    Qed.

    Lemma map_update : forall B (f : _ -> B) m1 m2, map f (m1 + m2) == map f m1 + map f m2.
      admit.
    Qed.

    Lemma map_update_all_comm : forall B (f : elt -> B) ms, map f (update_all ms) == update_all (List.map (map f) ms).
      induction ms; simpl; intros.
      repeat rewrite update_all_nil.
      rewrite map_empty.
      eauto.
      repeat rewrite update_all_cons.
      rewrite map_update.
      rewrite IHms.
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

    Lemma map_of_list : forall B (f : elt -> B) ls, map f (of_list ls) == of_list (List.map (fun p => (fst p, f (snd p))) ls).
      induction ls; simpl; intros.
      eapply map_empty.
      unfold uncurry; simpl in *.
      rewrite <- IHls.
      destruct a; simpl in *.
      eapply map_add.
    Qed.

    Lemma app_all_update_all : forall lsls, @NoDupKey elt (app_all lsls) -> of_list (app_all lsls) == update_all (List.map (@of_list _) lsls).
      induction lsls; simpl; intros.
      eauto.
      rewrite update_all_cons.
      rewrite of_list_app; eauto.
      rewrite IHlsls; eauto.
      eapply NoDupKey_unapp2; eauto.
    Qed.

  End Elt.

End UWFacts_fun.
