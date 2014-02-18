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

    Variable elt:Type.

    Definition update_all A maps := List.fold_left (fun acc m => update acc m) maps (@empty A).

    Implicit Types m : t elt.
    Implicit Types x y z k : key.
    Implicit Types e v : elt.
    Implicit Types ls : list (key * elt).

    Notation eqke := (@eq_key_elt elt).
    Notation eqk := (@eq_key elt).
    
    Require Import GeneralTactics.
    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap_scope.

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

    Lemma update_all_cons : forall m ms, update_all (m :: ms) == update m (update_all ms).
      admit.
    Qed.

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

    Lemma app_all_update_all : forall lsls, @NoDupKey elt (app_all lsls) -> of_list (app_all lsls) == update_all (List.map (@of_list _) lsls).
      admit.
    Qed.

    Lemma map_update_all_comm : forall B (f : elt -> B) ms, map f (update_all ms) == update_all (List.map (map f) ms).
      admit.
    Qed.

    Lemma update_all_Equal : forall ms1 ms2, List.Forall2 (@Equal elt) ms1 ms2 -> update_all ms1 == update_all ms2.
      admit.
    Qed.

    Lemma map_of_list : forall B (f : elt -> B) ls, map f (of_list ls) == of_list (List.map (fun p => (fst p, f (snd p))) ls).
      admit.
    Qed.

  End Elt.

End UWFacts_fun.
