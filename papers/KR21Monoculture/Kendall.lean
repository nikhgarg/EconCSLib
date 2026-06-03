import KR21Monoculture.FirstChoice
import EconCSLib.SocialChoice.Ranking.Kendall

open scoped BigOperators

namespace KR21Monoculture

def invertedPair {n : ℕ} (ρ π : Ranking n) (ab : Candidate n × Candidate n) :
    Prop :=
  rankOf ρ ab.1 < rankOf ρ ab.2 ∧ rankOf π ab.2 < rankOf π ab.1

noncomputable def inversionFinset {n : ℕ} (ρ π : Ranking n) :
    Finset (Candidate n × Candidate n) := by
  classical
  exact Finset.univ.filter (fun ab => invertedPair ρ π ab)

noncomputable def inversionFinsetInvolving {n : ℕ} (ρ π : Ranking n)
    (c : Candidate n) : Finset (Candidate n × Candidate n) := by
  classical
  exact (inversionFinset ρ π).filter (fun ab => ab.1 = c ∨ ab.2 = c)

noncomputable def inversionFinsetNotInvolving {n : ℕ} (ρ π : Ranking n)
    (c : Candidate n) : Finset (Candidate n × Candidate n) := by
  classical
  exact (inversionFinset ρ π).filter (fun ab => ¬(ab.1 = c ∨ ab.2 = c))

noncomputable def inversionFinsetInvolvingSecondNotFirst {n : ℕ}
    (ρ π : Ranking n) : Finset (Candidate n × Candidate n) := by
  classical
  exact (inversionFinset ρ π).filter
    (fun ab =>
      (ab.1 = secondChoice π ∨ ab.2 = secondChoice π) ∧
        ab.1 ≠ firstChoice π ∧ ab.2 ≠ firstChoice π)

noncomputable def kendallTau {n : ℕ} (ρ π : Ranking n) : ℕ :=
  (inversionFinset ρ π).card

@[simp] theorem invertedPair_self_false {n : ℕ} (ρ : Ranking n)
    (ab : Candidate n × Candidate n) :
    ¬ invertedPair ρ ρ ab :=
  EconCSLib.SocialChoice.Ranking.invertedPair_self_false ρ ab

@[simp] theorem inversionFinset_self {n : ℕ} (ρ : Ranking n) :
    inversionFinset ρ ρ = ∅ :=
  EconCSLib.SocialChoice.Ranking.inversionFinset_self ρ

@[simp] theorem kendallTau_self {n : ℕ} (ρ : Ranking n) :
    kendallTau ρ ρ = 0 :=
  EconCSLib.SocialChoice.Ranking.kendallTau_self ρ

theorem rankOf_ne_zero_of_ne_firstChoice {n : ℕ} (π : Ranking n)
    {c : Candidate n} (hc : c ≠ firstChoice π) :
    rankOf π c ≠ 0 :=
  EconCSLib.SocialChoice.Ranking.rankOf_ne_zero_of_ne_firstChoice π hc

theorem zero_lt_rankOf_of_ne_firstChoice {n : ℕ} (π : Ranking n)
    {c : Candidate n} (hc : c ≠ firstChoice π) :
    (0 : Candidate n) < rankOf π c :=
  EconCSLib.SocialChoice.Ranking.zero_lt_rankOf_of_ne_firstChoice π hc

theorem inversionFinsetInvolving_firstChoice_eq_image_Iio {n : ℕ}
    (ρ π : Ranking n) :
    inversionFinsetInvolving ρ π (firstChoice π) =
      (Finset.Iio (rankOf ρ (firstChoice π))).map
        ⟨fun i : Candidate n => (ρ i, firstChoice π),
          by
            intro i j h
            exact ρ.injective (Prod.ext_iff.mp h).1⟩ :=
  EconCSLib.SocialChoice.Ranking.inversionFinsetInvolving_firstChoice_eq_image_Iio ρ π

theorem inversionFinsetInvolving_firstChoice_card {n : ℕ}
    (ρ π : Ranking n) :
    (inversionFinsetInvolving ρ π (firstChoice π)).card =
      (rankOf ρ (firstChoice π) : ℕ) :=
  EconCSLib.SocialChoice.Ranking.inversionFinsetInvolving_firstChoice_card ρ π

theorem inversionFinsetInvolving_card_add_notInvolving_card {n : ℕ}
    (ρ π : Ranking n) (c : Candidate n) :
    (inversionFinsetInvolving ρ π c).card +
        (inversionFinsetNotInvolving ρ π c).card =
      (inversionFinset ρ π).card :=
  EconCSLib.SocialChoice.Ranking.inversionFinsetInvolving_card_add_notInvolving_card
    ρ π c

theorem kendallTau_eq_firstChoice_rank_add_notInvolving_card {n : ℕ}
    (ρ π : Ranking n) :
    kendallTau ρ π =
      (rankOf ρ (firstChoice π) : ℕ) +
        (inversionFinsetNotInvolving ρ π (firstChoice π)).card :=
  EconCSLib.SocialChoice.Ranking.kendallTau_eq_firstChoice_rank_add_notInvolving_card
    ρ π

theorem rankOf_eq_zero_iff_eq_firstChoice {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    rankOf π c = 0 ↔ c = firstChoice π :=
  EconCSLib.SocialChoice.Ranking.rankOf_eq_zero_iff_eq_firstChoice π c

theorem rankOf_lt_one_eq_zero {n : ℕ}
    {i : Candidate n} (hi : i < (1 : Candidate n)) :
    i = 0 :=
  EconCSLib.SocialChoice.Ranking.rankOf_lt_one_eq_zero hi

theorem one_le_of_ne_zero {n : ℕ}
    {i : Candidate n} (hi : i ≠ 0) :
    (1 : Candidate n) ≤ i :=
  EconCSLib.SocialChoice.Ranking.one_le_of_ne_zero hi

@[simp] theorem candidate_val_add_one_of_lt {n : ℕ}
    {i j : Candidate n} (hij : i < j) :
    ((i + 1 : Candidate n) : ℕ) = (i : ℕ) + 1 :=
  EconCSLib.SocialChoice.Ranking.candidate_val_add_one_of_lt hij

theorem inversionFinsetInvolvingSecondNotFirst_eq_map_Ico {n : ℕ}
    (τ : Ranking n) (hfirst : firstChoice τ = 0) :
    inversionFinsetInvolvingSecondNotFirst (Equiv.refl (Candidate n)) τ =
      (Finset.Ico (1 : Candidate n) (secondChoice τ)).map
        ⟨fun i : Candidate n => (i, secondChoice τ),
          by
            intro i j h
            exact (Prod.ext_iff.mp h).1⟩ :=
  EconCSLib.SocialChoice.Ranking.inversionFinsetInvolvingSecondNotFirst_eq_map_Ico
    τ hfirst

theorem inversionFinsetInvolvingSecondNotFirst_card {n : ℕ}
    (τ : Ranking n) (hfirst : firstChoice τ = 0) :
    (inversionFinsetInvolvingSecondNotFirst
      (Equiv.refl (Candidate n)) τ).card =
      (secondChoice τ : ℕ) - 1 :=
  EconCSLib.SocialChoice.Ranking.inversionFinsetInvolvingSecondNotFirst_card
    τ hfirst

theorem inversionFinsetInvolving_secondChoice_eq_involvingSecondNotFirst {n : ℕ}
    (τ : Ranking n) (hfirst : firstChoice τ = 0) :
    inversionFinsetInvolving (Equiv.refl (Candidate n)) τ (secondChoice τ) =
      inversionFinsetInvolvingSecondNotFirst (Equiv.refl (Candidate n)) τ :=
  EconCSLib.SocialChoice.Ranking.inversionFinsetInvolving_secondChoice_eq_involvingSecondNotFirst
    τ hfirst

theorem inversionFinsetInvolving_secondChoice_card_of_first_zero {n : ℕ}
    (τ : Ranking n) (hfirst : firstChoice τ = 0) :
    (inversionFinsetInvolving (Equiv.refl (Candidate n)) τ
      (secondChoice τ)).card =
      (secondChoice τ : ℕ) - 1 :=
  EconCSLib.SocialChoice.Ranking.inversionFinsetInvolving_secondChoice_card_of_first_zero
    τ hfirst

theorem cycleRange_lt_cycleRange_iff_of_ne {n : ℕ}
    (r a b : Candidate n) (ha : a ≠ r) (hb : b ≠ r) :
    Fin.cycleRange r a < Fin.cycleRange r b ↔ a < b :=
  EconCSLib.SocialChoice.Ranking.cycleRange_lt_cycleRange_iff_of_ne
    r a b ha hb

theorem cycleIcc_one_apply_of_ne {n : ℕ}
    {s x : Candidate n} (hx : x ≠ s) :
    Fin.cycleIcc (1 : Candidate n) s x =
      if x < (1 : Candidate n) then x else if x < s then x + 1 else x :=
  EconCSLib.SocialChoice.Ranking.cycleIcc_one_apply_of_ne hx

theorem cycleIcc_one_val_of_ne {n : ℕ}
    {s x : Candidate n} (hx : x ≠ s) :
    ((Fin.cycleIcc (1 : Candidate n) s x) : ℕ) =
      if x < (1 : Candidate n) then (x : ℕ)
      else if x < s then (x : ℕ) + 1
      else (x : ℕ) :=
  EconCSLib.SocialChoice.Ranking.cycleIcc_one_val_of_ne hx

theorem cycleIcc_one_lt_cycleIcc_one_iff_of_ne {n : ℕ}
    (s a b : Candidate n) (ha : a ≠ s) (hb : b ≠ s) :
    Fin.cycleIcc (1 : Candidate n) s a <
        Fin.cycleIcc (1 : Candidate n) s b ↔
      a < b :=
  EconCSLib.SocialChoice.Ranking.cycleIcc_one_lt_cycleIcc_one_iff_of_ne
    s a b ha hb

theorem invertedPair_refl_trans_cycleIcc_one_iff_of_ne {n : ℕ}
    (τ : Ranking n) (s a b : Candidate n) (ha : a ≠ s) (hb : b ≠ s) :
    invertedPair (Equiv.refl (Candidate n))
        (τ.trans (Fin.cycleIcc (1 : Candidate n) s))
        (Fin.cycleIcc (1 : Candidate n) s a,
          Fin.cycleIcc (1 : Candidate n) s b) ↔
      invertedPair (Equiv.refl (Candidate n)) τ (a, b) :=
  EconCSLib.SocialChoice.Ranking.invertedPair_refl_trans_cycleIcc_one_iff_of_ne
    τ s a b ha hb

theorem inversionFinsetNotInvolving_secondChoice_card_eq_cycleIcc_one {n : ℕ}
    (τ : Ranking n) (hfirst : firstChoice τ = 0) :
    (inversionFinsetNotInvolving (Equiv.refl (Candidate n)) τ
        (secondChoice τ)).card =
      (inversionFinset (Equiv.refl (Candidate n))
        (τ.trans (Fin.cycleIcc (1 : Candidate n) (secondChoice τ)))).card :=
  EconCSLib.SocialChoice.Ranking.inversionFinsetNotInvolving_secondChoice_card_eq_cycleIcc_one
    τ hfirst

theorem kendallTau_eq_secondChoice_sub_one_add_cycleIcc_one {n : ℕ}
    (τ : Ranking n) (hfirst : firstChoice τ = 0) :
    kendallTau (Equiv.refl (Candidate n)) τ =
      ((secondChoice τ : ℕ) - 1) +
        kendallTau (Equiv.refl (Candidate n))
          (τ.trans (Fin.cycleIcc (1 : Candidate n) (secondChoice τ))) :=
  EconCSLib.SocialChoice.Ranking.kendallTau_eq_secondChoice_sub_one_add_cycleIcc_one
    τ hfirst

@[simp] theorem firstChoice_trans {n : ℕ}
    (π e : Ranking n) :
    firstChoice (π.trans e) = e (firstChoice π) :=
  EconCSLib.SocialChoice.Ranking.firstChoice_trans π e

@[simp] theorem secondChoice_trans {n : ℕ}
    (π e : Ranking n) :
    secondChoice (π.trans e) = e (secondChoice π) :=
  EconCSLib.SocialChoice.Ranking.secondChoice_trans π e

@[simp] theorem rankOf_trans_apply {n : ℕ}
    (π e : Ranking n) (c : Candidate n) :
    rankOf (π.trans e) (e c) = rankOf π c :=
  EconCSLib.SocialChoice.Ranking.rankOf_trans_apply π e c

def rankingRightTransEquiv {n : ℕ} (e : Ranking n) :
    Ranking n ≃ Ranking n :=
  EconCSLib.SocialChoice.Ranking.rankingRightTransEquiv e

theorem invertedPair_refl_trans_cycleRange_iff_of_ne {n : ℕ}
    (τ : Ranking n) (r a b : Candidate n) (ha : a ≠ r) (hb : b ≠ r) :
    invertedPair (Equiv.refl (Candidate n)) (τ.trans (Fin.cycleRange r))
        (Fin.cycleRange r a, Fin.cycleRange r b) ↔
      invertedPair (Equiv.refl (Candidate n)) τ (a, b) :=
  EconCSLib.SocialChoice.Ranking.invertedPair_refl_trans_cycleRange_iff_of_ne
    τ r a b ha hb

@[simp] theorem firstChoice_trans_cycleRange_firstChoice {n : ℕ}
    (τ : Ranking n) :
    firstChoice (τ.trans (Fin.cycleRange (firstChoice τ))) = 0 :=
  EconCSLib.SocialChoice.Ranking.firstChoice_trans_cycleRange_firstChoice τ

theorem inversionFinsetNotInvolving_firstChoice_card_eq_cycleRange {n : ℕ}
    (τ : Ranking n) :
    (inversionFinsetNotInvolving (Equiv.refl (Candidate n)) τ
        (firstChoice τ)).card =
      (inversionFinset (Equiv.refl (Candidate n))
        (τ.trans (Fin.cycleRange (firstChoice τ)))).card :=
  EconCSLib.SocialChoice.Ranking.inversionFinsetNotInvolving_firstChoice_card_eq_cycleRange
    τ

theorem kendallTau_eq_firstChoice_add_cycleRange {n : ℕ}
    (τ : Ranking n) :
    kendallTau (Equiv.refl (Candidate n)) τ =
      (firstChoice τ : ℕ) +
        kendallTau (Equiv.refl (Candidate n))
          (τ.trans (Fin.cycleRange (firstChoice τ))) :=
  EconCSLib.SocialChoice.Ranking.kendallTau_eq_firstChoice_add_cycleRange τ

theorem kendallTau_center_trans {n : ℕ}
    (ρ τ : Ranking n) :
    kendallTau ρ (τ.trans ρ) =
      kendallTau (Equiv.refl (Candidate n)) τ :=
  EconCSLib.SocialChoice.Ranking.kendallTau_center_trans ρ τ

theorem apply_ne_apply_of_ne {n : ℕ} (π : Ranking n) {i j : Candidate n}
    (hij : i ≠ j) : π i ≠ π j :=
  EconCSLib.SocialChoice.Ranking.apply_ne_apply_of_ne π hij

theorem rankOf_center_first_lt_second {n : ℕ} (ρ : Ranking n) :
    rankOf ρ (firstChoice ρ) < rankOf ρ (secondChoice ρ) :=
  EconCSLib.SocialChoice.Ranking.rankOf_center_first_lt_second ρ

def StrictlyOrderedBy {n : ℕ} (ρ : Ranking n) (value : Candidate n → ℝ) : Prop :=
  ∀ {a b : Candidate n}, rankOf ρ a < rankOf ρ b → value b < value a

def WeaklyOrderedBy {n : ℕ} (ρ : Ranking n) (value : Candidate n → ℝ) : Prop :=
  ∀ {a b : Candidate n}, rankOf ρ a < rankOf ρ b → value b ≤ value a

theorem center_valueGap_pos_of_strictlyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy ρ value) :
    0 < valueGap value ρ := by
  have hvalue' :
      EconCSLib.SocialChoice.Ranking.StrictlyOrderedBy ρ value := by
    intro a b hab
    exact hvalue (by
      simpa [rankOf, EconCSLib.SocialChoice.Ranking.rankOf] using hab)
  simpa [valueGap, EconCSLib.SocialChoice.Ranking.valueGap,
    EconCSLib.SocialChoice.Ranking.topTwoValueGap] using
    EconCSLib.SocialChoice.Ranking.center_topTwoValueGap_pos_of_strictlyOrderedBy
      (ρ := ρ) (value := value) hvalue'

theorem center_valueGap_nonneg_of_weaklyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : WeaklyOrderedBy ρ value) :
    0 ≤ valueGap value ρ := by
  have hvalue' :
      EconCSLib.SocialChoice.Ranking.WeaklyOrderedBy ρ value := by
    intro a b hab
    exact hvalue (by
      simpa [rankOf, EconCSLib.SocialChoice.Ranking.rankOf] using hab)
  simpa [valueGap, EconCSLib.SocialChoice.Ranking.valueGap,
    EconCSLib.SocialChoice.Ranking.topTwoValueGap] using
    EconCSLib.SocialChoice.Ranking.center_topTwoValueGap_nonneg_of_weaklyOrderedBy
      (ρ := ρ) (value := value) hvalue'

end KR21Monoculture
