import EconCSLib.SocialChoice.Ranking.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Score-Induced Three-Candidate Rankings

Reusable finite ranking maps induced by three real scores, ordered descending
by score and with deterministic lower-index tie-breaking.

This module is deliberately probability-free. Continuous RUM files can prove
measurability or no-tie facts around these maps in their own measure layer.
-/

namespace EconCSLib
namespace SocialChoice
namespace Ranking

/-! ## Three-score order predicates -/

/-- Candidate `0` is weakly first among three realized scores. -/
def rum3TopFirstByScores (s1 s2 s3 : ℝ) : Prop :=
  s2 ≤ s1 ∧ s3 ≤ s1

/-- Candidate `1` strictly beats candidate `0` and weakly beats candidate `2`. -/
def rum3MiddleBeatsTopByScores (s1 s2 s3 : ℝ) : Prop :=
  s1 < s2 ∧ s3 ≤ s2

/-- Candidate `2` is weakly first among three realized scores. -/
def rum3BottomFirstByScores (s1 s2 s3 : ℝ) : Prop :=
  s1 ≤ s3 ∧ s2 ≤ s3

/-- Three realized scores have no pairwise ties. -/
def rum3NoTiesByScores (s1 s2 s3 : ℝ) : Prop :=
  s1 ≠ s2 ∧ s1 ≠ s3 ∧ s2 ≠ s3

/-! ## Concrete three-candidate rankings -/

/-- The concrete ranking `[0, 1, 2]`. -/
def rum3Ranking012 : Ranking 1 :=
  Equiv.refl (Candidate 1)

/-- The concrete ranking `[0, 2, 1]`. -/
def rum3Ranking021 : Ranking 1 :=
  Equiv.swap (1 : Candidate 1) (2 : Candidate 1)

/-- The concrete ranking `[1, 0, 2]`. -/
def rum3Ranking102 : Ranking 1 :=
  Equiv.swap (0 : Candidate 1) (1 : Candidate 1)

/-- The concrete ranking `[1, 2, 0]`. -/
def rum3Ranking120 : Ranking 1 :=
  (Equiv.swap (1 : Candidate 1) (2 : Candidate 1)).trans
    (Equiv.swap (0 : Candidate 1) (1 : Candidate 1))

/-- The concrete ranking `[2, 0, 1]`. -/
def rum3Ranking201 : Ranking 1 :=
  (Equiv.swap (0 : Candidate 1) (2 : Candidate 1)).trans
    (Equiv.swap (0 : Candidate 1) (1 : Candidate 1))

/-- The concrete ranking `[2, 1, 0]`. -/
def rum3Ranking210 : Ranking 1 :=
  Equiv.swap (0 : Candidate 1) (2 : Candidate 1)

@[simp] theorem rum3Ranking012_apply_zero :
    rum3Ranking012 (0 : Candidate 1) = (0 : Candidate 1) := rfl

@[simp] theorem rum3Ranking012_apply_one :
    rum3Ranking012 (1 : Candidate 1) = (1 : Candidate 1) := rfl

@[simp] theorem rum3Ranking012_apply_two :
    rum3Ranking012 (2 : Candidate 1) = (2 : Candidate 1) := rfl

@[simp] theorem rum3Ranking021_apply_zero :
    rum3Ranking021 (0 : Candidate 1) = (0 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking021_apply_one :
    rum3Ranking021 (1 : Candidate 1) = (2 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking021_apply_two :
    rum3Ranking021 (2 : Candidate 1) = (1 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking102_apply_zero :
    rum3Ranking102 (0 : Candidate 1) = (1 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking102_apply_one :
    rum3Ranking102 (1 : Candidate 1) = (0 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking102_apply_two :
    rum3Ranking102 (2 : Candidate 1) = (2 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking120_apply_zero :
    rum3Ranking120 (0 : Candidate 1) = (1 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking120_apply_one :
    rum3Ranking120 (1 : Candidate 1) = (2 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking120_apply_two :
    rum3Ranking120 (2 : Candidate 1) = (0 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking201_apply_zero :
    rum3Ranking201 (0 : Candidate 1) = (2 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking201_apply_one :
    rum3Ranking201 (1 : Candidate 1) = (0 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking201_apply_two :
    rum3Ranking201 (2 : Candidate 1) = (1 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking210_apply_zero :
    rum3Ranking210 (0 : Candidate 1) = (2 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking210_apply_one :
    rum3Ranking210 (1 : Candidate 1) = (1 : Candidate 1) := by
  decide

@[simp] theorem rum3Ranking210_apply_two :
    rum3Ranking210 (2 : Candidate 1) = (0 : Candidate 1) := by
  decide

/-! ## Ranking by score -/

/--
Ranking induced by three realized scores, ordered descending by score and
breaking ties in favor of the lower-indexed candidate.
-/
noncomputable def rum3RankByScores (s1 s2 s3 : ℝ) : Ranking 1 :=
  if h0 : s2 ≤ s1 ∧ s3 ≤ s1 then
    if s3 ≤ s2 then rum3Ranking012 else rum3Ranking021
  else if h1 : s1 < s2 ∧ s3 ≤ s2 then
    if s3 ≤ s1 then rum3Ranking102 else rum3Ranking120
  else
    if s2 ≤ s1 then rum3Ranking201 else rum3Ranking210

/-- Ranking map induced by three score-coordinate functions. -/
noncomputable def rum3RankByScoreFns {Ω : Type*}
    (r1 r2 r3 : Ω → ℝ) : Ω → Ranking 1 :=
  fun ω => rum3RankByScores (r1 ω) (r2 ω) (r3 ω)

@[simp] theorem firstChoice_rum3RankByScores (s1 s2 s3 : ℝ) :
    firstChoice (rum3RankByScores s1 s2 s3) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then (0 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then (1 : Candidate 1)
      else (2 : Candidate 1) := by
  unfold rum3RankByScores firstChoice
  split_ifs <;> simp

@[simp] theorem secondChoice_rum3RankByScores (s1 s2 s3 : ℝ) :
    secondChoice (rum3RankByScores s1 s2 s3) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then
        if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then
        if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1)
      else
        if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1) := by
  unfold rum3RankByScores secondChoice
  split_ifs <;> simp

@[simp] theorem rum3RankByScores_apply_zero (s1 s2 s3 : ℝ) :
    rum3RankByScores s1 s2 s3 (0 : Candidate 1) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then (0 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then (1 : Candidate 1)
      else (2 : Candidate 1) := by
  simpa [firstChoice] using firstChoice_rum3RankByScores s1 s2 s3

@[simp] theorem rum3RankByScores_apply_one (s1 s2 s3 : ℝ) :
    rum3RankByScores s1 s2 s3 (1 : Candidate 1) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then
        if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then
        if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1)
      else
        if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1) := by
  simpa [secondChoice] using secondChoice_rum3RankByScores s1 s2 s3

@[simp] theorem bestRemainingAfter_rum3RankByScores_remove0
    (s1 s2 s3 : ℝ) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
      if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1) := by
  change
    (if firstChoice (rum3RankByScores s1 s2 s3) = (0 : Candidate 1) then
      secondChoice (rum3RankByScores s1 s2 s3)
    else firstChoice (rum3RankByScores s1 s2 s3)) =
      if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1)
  by_cases h32 : s3 ≤ s2
  · by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
    · simp [h0, h32]
    · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
      · simp [h0, h1, h32]
      · exfalso
        by_cases h21 : s2 ≤ s1
        · exact h0 ⟨h21, le_trans h32 h21⟩
        · exact h1 ⟨lt_of_not_ge h21, h32⟩
  · by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
    · simp [h0, h32]
    · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
      · exact False.elim (h32 h1.2)
      · by_cases h21 : s2 ≤ s1
        · have h31 : ¬ s3 ≤ s1 := by
            intro h31
            exact h0 ⟨h21, h31⟩
          simp [h0, h1, h21, h32, h31]
        · simp [h0, h1, h21, h32]

@[simp] theorem bestRemainingAfter_rum3RankByScores_remove1
    (s1 s2 s3 : ℝ) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (1 : Candidate 1) =
      if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1) := by
  change
    (if firstChoice (rum3RankByScores s1 s2 s3) = (1 : Candidate 1) then
      secondChoice (rum3RankByScores s1 s2 s3)
    else firstChoice (rum3RankByScores s1 s2 s3)) =
      if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1)
  by_cases h31 : s3 ≤ s1
  · by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
    · simp [h0, h31]
    · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
      · simp [h0, h1, h31]
      · by_cases h21 : s2 ≤ s1
        · exact False.elim (h0 ⟨h21, h31⟩)
        · exact False.elim
            (h1 ⟨lt_of_not_ge h21,
              le_trans h31 (le_of_lt (lt_of_not_ge h21))⟩)
  · by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
    · exact False.elim (h31 h0.2)
    · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
      · simp [h0, h1, h31]
      · by_cases h21 : s2 ≤ s1 <;>
          simp [h0, h1, h21, h31]

@[simp] theorem bestRemainingAfter_rum3RankByScores_remove2
    (s1 s2 s3 : ℝ) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (2 : Candidate 1) =
      if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1) := by
  change
    (if firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1) then
      secondChoice (rum3RankByScores s1 s2 s3)
    else firstChoice (rum3RankByScores s1 s2 s3)) =
      if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1)
  by_cases h21 : s2 ≤ s1
  · by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
    · simp [h0, h21]
    · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
      · exact False.elim (not_lt_of_ge h21 h1.1)
      · have h31 : ¬ s3 ≤ s1 := by
          intro h31
          exact h0 ⟨h21, h31⟩
        simp [h0, h1, h21, h31]
  · by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
    · exact False.elim (h21 h0.1)
    · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
      · simp [h0, h1, h21]
      · by_cases h31 : s3 ≤ s1
        · have h1' : s1 < s2 ∧ s3 ≤ s2 :=
            ⟨lt_of_not_ge h21, le_trans h31 (le_of_lt (lt_of_not_ge h21))⟩
          exact False.elim (h1 h1')
        · simp [h0, h1, h21]

theorem rum3RankByScores_firstChoice_of_top_scores
    {s1 s2 s3 : ℝ}
    (h : rum3TopFirstByScores s1 s2 s3) :
    firstChoice (rum3RankByScores s1 s2 s3) = (0 : Candidate 1) := by
  rcases h with ⟨h21, h31⟩
  rw [firstChoice_rum3RankByScores]
  simp [h21, h31]

theorem rum3RankByScores_top_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (0 : Candidate 1)) :
    rum3TopFirstByScores s1 s2 s3 := by
  rw [firstChoice_rum3RankByScores] at h
  by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
  · simpa [rum3TopFirstByScores] using h0
  · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
    · simp [h0, h1] at h
    · simp [h0, h1] at h

theorem rum3RankByScores_bottom_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1)) :
    rum3BottomFirstByScores s1 s2 s3 := by
  rw [firstChoice_rum3RankByScores] at h
  by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
  · simp [h0] at h
  · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
    · simp [h0, h1] at h
    · constructor
      · by_contra hnot
        have h31 : s3 < s1 := lt_of_not_ge hnot
        by_cases h21 : s2 ≤ s1
        · exact h0 ⟨h21, le_of_lt h31⟩
        · have h12 : s1 < s2 := lt_of_not_ge h21
          exact h1 ⟨h12, le_trans (le_of_lt h31) (le_of_lt h12)⟩
      · by_contra hnot
        have h32 : s3 < s2 := lt_of_not_ge hnot
        by_cases h12 : s1 < s2
        · exact h1 ⟨h12, le_of_lt h32⟩
        · exact h0 ⟨le_of_not_gt h12,
            le_trans (le_of_lt h32) (le_of_not_gt h12)⟩

theorem rum3RankByScores_firstChoice_of_bottom_scores_of_noTies
    {s1 s2 s3 : ℝ}
    (hnt : rum3NoTiesByScores s1 s2 s3)
    (h : rum3BottomFirstByScores s1 s2 s3) :
    firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1) := by
  rcases hnt with ⟨hne12, hne13, hne23⟩
  rcases h with ⟨h13, h23⟩
  have h31 : ¬ s3 ≤ s1 := by
    intro h31
    exact hne13 (le_antisymm h13 h31)
  have h32 : ¬ s3 ≤ s2 := by
    intro h32
    exact hne23 (le_antisymm h23 h32)
  rw [firstChoice_rum3RankByScores]
  have h0 : ¬(s2 ≤ s1 ∧ s3 ≤ s1) := by
    intro h0
    exact h31 h0.2
  have h1 : ¬(s1 < s2 ∧ s3 ≤ s2) := by
    intro h1
    exact h32 h1.2
  simp [h0, h1]

theorem rum3RankByScores_firstChoice_of_strict_bottom_scores
    {s1 s2 s3 : ℝ}
    (h13 : s1 < s3) (h23 : s2 < s3) :
    firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1) := by
  rw [firstChoice_rum3RankByScores]
  have h0 : ¬(s2 ≤ s1 ∧ s3 ≤ s1) := by
    intro h0
    linarith
  have h1 : ¬(s1 < s2 ∧ s3 ≤ s2) := by
    intro h1
    linarith
  simp [h0, h1]

theorem rum3RankByScores_strict_bottom_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1)) :
    s1 < s3 ∧ s2 < s3 := by
  rw [firstChoice_rum3RankByScores] at h
  by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
  · simp [h0] at h
  · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
    · simp [h0, h1] at h
    · constructor
      · by_contra hnot
        have h31 : s3 ≤ s1 := le_of_not_gt hnot
        by_cases h21 : s2 ≤ s1
        · exact h0 ⟨h21, h31⟩
        · have h12 : s1 < s2 := lt_of_not_ge h21
          exact h1 ⟨h12, le_trans h31 (le_of_lt h12)⟩
      · by_contra hnot
        have h32 : s3 ≤ s2 := le_of_not_gt hnot
        by_cases h12 : s1 < s2
        · exact h1 ⟨h12, h32⟩
        · exact h0 ⟨le_of_not_gt h12, le_trans h32 (le_of_not_gt h12)⟩

theorem rum3RankByScores_middle_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (1 : Candidate 1)) :
    rum3MiddleBeatsTopByScores s1 s2 s3 := by
  rw [firstChoice_rum3RankByScores] at h
  by_cases h0 : s2 ≤ s1 ∧ s3 ≤ s1
  · simp [h0] at h
  · by_cases h1 : s1 < s2 ∧ s3 ≤ s2
    · simpa [rum3MiddleBeatsTopByScores] using h1
    · simp [h0, h1] at h

theorem rum3RankByScores_remove0_eq1_imp_score23
    {s1 s2 s3 : ℝ}
    (h :
      bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
        (1 : Candidate 1)) :
    s3 ≤ s2 := by
  by_contra h32
  simp [h32] at h

theorem rum3RankByScores_remove1_ne0_imp_score13
    {s1 s2 s3 : ℝ}
    (h :
      ¬ bestRemainingAfter (rum3RankByScores s1 s2 s3) (1 : Candidate 1) =
        (0 : Candidate 1)) :
    s1 < s3 := by
  by_contra h31
  exact h (by simp [le_of_not_gt h31])

theorem rum3RankByScores_remove1_eq0_of_score31
    {s1 s2 s3 : ℝ} (h31 : s3 ≤ s1) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (1 : Candidate 1) =
      (0 : Candidate 1) := by
  simp [h31]

theorem rum3RankByScores_remove0_ne1_of_score23_lt
    {s1 s2 s3 : ℝ} (h23 : s2 < s3) :
    ¬ bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
      (1 : Candidate 1) := by
  have h32 : ¬ s3 ≤ s2 := not_le_of_gt h23
  simp [h32]

theorem rum3RankByScores_remove0_eq2_imp_score23_lt
    {s1 s2 s3 : ℝ}
    (h :
      bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
        (2 : Candidate 1)) :
    s2 < s3 := by
  by_contra h23
  have h32 : s3 ≤ s2 := le_of_not_gt h23
  simp [h32] at h

theorem rum3RankByScores_remove0_eq1_of_score32
    {s1 s2 s3 : ℝ} (h32 : s3 ≤ s2) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
      (1 : Candidate 1) := by
  simp [h32]

theorem rum3RankByScores_remove2_eq1_imp_score12_lt
    {s1 s2 s3 : ℝ}
    (h :
      bestRemainingAfter (rum3RankByScores s1 s2 s3) (2 : Candidate 1) =
        (1 : Candidate 1)) :
    s1 < s2 := by
  by_contra h12
  have h21 : s2 ≤ s1 := le_of_not_gt h12
  simp [h21] at h

theorem rum3RankByScores_remove2_eq0_of_score21
    {s1 s2 s3 : ℝ} (h21 : s2 ≤ s1) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (2 : Candidate 1) =
      (0 : Candidate 1) := by
  simp [h21]

end Ranking
end SocialChoice
end EconCSLib
