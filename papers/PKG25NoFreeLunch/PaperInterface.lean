import PKG25NoFreeLunch.MainTheorems

/-!
# Human-Facing Paper Interface: A No Free Lunch Theorem for Human-AI Collaboration

This file exposes the compact source-facing definitions and theorem skeleton
for PKG25.  The implementation proofs live in `MainTheorems.lean`.
-/

namespace PKG25NoFreeLunch

/--
Source Definition 1: a collaboration setting.

The Lean source-facing surface uses finite calibrated collaboration settings,
which are the settings constructed in the paper proof, together with the
embedding into the abstract accuracy surface used by the theorem statement.
-/
abbrev definition_collaboration_setting (n : ℕ) := FiniteCollaborationSetting n

/--
Source definition: the paper rounds predicted probabilities to binary labels
using the convention `round(1/2) = 1`.

Source status: Definition from Section 3, immediately before the individual
accuracy formula.
-/
noncomputable abbrev definition_rounding_convention := roundProb

/--
Source definition: a collaboration strategy is a deterministic function from
`n` calibrated predicted probabilities to a binary classification.

Source status: Definition from Section 3.
-/
abbrev definition_collaboration_strategy (n : ℕ) := CollaborationStrategy n

/--
Source definition: the interior profile domain `(0,1)^n` used in the
non-collaboration definition.

Source status: Definition 4 constrains the strategy only on `(0,1)^n`; boundary
predictions `0` and `1` are intentionally exempt in the source.
-/
abbrev definition_interior_prediction_profile {n : ℕ} := @Interior n

/--
Source Definition 5: correctness of a prediction at a point.

At a point with conditional label probability `eta`, a prediction is correct
exactly when it equals the rounded Bayes-optimal label.
-/
def definition_correct_on (prediction : Label) (eta : ℝ) : Prop :=
  prediction = roundProb eta

/--
Source Definition 5: incorrectness of a prediction at a point.
-/
def definition_incorrect_on (prediction : Label) (eta : ℝ) : Prop :=
  prediction ≠ roundProb eta

/--
Source Definition 5: two agents or strategies agree at a point when their
binary predictions are equal.
-/
def definition_agree_on (prediction1 prediction2 : Label) : Prop :=
  prediction1 = prediction2

/--
Source Definition 5: two agents or strategies disagree at a point when their
binary predictions differ.
-/
def definition_disagree_on (prediction1 prediction2 : Label) : Prop :=
  prediction1 ≠ prediction2

/--
Source definition: a strategy is non-collaborative if it defers to one fixed
agent away from the tie point and uses one fixed tie value on `p_k = 1/2`, for
all prediction profiles in `(0,1)^n`.

Source status: Definition 4.
-/
abbrev definition_non_collaborative {n : ℕ} := @NonCollaborative n

/--
Source definition: reliability means the strategy is at least as accurate as
the least accurate calibrated agent in every collaboration setting.

Source status: Definition 3.  The finite adversarial settings used in the proof
embed into this source-style setting surface in `MainTheorems.lean`.
-/
abbrev definition_reliable {n : ℕ} := @Reliable n

/--
Proposition 6: linear combinations of finite collaboration settings preserve
agent and strategy accuracies componentwise.
-/
theorem proposition6_linear_combination_settings
    {n ell : ℕ} (S : Fin ell → FiniteCollaborationSetting n) (w : Fin ell → ℝ)
    (hw_nonneg : ∀ r : Fin ell, 0 ≤ w r)
    (hw_sum : ∑ r : Fin ell, w r = 1) :
    ∃ Smix : FiniteCollaborationSetting n,
      (∀ i : Fin n,
        Smix.agentAccuracy i = ∑ r : Fin ell, w r * (S r).agentAccuracy i) ∧
      (∀ C : CollaborationStrategy n,
        Smix.strategyAccuracy C = ∑ r : Fin ell, w r * (S r).strategyAccuracy C) := by
  refine ⟨FiniteCollaborationSetting.mix S w hw_nonneg hw_sum, ?_, ?_⟩
  · intro i
    exact FiniteCollaborationSetting.agentAccuracy_mix S w hw_nonneg hw_sum i
  · intro C
    exact FiniteCollaborationSetting.strategyAccuracy_mix S w hw_nonneg hw_sum C

/--
Lemma 8: if a collaboration strategy disagrees with agent `k` away from the
tie point, the source construction gives a finite collaboration setting where
agent `k` is strictly more accurate and every agent is at least as accurate as
the strategy.
-/
theorem lemma8_bad_tuple_counterexample_setting
    {n : ℕ} {C : CollaborationStrategy n} {p : Fin n → ℝ} (hp : Interior p)
    {k : Fin n} (hhalf_ne : p k ≠ (1 : ℝ) / 2)
    (hbad : C p ≠ roundProb (p k)) :
    WeakCounterexampleFor
      (FiniteCollaborationSetting.toAccuracySurface C
        (part1Setting (C p) p hp)) k := by
  exact part1Setting_weakCounterexample hp hhalf_ne hbad

/--
Proposition 7: reliability over all collaboration settings forces deferral to
one fixed agent away from the tie point.
-/
theorem proposition7_reliability_forces_fixed_deferral
    {n : ℕ} [Nonempty (Fin n)] (C : CollaborationStrategy n) :
    Reliable C → ∃ k : Fin n, DefersAwayFromHalf C k := by
  intro hrel
  exact reliableFinite_exists_defers_away (C := C) (reliableFinite_of_reliable hrel)

/--
Proposition 9: for the same fixed agent, reliability forces one fixed tie label
on the `p_k = 1 / 2` slice.
-/
theorem proposition9_reliability_forces_fixed_tie_label
    {n : ℕ} [Nonempty (Fin n)] (C : CollaborationStrategy n) (k : Fin n)
    (hrel : Reliable C) (hk : DefersAwayFromHalf C k) :
    ∃ α : Label, ConstantOnHalfSlice C k α := by
  exact reliableFinite_constant_on_half (C := C) (reliableFinite_of_reliable hrel) hk

/--
Main theorem: every reliable deterministic collaboration strategy is
non-collaborative.  Equivalently, there is one fixed agent `k` and one fixed tie
label `α` such that the strategy defers to `k` away from `p_k = 1/2` and uses
`α` on the `p_k = 1/2` slice, for all interior prediction profiles.

Source status: Theorem 1.  Proposition 1, the counterexample lemma, the linear
combination construction, and Proposition 2's two auxiliary settings are proved
in `MainTheorems.lean`; no proposition-level certificates are assumed here.
-/
theorem theorem_main_no_free_lunch {n : ℕ} [Nonempty (Fin n)]
    (C : CollaborationStrategy n) :
    Reliable C → NonCollaborative C :=
  main_no_free_lunch C

end PKG25NoFreeLunch
