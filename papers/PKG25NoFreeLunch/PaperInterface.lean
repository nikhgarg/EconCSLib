import PKG25NoFreeLunch.MainTheorems

/-!
# Human-Facing Paper Interface: A No Free Lunch Theorem for Human-AI Collaboration

This file exposes the compact source-facing definitions and theorem skeleton
for PKG25.  The implementation proofs live in `MainTheorems.lean`.
-/

namespace PKG25NoFreeLunch

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
