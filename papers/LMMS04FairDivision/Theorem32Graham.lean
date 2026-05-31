import Mathlib.Tactic

/-!
# LMMS Theorem 3.2: Graham scheduling certificate

Theorem 3.2 is cited from the scheduling literature: Graham's greedy
algorithm has approximation factor `1.4` for the ratio of maximum load to
minimum load on identical machines.  This file therefore does not reprove the
scheduling theorem.  It packages the cited result as a clean certificate and
proves the LMMS fair-division wrapper: in the identical-utilities case, a
bound on the scheduling max-load/min-load ratio gives the same pairwise
envy-ratio bound.
-/

namespace LMMS04FairDivision
namespace Theorem32

open scoped BigOperators

noncomputable section

/-- Identical-utilities bundle load: the common value of a bundle of goods. -/
def commonLoad {Item : Type*} (v : Item → ℝ) (S : Finset Item) : ℝ :=
  S.sum v

/-- The scheduling ratio used in the source: maximum load divided by minimum load. -/
def loadRatio (minLoad maxLoad : ℝ) : ℝ :=
  maxLoad / minLoad

/--
The pairwise envy-ratio bound in the identical-utilities view.  Player `p`'s
value for player `q`'s bundle is `load q`, while her value for her own bundle
is `load p`.
-/
def IdenticalUtilitiesEnvyRatioBound {Agent : Type*}
    (load : Agent → ℝ) (rho : ℝ) : Prop :=
  ∀ p q : Agent, load q / load p ≤ rho

/--
A scheduling extrema certificate for a concrete identical-machine allocation:
`minLoad` and `maxLoad` are positive/nonnegative enclosing extrema for all
machine loads.
-/
structure SchedulingExtremaCertificate {Agent : Type*}
    (load : Agent → ℝ) where
  minLoad : ℝ
  maxLoad : ℝ
  minLoad_pos : 0 < minLoad
  maxLoad_nonneg : 0 ≤ maxLoad
  load_lower : ∀ i : Agent, minLoad ≤ load i
  load_upper : ∀ i : Agent, load i ≤ maxLoad

namespace SchedulingExtremaCertificate

variable {Agent : Type*} {load : Agent → ℝ}

/--
Extrema translation: every pairwise identical-utilities envy ratio is bounded
by the scheduling max-load/min-load ratio.
-/
theorem pairwise_ratio_le_loadRatio
    (C : SchedulingExtremaCertificate load) (p q : Agent) :
    load q / load p ≤ loadRatio C.minLoad C.maxLoad := by
  have hp_pos : 0 < load p := lt_of_lt_of_le C.minLoad_pos (C.load_lower p)
  calc
    load q / load p ≤ C.maxLoad / load p :=
      div_le_div_of_nonneg_right (C.load_upper q) (le_of_lt hp_pos)
    _ ≤ C.maxLoad / C.minLoad := by
      rw [div_le_div_iff₀ hp_pos C.minLoad_pos]
      nlinarith [C.maxLoad_nonneg, C.load_lower p]
    _ = loadRatio C.minLoad C.maxLoad := rfl

/--
If the scheduling load ratio is at most `rho`, then the corresponding
identical-utilities allocation has pairwise envy-ratio at most `rho`.
-/
theorem envyRatioBound_of_loadRatio_bound
    (C : SchedulingExtremaCertificate load) {rho : ℝ}
    (hratio : loadRatio C.minLoad C.maxLoad ≤ rho) :
    IdenticalUtilitiesEnvyRatioBound load rho := by
  intro p q
  exact le_trans (C.pairwise_ratio_le_loadRatio p q) hratio

end SchedulingExtremaCertificate

/-- Graham's cited approximation factor `1.4`, represented exactly as `14 / 10`. -/
def grahamApproximationFactor : ℝ :=
  (14 : ℝ) / 10

theorem grahamApproximationFactor_eq_seven_fifths :
    grahamApproximationFactor = (7 : ℝ) / 5 := by
  norm_num [grahamApproximationFactor]

/--
Certificate form of the cited Graham theorem used by LMMS Theorem 3.2.

The field `approximation` is the imported scheduling fact: the Graham output's
load ratio is at most `1.4` times the optimal load ratio for the same
identical-machine instance.
-/
structure Graham14SchedulingApproximationCertificate {Agent : Type*}
    (load : Agent → ℝ) (optimalRatio : ℝ) where
  extrema : SchedulingExtremaCertificate load
  approximation :
    loadRatio extrema.minLoad extrema.maxLoad ≤
      grahamApproximationFactor * optimalRatio

/--
LMMS Theorem 3.2 wrapper: a Graham scheduling approximation certificate gives
the stated `1.4` approximation bound for pairwise envy-ratio in the
identical-utilities fair-division instance.
-/
theorem theorem32_graham_certificate_to_envy_ratio_bound
    {Agent : Type*} {load : Agent → ℝ} {optimalRatio : ℝ}
    (C : Graham14SchedulingApproximationCertificate load optimalRatio) :
    IdenticalUtilitiesEnvyRatioBound load
      (grahamApproximationFactor * optimalRatio) := by
  exact C.extrema.envyRatioBound_of_loadRatio_bound C.approximation

/--
Bundle-level version of the Theorem 3.2 wrapper for a common additive utility
`v` and an allocation represented by `bundleOf`.
-/
theorem theorem32_graham_bundle_certificate_to_envy_ratio_bound
    {Agent Item : Type*} {v : Item → ℝ} {bundleOf : Agent → Finset Item}
    {optimalRatio : ℝ}
    (C :
      Graham14SchedulingApproximationCertificate
        (fun i : Agent => commonLoad v (bundleOf i)) optimalRatio) :
    IdenticalUtilitiesEnvyRatioBound
      (fun i : Agent => commonLoad v (bundleOf i))
      (grahamApproximationFactor * optimalRatio) := by
  exact theorem32_graham_certificate_to_envy_ratio_bound C

end

end Theorem32
end LMMS04FairDivision
