import AccuracyDiversity.Examples
import AccuracyDiversity.Uniform

open scoped BigOperators

/-!
# Paper-Facing Theorems: Reconciling the Accuracy-Diversity Trade-off

This file is the public theorem interface for the accuracy-diversity
formalization. Detailed allocation, representation, Bernoulli, and exchange
lemmas live in the sibling files.
-/

namespace AccuracyDiversity

namespace ConsumptionModel

/--
Finite optimizer existence for a fixed slate size.

Because count allocations of total `N` form a finite search space, every
consumption-constrained model over a nonempty finite type space has an
objective-maximizing allocation.
-/
theorem paper_finite_optimum_exists
    {T : ℕ} [Nonempty (ItemType T)] (M : ConsumptionModel T) (N : ℕ) :
    ∃ a : CountAllocation T, M.IsOptimalAtTotal N a := by
  exact M.exists_isOptimalAtTotal N

/--
Finite exchange-improvement theorem.

If moving one recommendation from `src` to `dst` loses no more weighted marginal
value than it gains, then the consumption-constrained objective weakly improves.
-/
theorem paper_finite_exchange_improvement
    {T : ℕ} (M : ConsumptionModel T) :
    M.ExchangeImprovementTarget := by
  exact M.exchangeImprovementTarget

/--
Finite first-order condition for optimal count allocations.

At a finite optimum, the weighted forward marginal of any destination is at most
the weighted backward marginal of any positive source.
-/
theorem paper_finite_optimum_first_order_condition
    {T : ℕ} (M : ConsumptionModel T) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : M.IsOptimalAtTotal N a) (hne : src ≠ dst)
    (hcan : DecisionCore.Allocation.CanMoveOne a src) :
    M.weightedForwardMarginal dst (a.count dst) ≤
      M.weightedBackwardMarginal src (a.count src) := by
  exact M.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
    N hopt hne hcan

end ConsumptionModel

namespace BernoulliSatisfactionModel

/--
Bernoulli fixed-total optimizer existence.

The finite optimizer-existence theorem applies directly to the Bernoulli
satisfaction specialization of the consumption model.
-/
theorem paper_bernoulli_finite_optimum_exists
    {T : ℕ} [Nonempty (ItemType T)]
    (B : BernoulliSatisfactionModel T) (N : ℕ) :
    ∃ a : CountAllocation T, B.toConsumptionModel.IsOptimalAtTotal N a := by
  exact B.toConsumptionModel.exists_isOptimalAtTotal N

/--
Bernoulli specialization of the finite first-order condition.

For one-consumption Bernoulli satisfaction, an optimal allocation cannot have a
destination's Bernoulli marginal exceed a positive source's last-item marginal.
-/
theorem paper_bernoulli_optimum_first_order_condition
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a) (hne : src ≠ dst)
    (hcan : DecisionCore.Allocation.CanMoveOne a src) :
    B.likelihood dst * B.successProb dst *
        (1 - B.successProb dst) ^ (a.count dst) ≤
      B.likelihood src * B.successProb src *
        (1 - B.successProb src) ^ (a.count src - 1) := by
  exact B.forwardMarginal_le_backwardMarginal_of_optimum N hopt hne hcan

/--
Finite i.i.d. Bernoulli equal-representation balance theorem.

For identical Bernoulli item types, every finite optimum has pairwise type
counts differing by at most one.
-/
theorem paper_iid_bernoulli_optimum_pairwise_balanced
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a)
    (hlike : ∀ i j : ItemType T, B.likelihood i = B.likelihood j)
    (hprob : ∀ i j : ItemType T, B.successProb i = B.successProb j)
    (hlike_pos : ∀ i : ItemType T, 0 < B.likelihood i)
    (hprob_pos : ∀ i : ItemType T, 0 < B.successProb i)
    (hprob_lt_one : ∀ i : ItemType T, B.successProb i < 1) :
    ∀ src dst : ItemType T, a.count src ≤ a.count dst + 1 := by
  exact B.pairwise_count_le_succ_of_symmetric_optimum
    N hopt hlike hprob hlike_pos hprob_pos hprob_lt_one

/--
Finite i.i.d. Bernoulli `0`-homogeneity theorem.

For identical Bernoulli item types and positive slate size `N`, every finite
optimum has each type's recommendation share within `1 / N` of the uniform
target share. This is the finite exact-count version of the paper's
zero-homogeneity conclusion for i.i.d. Bernoulli item values.
-/
theorem paper_iid_bernoulli_optimum_uniform_homogeneity
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T}
    (hNpos : 0 < N)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a)
    (hlike : ∀ i j : ItemType T, B.likelihood i = B.likelihood j)
    (hprob : ∀ i j : ItemType T, B.successProb i = B.successProb j)
    (hlike_pos : ∀ i : ItemType T, 0 < B.likelihood i)
    (hprob_pos : ∀ i : ItemType T, 0 < B.successProb i)
    (hprob_lt_one : ∀ i : ItemType T, B.successProb i < 1) :
    (uniformProfile T).Approx a (1 / (N : ℝ)) := by
  have hbal :
      ∀ src dst : ItemType T, a.count src ≤ a.count dst + 1 :=
    B.pairwise_count_le_succ_of_symmetric_optimum
      N hopt hlike hprob hlike_pos hprob_pos hprob_lt_one
  exact uniformProfile_approx_of_pairwise_balanced_counts a hopt.1 hNpos hbal

end BernoulliSatisfactionModel

/--
Uniform `[0,1]`, `k = 1` finite first-order condition.

This is the exact marginal inequality used in the proof of Proposition 2 for
the special case where the user consumes one item: at a finite optimum, no
valid one-item exchange can have larger weighted uniform-order-statistic gain
than loss.
-/
theorem paper_uniform_top_one_optimum_first_order_condition
    {T : ℕ} (likelihood : ItemType T → ℝ) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hne : src ≠ dst)
    (hcan : DecisionCore.Allocation.CanMoveOne a src) :
    likelihood dst *
        (1 / ((a.count dst + 1 : ℝ) * (a.count dst + 2 : ℝ))) ≤
      likelihood src *
        (1 / ((a.count src : ℝ) * (a.count src + 1 : ℝ))) := by
  exact UniformTopOne.forwardMarginal_le_backwardMarginal_of_optimum
    likelihood N hopt hne hcan

/--
Proposition 2 square-root homogeneity bridge.

If an integer allocation is within `C` items of the real square-root target
counts, then its representation shares are within `C / N` of the paper's
`1/2`-homogeneity target.
-/
theorem paper_uniform_sqrt_homogeneity_of_count_closeness
    {T : ℕ} (likelihood : ItemType T → ℝ) (a : CountAllocation T)
    {N : ℕ} {C : ℝ}
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0)
    (hN : DecisionCore.Allocation.total a = N) (hNpos : 0 < N)
    (hclose :
      ∀ t,
        |(a.count t : ℝ) -
          (N : ℝ) *
            (Real.sqrt (likelihood t) /
              ∑ i : ItemType T, Real.sqrt (likelihood i))| ≤ C) :
    (sqrtLikelihoodProfile likelihood).Approx a (C / (N : ℝ)) := by
  refine sqrtLikelihoodProfile.approx_of_count_abs_error
    likelihood a hN hNpos ?_
  intro t
  simpa [sqrtLikelihoodProfile.targetShare_eq likelihood t hnorm] using hclose t

/--
Appendix D.5 finite rounding combinatorics.

This is the paper's rounding lemma stripped of its analytic premise. Once the
real-relaxation proof rules out high/low crossings around integer floor
anchors, this theorem gives the count-closeness bound needed by Proposition 2.
-/
theorem paper_rounding_count_close_of_no_crossing
    {T : ℕ} (a anchor : CountAllocation T) {N B : ℕ}
    (ha : DecisionCore.Allocation.total a = N)
    (hanchor : DecisionCore.Allocation.total anchor = B)
    (hBle : B ≤ N)
    (hNlt : N < B + Fintype.card (ItemType T))
    (hno :
      EconCSLean.FiniteRounding.NoRoundingCrossing
        (fun t : ItemType T => a.count t)
        (fun t : ItemType T => anchor.count t)) :
    ∀ t : ItemType T,
      anchor.count t < a.count t + Fintype.card (ItemType T) ∧
        a.count t < anchor.count t + Fintype.card (ItemType T) := by
  exact UniformRounding.count_close_of_no_rounding_crossing
    a anchor ha hanchor hBle hNlt hno

/--
Proposition 2 rounding step from a strict exchange certificate.

For the uniform `[0,1]`, `k = 1` objective, if the real-relaxation floor anchor
has the strict boundary marginal comparisons needed in Appendix D.5, then every
finite optimum is count-close to that anchor. The remaining paper-specific work
is to prove this certificate for the square-root real-relaxation optimizer.
-/
theorem paper_uniform_rounding_count_close_of_strict_exchange_certificate
    {T : ℕ} (likelihood : ItemType T → ℝ)
    (a anchor : CountAllocation T) {N B : ℕ}
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hanchor : DecisionCore.Allocation.total anchor = B)
    (hlike_nonneg : ∀ t, 0 ≤ likelihood t)
    (hBle : B ≤ N)
    (hNlt : N < B + Fintype.card (ItemType T))
    (hcert : UniformTopOne.StrictRoundingExchangeCertificate likelihood anchor) :
    ∀ t : ItemType T,
      anchor.count t < a.count t + Fintype.card (ItemType T) ∧
        a.count t < anchor.count t + Fintype.card (ItemType T) := by
  have hno :=
    UniformTopOne.noRoundingCrossing_of_strictExchangeCertificate
      likelihood N hopt hlike_nonneg hcert
  exact paper_rounding_count_close_of_no_crossing
    a anchor hopt.1 hanchor hBle hNlt hno

/--
Appendix D.5 two-anchor rounding step from a strict exchange certificate.

This version is closer to real-relaxation proofs where lower and upper integer
anchors can be different, e.g. floor/ceiling bounds around a real optimum.
-/
theorem paper_uniform_rounding_count_close_of_two_anchor_certificate
    {T : ℕ} (likelihood : ItemType T → ℝ)
    (a lower upper : CountAllocation T) {N L U : ℕ}
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hlower : DecisionCore.Allocation.total lower = L)
    (hupper : DecisionCore.Allocation.total upper = U)
    (hlike_nonneg : ∀ t, 0 ≤ likelihood t)
    (hNlt : N < L + Fintype.card (ItemType T))
    (hUlt : U < N + Fintype.card (ItemType T))
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hcert :
      UniformTopOne.StrictRoundingExchangeCertificateBetween
        likelihood lower upper) :
    ∀ t : ItemType T,
      lower.count t < a.count t + Fintype.card (ItemType T) ∧
        a.count t < upper.count t + Fintype.card (ItemType T) := by
  have hno :=
    UniformTopOne.noRoundingCrossingBetween_of_strictExchangeCertificate
      likelihood N hopt hlike_nonneg horder hcert
  exact UniformRounding.count_close_of_no_rounding_crossing_between
    a lower upper hopt.1 hlower hupper hNlt hUlt horder hno

/--
Appendix D.5 two-anchor rounding step from squared shifted real targets.

This discharges the strict exchange certificate when likelihoods are a positive
scale times squared shifted targets and the lower/upper anchors bracket those
targets.
-/
theorem paper_uniform_rounding_count_close_of_shifted_square_anchors
    {T : ℕ} (likelihood : ItemType T → ℝ)
    (a lower upper : CountAllocation T) {N L U : ℕ}
    (scale : ℝ) (shift : ItemType T → ℝ)
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hlower : DecisionCore.Allocation.total lower = L)
    (hupper : DecisionCore.Allocation.total upper = U)
    (hNlt : N < L + Fintype.card (ItemType T))
    (hUlt : U < N + Fintype.card (ItemType T))
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hscale_pos : 0 < scale)
    (hlike : ∀ t, likelihood t = scale * (shift t) ^ 2)
    (hshift_nonneg : ∀ t, 0 ≤ shift t)
    (hupper_shift : ∀ t, shift t ≤ (upper.count t : ℝ) + 1)
    (hlower_shift : ∀ t, (lower.count t : ℝ) + 1 ≤ shift t) :
    ∀ t : ItemType T,
      lower.count t < a.count t + Fintype.card (ItemType T) ∧
        a.count t < upper.count t + Fintype.card (ItemType T) := by
  have hlike_nonneg : ∀ t, 0 ≤ likelihood t := by
    intro t
    rw [hlike t]
    exact mul_nonneg (le_of_lt hscale_pos) (sq_nonneg (shift t))
  have hcert :=
    UniformTopOne.strictRoundingExchangeCertificateBetween_of_shifted_target
      likelihood lower upper scale shift hscale_pos hlike
      hshift_nonneg hupper_shift hlower_shift
  exact paper_uniform_rounding_count_close_of_two_anchor_certificate
    likelihood a lower upper hopt hlower hupper hlike_nonneg
    hNlt hUlt horder hcert

/--
Finite Proposition 2 bridge from square-root anchors to homogeneity.

For the uniform `[0,1]`, `k = 1` objective, suppose the real-relaxation floor
anchor is within one item of the square-root target count and satisfies the
strict boundary exchange certificate. Then every finite optimum is
approximately `1/2`-homogeneous with the paper's finite rounding error
`(m + 1) / N`.

The remaining paper-specific work is to construct this anchor from the
square-root real-relaxation optimizer.
-/
theorem paper_uniform_top_one_sqrt_homogeneity_of_anchor_certificate
    {T : ℕ} (likelihood : ItemType T → ℝ)
    (a anchor : CountAllocation T) {N B : ℕ}
    (hNpos : 0 < N)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0)
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hanchor : DecisionCore.Allocation.total anchor = B)
    (hlike_nonneg : ∀ t, 0 ≤ likelihood t)
    (hBle : B ≤ N)
    (hNlt : N < B + Fintype.card (ItemType T))
    (hcert : UniformTopOne.StrictRoundingExchangeCertificate likelihood anchor)
    (hanchor_close :
      ∀ t,
        |(anchor.count t : ℝ) -
          (N : ℝ) *
            (Real.sqrt (likelihood t) /
              ∑ i : ItemType T, Real.sqrt (likelihood i))| ≤ 1) :
    (sqrtLikelihoodProfile likelihood).Approx a
      (((Fintype.card (ItemType T) : ℝ) + 1) / (N : ℝ)) := by
  have hround :=
    paper_uniform_rounding_count_close_of_strict_exchange_certificate
      likelihood a anchor hopt hanchor hlike_nonneg hBle hNlt hcert
  refine paper_uniform_sqrt_homogeneity_of_count_closeness
    likelihood a hnorm hopt.1 hNpos ?_
  intro t
  let target : ℝ :=
    (N : ℝ) *
      (Real.sqrt (likelihood t) /
        ∑ i : ItemType T, Real.sqrt (likelihood i))
  have hcount_anchor :
      |(a.count t : ℝ) - (anchor.count t : ℝ)| ≤
        (Fintype.card (ItemType T) : ℝ) := by
    have hleft : (anchor.count t : ℝ) <
        (a.count t : ℝ) + (Fintype.card (ItemType T) : ℝ) := by
      exact_mod_cast (hround t).1
    have hright : (a.count t : ℝ) <
        (anchor.count t : ℝ) + (Fintype.card (ItemType T) : ℝ) := by
      exact_mod_cast (hround t).2
    rw [abs_le]
    constructor <;> linarith
  have hanchor_target : |(anchor.count t : ℝ) - target| ≤ 1 := by
    simpa [target] using hanchor_close t
  have hsplit :
      (a.count t : ℝ) - target =
        ((a.count t : ℝ) - (anchor.count t : ℝ)) +
          ((anchor.count t : ℝ) - target) := by
    ring
  calc
    |(a.count t : ℝ) - target|
        = |((a.count t : ℝ) - (anchor.count t : ℝ)) +
            ((anchor.count t : ℝ) - target)| := by
            rw [hsplit]
    _ ≤ |(a.count t : ℝ) - (anchor.count t : ℝ)| +
          |(anchor.count t : ℝ) - target| := abs_add_le _ _
    _ ≤ (Fintype.card (ItemType T) : ℝ) + 1 :=
          add_le_add hcount_anchor hanchor_target

/--
Finite Proposition 2 bridge from two square-root anchors to homogeneity.

If lower and upper integer anchors bracket the real square-root target within
one item and satisfy the strict two-anchor boundary exchange certificate, then
every finite optimum is approximately `1/2`-homogeneous with error
`(m + 1) / N`.
-/
theorem paper_uniform_top_one_sqrt_homogeneity_of_two_anchor_certificate
    {T : ℕ} (likelihood : ItemType T → ℝ)
    (a lower upper : CountAllocation T) {N L U : ℕ}
    (hNpos : 0 < N)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0)
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hlower : DecisionCore.Allocation.total lower = L)
    (hupper : DecisionCore.Allocation.total upper = U)
    (hlike_nonneg : ∀ t, 0 ≤ likelihood t)
    (hNlt : N < L + Fintype.card (ItemType T))
    (hUlt : U < N + Fintype.card (ItemType T))
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hcert :
      UniformTopOne.StrictRoundingExchangeCertificateBetween
        likelihood lower upper)
    (hlower_close :
      ∀ t,
        |(lower.count t : ℝ) -
          (N : ℝ) *
            (Real.sqrt (likelihood t) /
              ∑ i : ItemType T, Real.sqrt (likelihood i))| ≤ 1)
    (hupper_close :
      ∀ t,
        |(upper.count t : ℝ) -
          (N : ℝ) *
            (Real.sqrt (likelihood t) /
              ∑ i : ItemType T, Real.sqrt (likelihood i))| ≤ 1) :
    (sqrtLikelihoodProfile likelihood).Approx a
      (((Fintype.card (ItemType T) : ℝ) + 1) / (N : ℝ)) := by
  have hround :=
    paper_uniform_rounding_count_close_of_two_anchor_certificate
      likelihood a lower upper hopt hlower hupper hlike_nonneg
      hNlt hUlt horder hcert
  refine paper_uniform_sqrt_homogeneity_of_count_closeness
    likelihood a hnorm hopt.1 hNpos ?_
  intro t
  let target : ℝ :=
    (N : ℝ) *
      (Real.sqrt (likelihood t) /
        ∑ i : ItemType T, Real.sqrt (likelihood i))
  have hlow_round : (lower.count t : ℝ) <
      (a.count t : ℝ) + (Fintype.card (ItemType T) : ℝ) := by
    exact_mod_cast (hround t).1
  have hhigh_round : (a.count t : ℝ) <
      (upper.count t : ℝ) + (Fintype.card (ItemType T) : ℝ) := by
    exact_mod_cast (hround t).2
  have hlower_abs : |(lower.count t : ℝ) - target| ≤ 1 := by
    simpa [target] using hlower_close t
  have hupper_abs : |(upper.count t : ℝ) - target| ≤ 1 := by
    simpa [target] using hupper_close t
  have hlower_left : -1 ≤ (lower.count t : ℝ) - target :=
    (abs_le.mp hlower_abs).1
  have hupper_right : (upper.count t : ℝ) - target ≤ 1 :=
    (abs_le.mp hupper_abs).2
  rw [abs_le]
  constructor <;> linarith

/--
Finite Proposition 2 bridge from squared shifted real targets to homogeneity.

This combines the two-anchor shifted-target exchange certificate, rounding
combinatorics, and square-root-profile representation bridge.
-/
theorem paper_uniform_top_one_sqrt_homogeneity_of_shifted_square_anchors
    {T : ℕ} (likelihood : ItemType T → ℝ)
    (a lower upper : CountAllocation T) {N L U : ℕ}
    (scale : ℝ) (shift : ItemType T → ℝ)
    (hNpos : 0 < N)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0)
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hlower : DecisionCore.Allocation.total lower = L)
    (hupper : DecisionCore.Allocation.total upper = U)
    (hNlt : N < L + Fintype.card (ItemType T))
    (hUlt : U < N + Fintype.card (ItemType T))
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hscale_pos : 0 < scale)
    (hlike : ∀ t, likelihood t = scale * (shift t) ^ 2)
    (hshift_nonneg : ∀ t, 0 ≤ shift t)
    (hupper_shift : ∀ t, shift t ≤ (upper.count t : ℝ) + 1)
    (hlower_shift : ∀ t, (lower.count t : ℝ) + 1 ≤ shift t)
    (hlower_close :
      ∀ t,
        |(lower.count t : ℝ) -
          (N : ℝ) *
            (Real.sqrt (likelihood t) /
              ∑ i : ItemType T, Real.sqrt (likelihood i))| ≤ 1)
    (hupper_close :
      ∀ t,
        |(upper.count t : ℝ) -
          (N : ℝ) *
            (Real.sqrt (likelihood t) /
              ∑ i : ItemType T, Real.sqrt (likelihood i))| ≤ 1) :
    (sqrtLikelihoodProfile likelihood).Approx a
      (((Fintype.card (ItemType T) : ℝ) + 1) / (N : ℝ)) := by
  have hlike_nonneg : ∀ t, 0 ≤ likelihood t := by
    intro t
    rw [hlike t]
    exact mul_nonneg (le_of_lt hscale_pos) (sq_nonneg (shift t))
  have hcert :=
    UniformTopOne.strictRoundingExchangeCertificateBetween_of_shifted_target
      likelihood lower upper scale shift hscale_pos hlike
      hshift_nonneg hupper_shift hlower_shift
  exact paper_uniform_top_one_sqrt_homogeneity_of_two_anchor_certificate
    likelihood a lower upper hNpos hnorm hopt hlower hupper
    hlike_nonneg hNlt hUlt horder hcert hlower_close hupper_close

/--
Two-type Bernoulli first-order condition from type `0` to type `1`.
-/
theorem paper_two_type_forward_one_le_backward_zero
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (ha : 0 < a) :
    B.likelihood 1 * B.successProb 1 * (1 - B.successProb 1) ^ b ≤
      B.likelihood 0 * B.successProb 0 * (1 - B.successProb 0) ^ (a - 1) := by
  exact twoTypeAllocation_forward_one_le_backward_zero_of_optimum B N a b hopt ha

/--
Two-type Bernoulli first-order condition from type `1` to type `0`.
-/
theorem paper_two_type_forward_zero_le_backward_one
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (hb : 0 < b) :
    B.likelihood 0 * B.successProb 0 * (1 - B.successProb 0) ^ a ≤
      B.likelihood 1 * B.successProb 1 * (1 - B.successProb 1) ^ (b - 1) := by
  exact twoTypeAllocation_forward_zero_le_backward_one_of_optimum B N a b hopt hb

/--
Symmetric two-type Bernoulli finite homogeneity theorem.

When two Bernoulli item types have the same likelihood and success probability,
every finite optimum splits the slate between the two types up to a one-item
rounding error.
-/
theorem paper_symmetric_two_type_bernoulli_optimum_balanced
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (hlike : B.likelihood 0 = B.likelihood 1)
    (hprob : B.successProb 0 = B.successProb 1)
    (hlike_pos : 0 < B.likelihood 0)
    (hprob_pos : 0 < B.successProb 0)
    (hprob_lt_one : B.successProb 0 < 1) :
    a ≤ b + 1 ∧ b ≤ a + 1 := by
  exact twoTypeAllocation_balanced_of_symmetric_bernoulli_optimum
    B N a b hopt hlike hprob hlike_pos hprob_pos hprob_lt_one

/--
Symmetric two-type Bernoulli finite `0`-homogeneity theorem.

When two Bernoulli item types have the same likelihood and success probability,
every positive-size finite optimum is approximately equal-representation, with
error at most `1 / N`.
-/
theorem paper_symmetric_two_type_bernoulli_optimum_equal_homogeneity
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hNpos : 0 < N)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (hlike : B.likelihood 0 = B.likelihood 1)
    (hprob : B.successProb 0 = B.successProb 1)
    (hlike_pos : 0 < B.likelihood 0)
    (hprob_pos : 0 < B.successProb 0)
    (hprob_lt_one : B.successProb 0 < 1) :
    equalTwoTypeProfile.Approx (twoTypeAllocation a b) (1 / (N : ℝ)) := by
  exact twoTypeAllocation_equalTwoTypeProfile_approx_of_symmetric_bernoulli_optimum
    B N a b hNpos hopt hlike hprob hlike_pos hprob_pos hprob_lt_one

end AccuracyDiversity
