import PRPKG24AccuracyDiversity.Examples
import PRPKG24AccuracyDiversity.Uniform
import PRPKG24AccuracyDiversity.TailHomogeneity
import PRPKG24AccuracyDiversity.Bounded
import PRPKG24AccuracyDiversity.Pareto
import PRPKG24AccuracyDiversity.SeparableAsymptotic
import PRPKG24AccuracyDiversity.FiniteDiscreteOrderStats
import PRPKG24AccuracyDiversity.ExponentialTopOne
import PRPKG24AccuracyDiversity.DecayingBernoulli
import EconCSLib.Foundations.Probability.RealDistribution

open scoped BigOperators

/-!
# Paper-Facing Theorems: Reconciling the Accuracy-Diversity Trade-off

This file is the public theorem interface for the accuracy-diversity
formalization. Detailed allocation, representation, Bernoulli, and exchange
lemmas live in the sibling files.
-/

namespace PRPKG24AccuracyDiversity

namespace ConsumptionModel

/--
Finite optimizer existence for a fixed slate size.
-/
theorem paper_finite_optimum_exists
    {T : ℕ} [Nonempty (ItemType T)] (M : ConsumptionModel T) (N : ℕ) :
    ∃ a : CountAllocation T, M.IsOptimalAtTotal N a := by
  exact M.exists_isOptimalAtTotal N

/--
Finite exchange-improvement theorem.
-/
theorem paper_finite_exchange_improvement
    {T : ℕ} (M : ConsumptionModel T) :
    M.ExchangeImprovementTarget := by
  exact M.exchangeImprovementTarget

/--
Finite first-order condition for optimal count allocations.
-/
theorem paper_finite_optimum_first_order_condition
    {T : ℕ} (M : ConsumptionModel T) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : M.IsOptimalAtTotal N a) (hne : src ≠ dst)
    (hcan : EconCSLib.Allocation.CanMoveOne a src) :
    M.weightedForwardMarginal dst (a.count dst) ≤
      M.weightedBackwardMarginal src (a.count src) := by
  exact M.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
    N hopt hne hcan

/--
Source Theorem 1(v), all-consumed/no-consumption-constraint core.

When every type has the same nonnegative conditional mean, the all-consumed
linear objective is optimized by putting all recommendations on any type with
maximal likelihood.
-/
theorem paper_theorem1_all_consumed_common_mean_argmax_optimum
    {T : ℕ} (likelihood : ItemType T → ℝ) (mean : ℝ) (N : ℕ)
    (best : ItemType T)
    (hmean_nonneg : 0 ≤ mean)
    (hbest : ∀ t, likelihood t ≤ likelihood best) :
    (ConsumptionModel.linearized likelihood (fun _ => mean)).IsOptimalAtTotal
      N (allOnTypeAllocation N best) := by
  exact allOnTypeAllocation_linearized_isOptimalAtTotal
    likelihood (fun _ => mean) N best
    (fun t => mul_le_mul_of_nonneg_right (hbest t) hmean_nonneg)

/--
Source Theorem 1(v), unique-argmax converse.

When the common conditional mean is positive and `best` is the unique maximizer
of type likelihood, every all-consumed optimum places zero recommendations on
all non-best types.
-/
theorem paper_theorem1_all_consumed_unique_common_mean_only_argmax
    {T : ℕ} (likelihood : ItemType T → ℝ) (mean : ℝ) (N : ℕ)
    (best : ItemType T)
    (hmean_pos : 0 < mean)
    (hbest_strict : ∀ t, t ≠ best → likelihood t < likelihood best)
    (a : CountAllocation T)
    (hopt :
      (ConsumptionModel.linearized likelihood (fun _ => mean)).IsOptimalAtTotal
        N a) :
    ∀ t, t ≠ best → a.count t = 0 := by
  intro t ht
  exact
    linearized_optimal_count_eq_zero_of_strict_score_lt
      (N := N) (a := a) (t := t) (best := best) hopt
      (by
        simpa using
          mul_lt_mul_of_pos_right (hbest_strict t ht) hmean_pos)

end ConsumptionModel

/--
Source Example 1, all-consumed side: because both genres have the same
conditional exponential mean `1/lambda`, a romance-only slate is optimal when
`p1 >= p2`.
-/
theorem paper_example1_all_consumed_all_romance_is_optimal
    {p1 p2 lambda : ℝ} (N : ℕ)
    (hlambda : 0 < lambda) (hp2_le_p1 : p2 ≤ p1) :
    (example1AllConsumedModel p1 p2 lambda).IsOptimalAtTotal
      N (allOnTypeAllocation N (0 : ItemType 2)) := by
  have hmean_nonneg : 0 ≤ example1ExponentialMean lambda :=
    le_of_lt (by simpa [example1ExponentialMean] using inv_pos.mpr hlambda)
  have hbest :
      ∀ t : ItemType 2,
        example1Likelihood p1 p2 t ≤
          example1Likelihood p1 p2 (0 : ItemType 2) := by
    intro t
    fin_cases t
    · simp
    · simpa using hp2_le_p1
  simpa [example1AllConsumedModel] using
    ConsumptionModel.paper_theorem1_all_consumed_common_mean_argmax_optimum
      (example1Likelihood p1 p2) (example1ExponentialMean lambda) N
      (0 : ItemType 2) hmean_nonneg hbest

/--
Source Example 1, all-consumed unique-argmax side: if `p1 > p2`, every optimum
places zero action recommendations.
-/
theorem paper_example1_all_consumed_only_romance
    {p1 p2 lambda : ℝ} {N : ℕ} (a : CountAllocation 2)
    (hlambda : 0 < lambda) (hp2_lt_p1 : p2 < p1)
    (hopt : (example1AllConsumedModel p1 p2 lambda).IsOptimalAtTotal N a) :
    a.count (1 : ItemType 2) = 0 := by
  have hmean_pos : 0 < example1ExponentialMean lambda := by
    simpa [example1ExponentialMean] using inv_pos.mpr hlambda
  have hbest_strict :
      ∀ t : ItemType 2, t ≠ (0 : ItemType 2) →
        example1Likelihood p1 p2 t <
          example1Likelihood p1 p2 (0 : ItemType 2) := by
    intro t ht
    fin_cases t
    · exact False.elim (ht rfl)
    · simpa using hp2_lt_p1
  have h :=
    ConsumptionModel.paper_theorem1_all_consumed_unique_common_mean_only_argmax
      (example1Likelihood p1 p2) (example1ExponentialMean lambda) N
      (0 : ItemType 2) hmean_pos hbest_strict a
      (by simpa [example1AllConsumedModel] using hopt)
  exact h (1 : ItemType 2) (by decide)

/--
Source Example 1 feasibility check: the calibrated relaxed split has total
slate size `n` when `p1 + p2 = 1`.
-/
theorem paper_example1_calibrated_split_sum
    {p1 p2 n : ℝ} (hp_sum : p1 + p2 = 1) :
    p1 * n + p2 * n = n :=
  example1_calibrated_split_sum hp_sum

/--
Source Example 1, top-one side: the calibrated split maximizes the displayed
log-relaxation objective among positive relaxed splits with total size `n`.
-/
theorem paper_example1_top_one_log_relaxation_calibrated
    {p1 p2 lambda n x y : ℝ}
    (hp1 : 0 < p1) (hp2 : 0 < p2) (hlambda : 0 < lambda)
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y)
    (hp_sum : p1 + p2 = 1) (hxy_sum : x + y = n) :
    example1LogRelaxedObjective p1 p2 lambda x y ≤
      example1LogRelaxedObjective p1 p2 lambda (p1 * n) (p2 * n) :=
  example1_log_relaxed_objective_le_calibrated
    hp1 hp2 hlambda hn hx hy hp_sum hxy_sum

/--
Source Definition 1, finite γ-homogeneity: exact representation agrees with
the paper formula `p_t^γ / ∑_i p_i^γ`.
-/
theorem paper_definition1_gamma_homogeneity_exact_iff
    {T : ℕ} (a : CountAllocation T) (likelihood : ItemType T → ℝ)
    (γ : ℝ)
    (hnorm : (∑ i : ItemType T, (likelihood i) ^ γ) ≠ 0) :
    (gammaLikelihoodProfile likelihood γ).Exact a ↔
      ∀ t : ItemType T,
        CountAllocation.representation a t =
          (likelihood t) ^ γ /
            ∑ i : ItemType T, (likelihood i) ^ γ := by
  constructor
  · intro h t
    unfold GammaHomogeneityProfile.Exact
      CountAllocation.HasExactRepresentation at h
    rw [h t]
    exact gammaLikelihoodProfile_targetShare_eq likelihood γ t hnorm
  · intro h
    unfold GammaHomogeneityProfile.Exact
      CountAllocation.HasExactRepresentation
    intro t
    calc
      CountAllocation.representation a t =
          (likelihood t) ^ γ /
            ∑ i : ItemType T, (likelihood i) ^ γ := h t
      _ = (gammaLikelihoodProfile likelihood γ).targetShare t := by
          symm
          exact gammaLikelihoodProfile_targetShare_eq likelihood γ t hnorm

/--
Source Definition 2, sequence γ-homogeneity: convergence of type
representations agrees with the paper formula `p_t^γ / ∑_i p_i^γ`.
-/
theorem paper_definition2_gamma_homogeneity_sequence_iff
    {T : ℕ} (seq : AllocationSequence T)
    (likelihood : ItemType T → ℝ) (γ : ℝ)
    (hnorm : (∑ i : ItemType T, (likelihood i) ^ γ) ≠ 0) :
    seq.ConvergesToProfile (gammaLikelihoodProfile likelihood γ) ↔
      ∀ t : ItemType T,
        Filter.Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          Filter.atTop
          (nhds
            ((likelihood t) ^ γ /
              ∑ i : ItemType T, (likelihood i) ^ γ)) := by
  constructor
  · intro h t
    have htarget :=
      gammaLikelihoodProfile_targetShare_eq likelihood γ t hnorm
    simpa [AllocationSequence.representation, htarget] using h t
  · intro h t
    have htarget :=
      gammaLikelihoodProfile_targetShare_eq likelihood γ t hnorm
    simpa [AllocationSequence.representation, htarget] using h t

/--
Source Definition 3 / Proposition 5 interface: if `μ i a` is the expected
`i`-th smallest order statistic among `a` i.i.d. draws, the expected top-`k`
sum is the sum of the upper `min k a` order-statistic means.
-/
theorem paper_definition3_order_statistic_topk_sum_from_mean
    (μ : ℕ → ℕ → ℝ) (k a : ℕ) :
    orderStatisticTopKSumFromMean μ k a =
      ∑ i ∈ Finset.range (min k a), μ (a - i) a := rfl

/--
Definition 3 finite-prefix bridge: for fixed `k`, once `a ≥ k`, the paper's
bottom-indexed order-statistic sum is the `Fin k` source-mean sum used by the
bounded-support asymptotic layer.
-/
theorem paper_definition3_order_statistic_topk_sum_eq_fin_sum_of_le
    (μ : ℕ → ℕ → ℝ) {k a : ℕ} (hka : k ≤ a) :
    orderStatisticTopKSumFromMean μ k a =
      ∑ i : Fin k, μ (a - i.val) a :=
  orderStatisticTopKSumFromMean_eq_fin_sum_of_le μ hka

/--
Endpoint-loss form of the Definition 3 finite-prefix bridge.  The event is
automatic for fixed `k`, so asymptotic proofs may replace the `min k a` sum by
the `Fin k` source-mean sum after a finite prefix.
-/
theorem paper_definition3_order_statistic_topk_loss_eventually_eq_fin_loss
    (M : ℝ) (μ : ℕ → ℕ → ℝ) (k : ℕ) :
    ∀ᶠ a in Filter.atTop,
      (k : ℝ) * M - orderStatisticTopKSumFromMean μ k a =
        (k : ℝ) * M - ∑ i : Fin k, μ (a - i.val) a := by
  filter_upwards [Filter.eventually_ge_atTop k] with a hka
  exact orderStatisticTopKLossFromMean_eq_fin_loss_of_le M μ hka

/--
Pointwise source bridge for Definition 3: a concrete real sample tuple induces
the paper's bottom-indexed order-statistic top-`k` sum.
-/
theorem paper_definition3_order_statistic_topk_sum_from_sample
    {a : ℕ} (sample : Fin a → ℝ) (k : ℕ) :
    orderStatisticTopKSumFromMean
        (fun rank sampleSize =>
          if sampleSize = a then sampleOrderStatisticValue sample rank else 0)
        k a =
      EconCSLib.Probability.sampleTopKSum sample k :=
  orderStatisticTopKSumFromSample_eq_sampleTopKSum sample k

/--
Measurability of the paper's bottom-indexed sample order-statistic value.
-/
theorem paper_definition3_sample_order_statistic_value_measurable
    {a : ℕ} (rank : ℕ) :
    Measurable
      (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample rank) :=
  sampleOrderStatisticValue_measurable rank

/--
Pointwise bounded-support reflection for real sample tuples: endpoint loss of
the largest source values equals the sum of the smallest reflected values.
-/
theorem paper_definition3_sample_topk_endpoint_loss_eq_reflected_bottom_sum
    (M : ℝ) {a : ℕ} (sample : Fin a → ℝ) (k : ℕ) :
    EconCSLib.Probability.sampleTopKEndpointLoss M sample k =
      EconCSLib.Probability.reflectedBottomKSum M sample k :=
  EconCSLib.Probability.sampleTopKEndpointLoss_eq_reflectedBottomKSum
    M sample k

/--
Pointwise layer-cake form of the reflected bottom-`k` sum.  This is the
finite-sample algebra behind the bounded-source CDF/binomial integral bridge:
the reflected lower order statistics are represented by threshold events where
at most `rank` reflected sample coordinates are below the threshold.
-/
theorem paper_definition3_reflected_bottom_sum_eq_integral_rank_count_indicator
    (M : ℝ) {a : ℕ} (sample : Fin a → ℝ) (k : ℕ)
    (hM : ∀ i, sample i ≤ M) :
    EconCSLib.Probability.reflectedBottomKSum M sample k =
      ∫ x in Set.Ioi (0 : ℝ),
        ∑ i : Fin (min k a),
          if (Finset.univ.filter
              (fun j : Fin a =>
                EconCSLib.Probability.reflectedSample M sample j ≤ x)).card ≤
              (EconCSLib.Probability.topKRankEmbedding k a i).val
          then (1 : ℝ) else 0 :=
  EconCSLib.Probability.reflectedBottomKSum_eq_integral_rank_count_indicator
    M sample k hM

/--
Pointwise bounded-support envelope: if all sample values are at most the
endpoint `M`, then the reflected bottom-`k` sum is nonnegative.
-/
theorem paper_definition3_reflected_bottom_sum_nonneg_of_forall_le
    (M : ℝ) {a : ℕ} {sample : Fin a → ℝ}
    (hM : ∀ i, sample i ≤ M) (k : ℕ) :
    0 ≤ EconCSLib.Probability.reflectedBottomKSum M sample k :=
  EconCSLib.Probability.reflectedBottomKSum_nonneg_of_forall_le
    M hM k

/--
Pointwise bounded-support envelope: if all sample values are at least `L`,
then the reflected bottom-`k` sum is bounded by `min k a * (M - L)`.
-/
theorem paper_definition3_reflected_bottom_sum_le_of_forall_lower
    (M L : ℝ) {a : ℕ} {sample : Fin a → ℝ}
    (hL : ∀ i, L ≤ sample i) (k : ℕ) :
    EconCSLib.Probability.reflectedBottomKSum M sample k ≤
      (min k a : ℝ) * (M - L) :=
  EconCSLib.Probability.reflectedBottomKSum_le_of_forall_lower
    M L hL k

/--
Pointwise bounded-support envelope for the top-`k` endpoint loss.
-/
theorem paper_definition3_sample_topk_endpoint_loss_le_of_forall_bounds
    (M L : ℝ) {a : ℕ} {sample : Fin a → ℝ}
    (hL : ∀ i, L ≤ sample i) (k : ℕ) :
    EconCSLib.Probability.sampleTopKEndpointLoss M sample k ≤
      (min k a : ℝ) * (M - L) :=
  EconCSLib.Probability.sampleTopKEndpointLoss_le_of_forall_bounds
    M L hL k

/--
Bounded-support integrability of a single sample order-statistic value.
-/
theorem paper_definition3_sample_order_statistic_value_integrable_of_ae_bounds
    (L U : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (rank : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    MeasureTheory.Integrable
      (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample rank) μ :=
  sampleOrderStatisticValue_integrable_of_ae_bounds
    L U μ rank h_bounds

/--
Bounded-support integrability for every order-statistic value appearing in the
paper's top-`k` finite sum.
-/
theorem paper_definition3_sample_order_statistic_topk_range_integrable_of_ae_bounds
    (L U : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    ∀ i ∈ Finset.range (min k a),
      MeasureTheory.Integrable
        (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample (a - i)) μ :=
  sampleOrderStatisticValue_topKRange_integrable_of_ae_bounds
    L U μ k h_bounds

/--
Bounded-support integrability of the pointwise top-`k` sample sum.
-/
theorem paper_definition3_sample_topk_sum_integrable_of_ae_bounds
    (L U : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    MeasureTheory.Integrable
      (fun sample : Fin a → ℝ => EconCSLib.Probability.sampleTopKSum sample k) μ :=
  EconCSLib.Probability.sampleTopKSum_integrable_of_ae_bounds
    L U μ k h_bounds

/--
Bounded-support integrability of the pointwise top-`k` endpoint loss.
-/
theorem paper_definition3_sample_topk_endpoint_loss_integrable_of_ae_bounds
    (M L : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M) :
    MeasureTheory.Integrable
      (fun sample : Fin a → ℝ =>
        EconCSLib.Probability.sampleTopKEndpointLoss M sample k) μ :=
  EconCSLib.Probability.sampleTopKEndpointLoss_integrable_of_ae_bounds
    M L μ k h_bounds

/--
Bounded-support integrability of the reflected bottom-`k` aggregate.
-/
theorem paper_definition3_reflected_bottom_sum_integrable_of_ae_bounds
    (M L : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M) :
    MeasureTheory.Integrable
      (fun sample : Fin a → ℝ =>
        EconCSLib.Probability.reflectedBottomKSum M sample k) μ :=
  EconCSLib.Probability.reflectedBottomKSum_integrable_of_ae_bounds
    M L μ k h_bounds

/--
Measure-level Definition 3 bridge: expected sample order-statistic means
induced by a finite real-sample law reproduce the expected pointwise top-`k`
sample sum.
-/
theorem paper_definition3_expected_order_statistic_topk_sum_eq_expected_sample_topk_sum
    {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ)) (k : ℕ)
    (h_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i)) μ) :
    orderStatisticTopKSumFromMean
        (expectedSampleOrderStatisticMean μ) k a =
      EconCSLib.Probability.expectedSampleTopKSum μ k :=
  expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum
    μ k h_integrable

/--
Bounded-support version of the measure-level Definition 3 bridge.  The
coordinatewise a.e. bounds discharge the finite order-statistic integrability
side condition.
-/
theorem paper_definition3_expected_order_statistic_topk_sum_eq_expected_sample_topk_sum_of_ae_bounds
    (L U : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    orderStatisticTopKSumFromMean
        (expectedSampleOrderStatisticMean μ) k a =
      EconCSLib.Probability.expectedSampleTopKSum μ k :=
  paper_definition3_expected_order_statistic_topk_sum_eq_expected_sample_topk_sum
    μ k
    (paper_definition3_sample_order_statistic_topk_range_integrable_of_ae_bounds
      L U μ k h_bounds)

/--
Measure-level bounded-support reflection in the paper's `μ_D` interface.  The
remaining distribution-specific step is to identify the reflected-bottom
expectation with the CDF integral terms in Lemma D.2.
-/
theorem paper_definition3_expected_order_statistic_topk_endpoint_loss_eq_expected_reflected_bottom_sum
    (M : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsProbabilityMeasure μ] (k : ℕ)
    (h_order_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i)) μ)
    (h_top_integrable :
      MeasureTheory.Integrable
        (fun sample => EconCSLib.Probability.sampleTopKSum sample k) μ) :
    (min k a : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedSampleOrderStatisticMean μ) k a =
      EconCSLib.Probability.expectedReflectedBottomKSum M μ k :=
  expectedSampleOrderStatisticTopKEndpointLoss_eq_expectedReflectedBottomKSum
    M μ k h_order_integrable h_top_integrable

/--
Bounded-support version of the measure-level reflection bridge.  If the finite
sample lies a.e. in `[L, M]`, both expectation-side integrability obligations
are automatic.
-/
theorem paper_definition3_expected_order_statistic_topk_endpoint_loss_eq_expected_reflected_bottom_sum_of_ae_bounds
    (M L : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsProbabilityMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M) :
    (min k a : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedSampleOrderStatisticMean μ) k a =
      EconCSLib.Probability.expectedReflectedBottomKSum M μ k :=
  paper_definition3_expected_order_statistic_topk_endpoint_loss_eq_expected_reflected_bottom_sum
    M μ k
    (paper_definition3_sample_order_statistic_topk_range_integrable_of_ae_bounds
      L M μ k h_bounds)
    (paper_definition3_sample_topk_sum_integrable_of_ae_bounds
      L M μ k h_bounds)

/--
Definition 3 bridge for a family of finite real-sample laws, producing the
paper's global `μ_D(rank,a)` interface across sample sizes.
-/
theorem paper_definition3_expected_order_statistic_mean_seq_topk_sum_eq_expected_sample_topk_sum
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (k a : ℕ)
    (h_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i))
          (sampleMeasure a)) :
    orderStatisticTopKSumFromMean
        (expectedOrderStatisticMeanSeq sampleMeasure) k a =
      EconCSLib.Probability.expectedSampleTopKSum (sampleMeasure a) k :=
  expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum
    sampleMeasure k a h_integrable

/--
Bounded-support version of the varying-sample-size Definition 3 bridge.
-/
theorem paper_definition3_expected_order_statistic_mean_seq_topk_sum_eq_expected_sample_topk_sum_of_ae_bounds
    (L U : ℝ)
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (k a : ℕ) [MeasureTheory.IsFiniteMeasure (sampleMeasure a)]
    (h_bounds :
      ∀ᵐ sample ∂sampleMeasure a, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    orderStatisticTopKSumFromMean
        (expectedOrderStatisticMeanSeq sampleMeasure) k a =
      EconCSLib.Probability.expectedSampleTopKSum (sampleMeasure a) k :=
  paper_definition3_expected_order_statistic_mean_seq_topk_sum_eq_expected_sample_topk_sum
    sampleMeasure k a
    (paper_definition3_sample_order_statistic_topk_range_integrable_of_ae_bounds
      L U (sampleMeasure a) k h_bounds)

/--
Bounded-support reflection bridge for a family of finite real-sample laws in
the paper's global `μ_D(rank,a)` interface.
-/
theorem paper_definition3_expected_order_statistic_mean_seq_topk_endpoint_loss_eq_expected_reflected_bottom_sum
    (M : ℝ)
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    {a : ℕ} [MeasureTheory.IsProbabilityMeasure (sampleMeasure a)] (k : ℕ)
    (h_order_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i))
          (sampleMeasure a))
    (h_top_integrable :
      MeasureTheory.Integrable
        (fun sample => EconCSLib.Probability.sampleTopKSum sample k)
        (sampleMeasure a)) :
    (min k a : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k a =
      EconCSLib.Probability.expectedReflectedBottomKSum
        M (sampleMeasure a) k :=
  expectedOrderStatisticMeanSeq_topKEndpointLoss_eq_expectedReflectedBottomKSum
    M sampleMeasure k h_order_integrable h_top_integrable

/--
Bounded-support version of the varying-sample-size reflection bridge.
-/
theorem paper_definition3_expected_order_statistic_mean_seq_topk_endpoint_loss_eq_expected_reflected_bottom_sum_of_ae_bounds
    (M L : ℝ)
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    {a : ℕ} [MeasureTheory.IsProbabilityMeasure (sampleMeasure a)] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂sampleMeasure a, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M) :
    (min k a : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k a =
      EconCSLib.Probability.expectedReflectedBottomKSum
        M (sampleMeasure a) k :=
  paper_definition3_expected_order_statistic_mean_seq_topk_endpoint_loss_eq_expected_reflected_bottom_sum
    M sampleMeasure k
    (paper_definition3_sample_order_statistic_topk_range_integrable_of_ae_bounds
      L M (sampleMeasure a) k h_bounds)
    (paper_definition3_sample_topk_sum_integrable_of_ae_bounds
      L M (sampleMeasure a) k h_bounds)

/--
Measure-level linearity bridge for the bounded reflected endpoint term.  This
reduces the aggregate reflected-bottom expectation to the finite sum of
reflected lower order-statistic integrals that the CDF calculation evaluates.
-/
theorem paper_definition3_expected_reflected_bottom_sum_eq_sum_reflected_order_statistic_integrals
    (M : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ)) (k : ℕ)
    (h_integrable :
      ∀ i : Fin (min k a),
        MeasureTheory.Integrable
          (fun sample =>
            EconCSLib.Probability.ascendingOrderStatistic
              (EconCSLib.Probability.reflectedSample M sample)
              (EconCSLib.Probability.topKRankEmbedding k a i))
          μ) :
    EconCSLib.Probability.expectedReflectedBottomKSum M μ k =
      ∑ i : Fin (min k a),
        ∫ sample,
          EconCSLib.Probability.ascendingOrderStatistic
            (EconCSLib.Probability.reflectedSample M sample)
            (EconCSLib.Probability.topKRankEmbedding k a i) ∂μ :=
  EconCSLib.Probability.expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic
    M μ k h_integrable

/--
Fixed-`k` version of the reflected-bottom linearity bridge for the eventual
regime `k ≤ a`.
-/
theorem paper_definition3_expected_reflected_bottom_sum_eq_sum_reflected_order_statistic_integrals_of_le
    (M : ℝ) {a k : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    (hka : k ≤ a)
    (h_integrable :
      ∀ i : Fin k,
        MeasureTheory.Integrable
          (fun sample =>
            EconCSLib.Probability.ascendingOrderStatistic
              (EconCSLib.Probability.reflectedSample M sample)
              ⟨i.val, lt_of_lt_of_le i.isLt hka⟩)
          μ) :
    EconCSLib.Probability.expectedReflectedBottomKSum M μ k =
      ∑ i : Fin k,
        ∫ sample,
          EconCSLib.Probability.ascendingOrderStatistic
            (EconCSLib.Probability.reflectedSample M sample)
            ⟨i.val, lt_of_lt_of_le i.isLt hka⟩ ∂μ :=
  EconCSLib.Probability.expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic_of_le
    M μ hka h_integrable

/--
Source Definition 3 oracle constructor from paper order-statistic means.
-/
noncomputable def paper_definition3_topk_value_oracle_from_order_statistic_mean
    (T : ℕ) (μ : ℕ → ℕ → ℝ) : TopKValueOracle T :=
  TopKValueOracle.ofOrderStatisticMean T μ

@[simp] theorem paper_definition3_topk_value_oracle_expectedTopSum
    (T : ℕ) (μ : ℕ → ℕ → ℝ) (k : ℕ) (t : ItemType T) (a : ℕ) :
    (paper_definition3_topk_value_oracle_from_order_statistic_mean T μ).expectedTopSum
        k t a =
      orderStatisticTopKSumFromMean μ k a := rfl

/--
Source Proposition 5, uniform `[0,1]` instance in the paper's bottom-indexed
order-statistic convention.
-/
theorem paper_proposition5_uniform_order_statistic_topk_sum_eq_value
    (k a : ℕ) :
    orderStatisticTopKSumFromMean uniformAscendingOrderStatisticMean k a =
      uniformTopKValue k a :=
  uniform_orderStatisticTopKSumFromMean_eq_value k a

/--
Uniform `[0,1]` top-`k` order-statistic means satisfy the bounded branch's
scaled-marginal interface with `β = 1`.
-/
noncomputable def paper_theorem1_ii_uniform_order_statistic_scaled_marginal_certificate
    (T : ℕ) {k : ℕ} (k_pos : 0 < k) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T uniformAscendingOrderStatisticMean) k
      (boundedPowerMarginalScale 1)
      (fun _ : ItemType T => uniformTopKFactor k) :=
  (BoundedOrderStatisticScaledMarginalCertificate.ofMarginalAsymptoticEquivalent
    (beta := 1) (limitCoeff := uniformTopKFactor k)
    (by norm_num) k_pos (uniformTopKFactor_pos k_pos) <| by
      rw [EconCSLib.Math.AsymptoticEquivalent]
      have hratio :
          Filter.Tendsto
            (fun q : ℕ => (((q + 1 : ℕ) : ℝ) / ((q + 2 : ℕ) : ℝ)))
            Filter.atTop (nhds 1) := by
        have h :=
          tendsto_add_mul_div_add_mul_atTop_nhds
            (𝕜 := ℝ) (1 : ℝ) (2 : ℝ) (1 : ℝ)
            (by norm_num : (1 : ℝ) ≠ 0)
        convert h using 1
        · ext q
          norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          ring
        · norm_num
      refine Filter.Tendsto.congr' ?_ hratio
      filter_upwards [Filter.eventually_ge_atTop k] with q hkq
      rw [uniform_orderStatisticTopKSumFromMean_eq_value,
        uniform_orderStatisticTopKSumFromMean_eq_value,
        uniformTopKValue_succ_sub_of_le hkq,
        boundedPowerMarginalScale_one_eq_inv_sq]
      have hfactor_ne : uniformTopKFactor k ≠ 0 :=
        (uniformTopKFactor_pos k_pos).ne'
      have hq1_pos : 0 < (((q + 1 : ℕ) : ℝ)) := by positivity
      have hq1_nonneg : 0 ≤ (((q + 1 : ℕ) : ℝ)) := hq1_pos.le
      have hq1_ne : (((q + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hq1_pos
      have hq2_pos : 0 < (((q + 2 : ℕ) : ℝ)) := by positivity
      have hq2_ne : (((q + 2 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hq2_pos
      have hq1_sq_ne : (((q + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≠ 0 :=
        pow_ne_zero 2 hq1_ne
      rw [Real.rpow_neg hq1_nonneg (2 : ℝ)]
      field_simp [hfactor_ne, hq1_ne, hq2_ne, hq1_sq_ne]
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring_nf
      have hpoly :
          (2 : ℝ) + (q : ℝ) * 5 + (q : ℝ) ^ 2 * 4 + (q : ℝ) ^ 3 =
            (q : ℝ) * (1 + (q : ℝ)) ^ (2 : ℝ) +
              (1 + (q : ℝ)) ^ (2 : ℝ) * 2 := by
        rw [Real.rpow_two]
        ring
      exact hpoly).toTopKScaledMarginalLimitCertificate

/--
The exact uniform order-statistic oracle induces the same consumption model as
the paper's closed-form uniform top-`k` objective.
-/
theorem paper_theorem1_ii_uniform_order_statistic_toConsumptionModel_eq
    {T : ℕ} (likelihood : ItemType T → ℝ) (k : ℕ) :
    (TopKValueOracle.ofOrderStatisticMean T uniformAscendingOrderStatisticMean).toConsumptionModel
        likelihood k =
      uniformTopKConsumptionModel likelihood k := by
  unfold TopKValueOracle.toConsumptionModel TopKValueOracle.ofOrderStatisticMean
    uniformTopKConsumptionModel
  congr
  funext t q
  exact uniform_orderStatisticTopKSumFromMean_eq_value k q

/--
The Proposition 2 square-root profile is the `γ = 1/2` likelihood profile.

This lets the exact uniform order-statistic branch feed the same
`gammaLikelihoodProfile` API as Theorem 1(ii)'s bounded-support statement.
-/
theorem paper_uniform_sqrt_profile_targetShare_eq_gamma_half
    {T : ℕ} (likelihood : ItemType T → ℝ) (t : ItemType T)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0) :
    (sqrtLikelihoodProfile likelihood).targetShare t =
      (gammaLikelihoodProfile likelihood (1 / 2)).targetShare t := by
  have hnorm_gamma :
      (∑ i : ItemType T, (likelihood i) ^ (1 / 2 : ℝ)) ≠ 0 := by
    simpa [Real.sqrt_eq_rpow] using hnorm
  rw [sqrtLikelihoodProfile.targetShare_eq likelihood t hnorm,
    gammaLikelihoodProfile_targetShare_eq likelihood (1 / 2) t hnorm_gamma]
  simp [Real.sqrt_eq_rpow]

/--
Source Theorem 1(i), equation (90) algebra for a pure geometric tail.
-/
theorem paper_theorem1_i_finite_discrete_log_geometric_tail_ratio
    {C r : ℝ} (hC : 0 < C) (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        Real.log (C * r ^ N) / (Real.log r * (N : ℝ)))
      Filter.atTop (nhds 1) :=
  finiteDiscrete_log_geometric_tail_ratio hC hr_pos hr_lt_one

/--
Source Theorem 1(i), equation (90) algebra for the polynomial-times-geometric
upper tail from line (89).
-/
theorem paper_theorem1_i_finite_discrete_log_polynomial_geometric_tail_ratio
    {C r : ℝ} (d : ℕ)
    (hC : 0 < C) (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        Real.log (C * (N : ℝ) ^ d * r ^ N) /
          (Real.log r * (N : ℝ)))
      Filter.atTop (nhds 1) :=
  finiteDiscrete_log_polynomial_geometric_tail_ratio d hC hr_pos hr_lt_one

/--
Source Theorem 1(i), equation (90) squeeze from the paper's geometric lower
bound and polynomial-times-geometric upper bound.
-/
theorem paper_theorem1_i_finite_discrete_log_tail_ratio_of_geometric_bounds
    {gap : ℕ → ℝ} {lower upper r : ℝ} (d : ℕ)
    (hlower_pos : 0 < lower) (hupper_pos : 0 < upper)
    (hr_pos : 0 < r) (hr_lt_one : r < 1)
    (hlower :
      ∀ᶠ N in Filter.atTop, lower * r ^ N ≤ gap N)
    (hupper :
      ∀ᶠ N in Filter.atTop, gap N ≤ upper * (N : ℝ) ^ d * r ^ N) :
    Filter.Tendsto
      (fun N : ℕ =>
        Real.log (gap N) / (Real.log r * (N : ℝ)))
      Filter.atTop (nhds 1) :=
  finiteDiscrete_log_tail_ratio_of_geometric_bounds
    d hlower_pos hupper_pos hr_pos hr_lt_one hlower hupper

/--
Source Theorem 1(i), deterministic top-`k` upper marginal step.

If the old sample already contains `k` top-support values, adding another
bounded item does not increase the top-`k` value.  On the complementary
failure event, the improvement is at most `k * xTop`.
-/
theorem paper_theorem1_i_finite_discrete_sample_topK_upper_marginal_failure_indicator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop newValue : ℝ}
    [Decidable (hasKTopValues k xTop v)]
    (hxTop_nonneg : 0 ≤ xTop)
    (h_le : ∀ i, v i ≤ xTop) (hnew_le : newValue ≤ xTop) :
    topKSumOn k (extendSample v newValue) - topKSumOn k v ≤
      (k : ℝ) * xTop *
        (if hasKTopValues k xTop v then (0 : ℝ) else 1) :=
  topKSumOn_extend_sub_le_top_failure_indicator
    k v hxTop_nonneg h_le hnew_le

/--
Source Theorem 1(i), finite-expectation lift of the upper marginal step.

For an old random sample and an independent new item, the expected top-`k`
marginal is bounded by `k * xTop` times the probability that the old sample has
fewer than `k` top-support values.
-/
theorem paper_theorem1_i_finite_discrete_expected_topK_upper_marginal_failure_prob
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (sampleLaw : PMF (ι → Ω)) (itemLaw : PMF Ω)
    (k : ℕ) (value : Ω → ℝ) {xTop : ℝ}
    (hxTop_nonneg : 0 ≤ xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    [DecidablePred
      (fun sample : ι → Ω =>
        ¬ hasKTopValues k xTop (fun i => value (sample i)))] :
    EconCSLib.pmfPairExp sampleLaw itemLaw
        (fun sample newItem =>
          topKSumOn k
              (extendSample (fun i => value (sample i)) (value newItem)) -
            topKSumOn k (fun i => value (sample i)))
      ≤
        (k : ℝ) * xTop *
          EconCSLib.pmfProb sampleLaw
            (fun sample =>
              ¬ hasKTopValues k xTop (fun i => value (sample i))) :=
  pmfPairExp_topK_extend_sub_le_top_failure_prob
    sampleLaw itemLaw k value hxTop_nonneg hvalue_le

/--
Source Theorem 1(i), event/cardinality bridge for the upper marginal: the event
that a sample already contains `k` top-support draws is exactly the event that
the top-value count is at least `k`.
-/
theorem paper_theorem1_i_finite_discrete_hasKTopValues_iff_topValueCount
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (xTop : ℝ) (v : ι → ℝ) :
    hasKTopValues k xTop v ↔ k ≤ topValueCount xTop v :=
  hasKTopValues_iff_le_topValueCount k xTop v

/--
Source Theorem 1(i), deterministic promoting-event lower marginal step.

If the old sample has exactly `k-1` top-support values, all other old values
are at most the second support value, and the new draw is top-support, then the
top-`k` value increases by at least `xTop - xSecond`.
-/
theorem paper_theorem1_i_finite_discrete_sample_topK_lower_marginal_promoting_event
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop xSecond newValue : ℝ}
    (hk_pos : 0 < k)
    (hxTop_nonneg : 0 ≤ xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (topSet : Finset ι)
    (htop_card : topSet.card = k - 1)
    (htop_value : ∀ i ∈ topSet, v i = xTop)
    (hnontop_le : ∀ i, i ∉ topSet → v i ≤ xSecond)
    (hnew_eq : newValue = xTop) :
    xTop - xSecond ≤
      topKSumOn k (extendSample v newValue) - topKSumOn k v :=
  topKSumOn_extend_sub_ge_top_gap_of_pred_top_witness
    k v hk_pos hxTop_nonneg hxSecond_nonneg hsecond_le_top topSet
    htop_card htop_value hnontop_le hnew_eq

/--
Source Theorem 1(i), finite-expectation lift of the promoting-event lower
marginal step.  The event probability is represented as the pair expectation
of its indicator.
-/
theorem paper_theorem1_i_finite_discrete_expected_topK_lower_marginal_promoting_event
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (sampleLaw : PMF (ι → Ω)) (itemLaw : PMF Ω)
    (k : ℕ) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hxTop_nonneg : 0 ≤ xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    [∀ sample : ι → Ω,
      DecidablePred
        (fun newItem : Ω =>
          hasPredTopValuesWithSecondBound k xTop xSecond
              (fun i => value (sample i)) ∧
            value newItem = xTop)] :
    (xTop - xSecond) *
        EconCSLib.pmfPairExp sampleLaw itemLaw
          (fun sample newItem =>
            if hasPredTopValuesWithSecondBound k xTop xSecond
                (fun i => value (sample i)) ∧
              value newItem = xTop then (1 : ℝ) else 0)
      ≤
        EconCSLib.pmfPairExp sampleLaw itemLaw
          (fun sample newItem =>
            topKSumOn k
                (extendSample (fun i => value (sample i)) (value newItem)) -
              topKSumOn k (fun i => value (sample i))) :=
  top_gap_mul_pmfPairExp_promoting_indicator_le_topK_extend_sub
    sampleLaw itemLaw k value hk_pos hxTop_nonneg hxSecond_nonneg
    hsecond_le_top

/--
Source Theorem 1(i), event/cardinality bridge for the lower marginal: under the
finite-discrete two-level support split, the promoting event is exactly that the
old sample has `k-1` top-support draws.
-/
theorem
    paper_theorem1_i_finite_discrete_promoting_event_iff_topValueCount_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) {xTop xSecond : ℝ} (v : ι → ℝ)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_split : ∀ i, v i = xTop ∨ v i ≤ xSecond) :
    hasPredTopValuesWithSecondBound k xTop xSecond v ↔
      topValueCount xTop v = k - 1 :=
  hasPredTopValuesWithSecondBound_iff_topValueCount_eq
    k v hsecond_lt_top hvalue_split

/--
Source Theorem 1(i), finite i.i.d. bridge: a coordinate-dependent event under
the independent product PMF factors into one-coordinate probabilities.  This is
the product-law input for the binomial count bridge.
-/
theorem paper_theorem1_i_finite_discrete_product_forall_factorization
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (event : ι → Ω → Prop)
    [∀ i, DecidablePred (event i)] :
    EconCSLib.pmfProb (EconCSLib.pmfProduct ι Ω itemLaw)
        (fun sample : ι → Ω => ∀ i : ι, event i (sample i)) =
      ∏ i : ι, EconCSLib.pmfProb itemLaw (event i) :=
  pmfProduct_prob_forall_dependent itemLaw event

/--
Source Theorem 1(i), exact finite i.i.d. binomial lower-tail bridge: the
probability that the old sample has fewer than `k` top-support draws is exactly
`finiteDiscreteTopMassFailureTail`.
-/
theorem paper_theorem1_i_finite_discrete_product_failure_tail_exact
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) (xTop : ℝ)
    [DecidablePred
      (fun sample : ι → Ω =>
        ¬ hasKTopValues k xTop (fun i => value (sample i)))] :
    EconCSLib.pmfProb (EconCSLib.pmfProduct ι Ω itemLaw)
        (fun sample : ι → Ω =>
          ¬ hasKTopValues k xTop (fun i => value (sample i))) =
      finiteDiscreteTopMassFailureTail k (Fintype.card ι)
        (EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
        (EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) := by
  classical
  calc
    EconCSLib.pmfProb (EconCSLib.pmfProduct ι Ω itemLaw)
        (fun sample : ι → Ω =>
          ¬ hasKTopValues k xTop (fun i => value (sample i)))
        =
        EconCSLib.pmfProb (EconCSLib.pmfProduct ι Ω itemLaw)
          (fun sample : ι → Ω =>
            (successIndexSet (fun ω => value ω = xTop) sample).card < k) := by
          refine EconCSLib.pmfProb_congr _ ?_
          intro sample
          have hcount :
              topValueCount xTop (fun i => value (sample i)) =
                (successIndexSet (fun ω => value ω = xTop) sample).card := rfl
          rw [hasKTopValues_iff_le_topValueCount]
          simpa [hcount] using
            (not_le :
              (¬ k ≤ (successIndexSet (fun ω => value ω = xTop) sample).card) ↔
                (successIndexSet (fun ω => value ω = xTop) sample).card < k)
    _ =
        finiteDiscreteTopMassFailureTail k (Fintype.card ι)
          (EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
          (EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) := by
          rw [pmfProduct_prob_successIndexSet_card_lt_eq_sum]
          rfl

/--
Source Theorem 1(i), exact finite i.i.d. promoting-event bridge: the event that
the old sample has exactly `k-1` top-support draws and the new draw is
top-support has mass `finiteDiscreteTopMassPromotingEvent`.
-/
theorem paper_theorem1_i_finite_discrete_product_promoting_event_exact
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    [∀ sample : ι → Ω,
      DecidablePred
        (fun newItem : Ω =>
          hasPredTopValuesWithSecondBound k xTop xSecond
              (fun i => value (sample i)) ∧
            value newItem = xTop)] :
    EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
        (fun sample newItem =>
          if hasPredTopValuesWithSecondBound k xTop xSecond
              (fun i => value (sample i)) ∧
            value newItem = xTop then (1 : ℝ) else 0) =
      finiteDiscreteTopMassPromotingEvent k (Fintype.card ι)
        (EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
        (EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) := by
  classical
  let q := EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop)
  let rho := EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)
  let oldPromoting : (ι → Ω) → Prop :=
    fun sample =>
      hasPredTopValuesWithSecondBound k xTop xSecond
        (fun i => value (sample i))
  have hold_eq :
      EconCSLib.pmfProb (EconCSLib.pmfProduct ι Ω itemLaw) oldPromoting =
        (Nat.choose (Fintype.card ι) (k - 1) : ℝ) *
          q ^ (k - 1) * rho ^ (Fintype.card ι - (k - 1)) := by
    calc
      EconCSLib.pmfProb (EconCSLib.pmfProduct ι Ω itemLaw) oldPromoting
          =
          EconCSLib.pmfProb (EconCSLib.pmfProduct ι Ω itemLaw)
            (fun sample : ι → Ω =>
              (successIndexSet (fun ω => value ω = xTop) sample).card =
                k - 1) := by
            refine EconCSLib.pmfProb_congr _ ?_
            intro sample
            have hcount :
                topValueCount xTop (fun i => value (sample i)) =
                  (successIndexSet (fun ω => value ω = xTop) sample).card := rfl
            have hsplit_sample :
                ∀ i, value (sample i) = xTop ∨ value (sample i) ≤ xSecond :=
              fun i => hvalue_split (sample i)
            change
              hasPredTopValuesWithSecondBound k xTop xSecond
                  (fun i => value (sample i)) ↔
                (successIndexSet (fun ω => value ω = xTop) sample).card =
                  k - 1
            rw [hasPredTopValuesWithSecondBound_iff_topValueCount_eq
              k (fun i => value (sample i)) hsecond_lt_top hsplit_sample]
            simp [hcount]
      _ =
          (Nat.choose (Fintype.card ι) (k - 1) : ℝ) *
            q ^ (k - 1) * rho ^ (Fintype.card ι - (k - 1)) := by
            rw [pmfProduct_prob_successIndexSet_card_eq]
  have hpair :
      EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
        (fun sample newItem =>
          if oldPromoting sample ∧ value newItem = xTop then (1 : ℝ) else 0) =
        EconCSLib.pmfProb (EconCSLib.pmfProduct ι Ω itemLaw) oldPromoting *
          q := by
    unfold EconCSLib.pmfPairExp
    calc
      EconCSLib.pmfExp (EconCSLib.pmfProduct ι Ω itemLaw)
          (fun sample => EconCSLib.pmfExp itemLaw
            (fun newItem =>
              if oldPromoting sample ∧ value newItem = xTop then
                (1 : ℝ)
              else 0))
          =
          EconCSLib.pmfExp (EconCSLib.pmfProduct ι Ω itemLaw)
            (fun sample =>
              (if oldPromoting sample then (1 : ℝ) else 0) * q) := by
            refine EconCSLib.pmfExp_congr _ ?_
            intro sample
            by_cases hsample : oldPromoting sample
            · simp [hsample, q, EconCSLib.pmfProb]
            · simp [hsample]
      _ =
          EconCSLib.pmfProb (EconCSLib.pmfProduct ι Ω itemLaw) oldPromoting *
            q := by
            rw [EconCSLib.pmfExp_mul_const]
            rfl
  have hk_pred_succ : (k - 1) + 1 = k :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hk_pos)
  have hrho_exp :
      Fintype.card ι - (k - 1) = Fintype.card ι + 1 - k := by
    omega
  calc
    EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
        (fun sample newItem =>
          if hasPredTopValuesWithSecondBound k xTop xSecond
              (fun i => value (sample i)) ∧
            value newItem = xTop then (1 : ℝ) else 0)
        =
        EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
          (fun sample newItem =>
            if oldPromoting sample ∧ value newItem = xTop then (1 : ℝ) else 0) := rfl
    _ =
        ((Nat.choose (Fintype.card ι) (k - 1) : ℝ) *
          q ^ (k - 1) * rho ^ (Fintype.card ι - (k - 1))) * q := by
          rw [hpair, hold_eq]
    _ =
        finiteDiscreteTopMassPromotingEvent k (Fintype.card ι)
          (EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
          (EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) := by
          unfold finiteDiscreteTopMassPromotingEvent
          dsimp [q, rho]
          calc
            ((Nat.choose (Fintype.card ι) (k - 1) : ℝ) *
                (EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop)) ^ (k - 1) *
                  (EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) ^
                    (Fintype.card ι - (k - 1))) *
                EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop)
                =
                (Nat.choose (Fintype.card ι) (k - 1) : ℝ) *
                  ((EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop)) ^
                    (k - 1) *
                    EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop)) *
                  (EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) ^
                    (Fintype.card ι - (k - 1)) := by
                  ring
            _ =
                (Nat.choose (Fintype.card ι) (k - 1) : ℝ) *
                  (EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop)) ^ k *
                  (EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) ^
                    (Fintype.card ι + 1 - k) := by
                  rw [← pow_succ,
                    hk_pred_succ, hrho_exp]

/--
Source Theorem 1(i), iid scalar marginal identity on an arbitrary finite old
sample index type: the expected top-`k` value for `Option ι` minus that for `ι`
is exactly the pair expectation of adding one independent draw.
-/
theorem paper_theorem1_i_finite_discrete_iid_option_marginal_identity
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) :
    iidTopKExpectedOn (Option ι) Ω itemLaw k value -
        iidTopKExpectedOn ι Ω itemLaw k value =
      EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
        (fun sample newItem =>
          topKSumOn k
              (extendSample (fun i => value (sample i)) (value newItem)) -
            topKSumOn k (fun i => value (sample i))) := by
  classical
  unfold iidTopKExpectedOn
  rw [pmfExp_pmfProduct_option_eq_pairExp]
  have hignore :
      EconCSLib.pmfExp (EconCSLib.pmfProduct ι Ω itemLaw)
          (fun sample : ι → Ω =>
            topKSumOn k (fun i => value (sample i))) =
        EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
          (fun sample _newItem =>
            topKSumOn k (fun i => value (sample i))) := by
    simpa using
      (EconCSLib.pmfPairExp_ignore_right
        (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
        (fun sample : ι → Ω =>
          topKSumOn k (fun i => value (sample i)))).symm
  calc
    EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
        (fun sample newItem =>
          topKSumOn k (fun x => value (extendDraw sample newItem x))) -
        EconCSLib.pmfExp (EconCSLib.pmfProduct ι Ω itemLaw)
          (fun sample : ι → Ω =>
            topKSumOn k (fun i => value (sample i)))
        =
        EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
          (fun sample newItem =>
            topKSumOn k (fun x => value (extendDraw sample newItem x))) -
          EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
            (fun sample _newItem =>
              topKSumOn k (fun i => value (sample i))) := by
          rw [hignore]
    _ =
        EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
          (fun sample newItem =>
            topKSumOn k (fun x => value (extendDraw sample newItem x)) -
              topKSumOn k (fun i => value (sample i))) := by
          rw [← pmfPairExp_sub]
    _ =
        EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
          (fun sample newItem =>
            topKSumOn k
                (extendSample (fun i => value (sample i)) (value newItem)) -
              topKSumOn k (fun i => value (sample i))) := by
          unfold EconCSLib.pmfPairExp
          refine EconCSLib.pmfExp_congr _ ?_
          intro sample
          refine EconCSLib.pmfExp_congr _ ?_
          intro newItem
          change
            topKSumOn k (fun x => value (extendDraw sample newItem x)) -
                topKSumOn k (fun i => value (sample i)) =
              topKSumOn k
                  (extendSample (fun i => value (sample i)) (value newItem)) -
                topKSumOn k (fun i => value (sample i))
          congr 1
          apply congrArg (topKSumOn k)
          funext x
          cases x <;> rfl

/--
Source Theorem 1(i), iid finite-discrete upper scalar marginal bound on an
arbitrary finite old sample index type.
-/
theorem paper_theorem1_i_finite_discrete_iid_option_upper_marginal_failure_tail
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) {xTop : ℝ}
    (hxTop_nonneg : 0 ≤ xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    [DecidablePred
      (fun sample : ι → Ω =>
        ¬ hasKTopValues k xTop (fun i => value (sample i)))] :
    iidTopKExpectedOn (Option ι) Ω itemLaw k value -
        iidTopKExpectedOn ι Ω itemLaw k value ≤
      (k : ℝ) * xTop *
        finiteDiscreteTopMassFailureTail k (Fintype.card ι)
          (EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
          (EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) := by
  classical
  rw [paper_theorem1_i_finite_discrete_iid_option_marginal_identity]
  calc
    EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
        (fun sample newItem =>
          topKSumOn k
              (extendSample (fun i => value (sample i)) (value newItem)) -
            topKSumOn k (fun i => value (sample i)))
        ≤
        (k : ℝ) * xTop *
          EconCSLib.pmfProb (EconCSLib.pmfProduct ι Ω itemLaw)
            (fun sample : ι → Ω =>
              ¬ hasKTopValues k xTop (fun i => value (sample i))) :=
          pmfPairExp_topK_extend_sub_le_top_failure_prob
            (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
            k value hxTop_nonneg hvalue_le
    _ =
        (k : ℝ) * xTop *
          finiteDiscreteTopMassFailureTail k (Fintype.card ι)
            (EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
            (EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) := by
          rw [paper_theorem1_i_finite_discrete_product_failure_tail_exact]

/--
Source Theorem 1(i), iid finite-discrete lower scalar marginal bound on an
arbitrary finite old sample index type.
-/
theorem paper_theorem1_i_finite_discrete_iid_option_lower_marginal_promoting_event
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hxTop_nonneg : 0 ≤ xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    [∀ sample : ι → Ω,
      DecidablePred
        (fun newItem : Ω =>
          hasPredTopValuesWithSecondBound k xTop xSecond
              (fun i => value (sample i)) ∧
            value newItem = xTop)] :
    (xTop - xSecond) *
        finiteDiscreteTopMassPromotingEvent k (Fintype.card ι)
          (EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
          (EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
      ≤
        iidTopKExpectedOn (Option ι) Ω itemLaw k value -
          iidTopKExpectedOn ι Ω itemLaw k value := by
  classical
  rw [paper_theorem1_i_finite_discrete_iid_option_marginal_identity]
  calc
    (xTop - xSecond) *
        finiteDiscreteTopMassPromotingEvent k (Fintype.card ι)
          (EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
          (EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
        =
        (xTop - xSecond) *
          EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
            (fun sample newItem =>
              if hasPredTopValuesWithSecondBound k xTop xSecond
                  (fun i => value (sample i)) ∧
                value newItem = xTop then (1 : ℝ) else 0) := by
          rw [paper_theorem1_i_finite_discrete_product_promoting_event_exact
            (itemLaw := itemLaw) (k := k) (value := value)
            (xTop := xTop) (xSecond := xSecond)
            hk_pos hsecond_lt_top hvalue_split]
    _ ≤
        EconCSLib.pmfPairExp (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
          (fun sample newItem =>
            topKSumOn k
                (extendSample (fun i => value (sample i)) (value newItem)) -
              topKSumOn k (fun i => value (sample i))) :=
          top_gap_mul_pmfPairExp_promoting_indicator_le_topK_extend_sub
            (EconCSLib.pmfProduct ι Ω itemLaw) itemLaw
            k value hk_pos hxTop_nonneg hxSecond_nonneg hsecond_le_top

/--
Source Theorem 1(i), scalar `h(a)` upper marginal bound for the finite-discrete
i.i.d. top-`k` expectation.
-/
theorem paper_theorem1_i_finite_discrete_scalar_upper_marginal_failure_tail
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k a : ℕ) (value : Ω → ℝ) {xTop : ℝ}
    (hxTop_nonneg : 0 ≤ xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    [DecidablePred
      (fun sample : Fin a → Ω =>
        ¬ hasKTopValues k xTop (fun i => value (sample i)))] :
    finiteDiscreteIidTopKExpected Ω itemLaw k value (a + 1) -
        finiteDiscreteIidTopKExpected Ω itemLaw k value a ≤
      (k : ℝ) * xTop *
        finiteDiscreteTopMassFailureTail k a
          (EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
          (EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop)) := by
  simpa [finiteDiscreteIidTopKExpected,
    iidTopKExpectedOn_option_fin_eq_succ]
    using
      paper_theorem1_i_finite_discrete_iid_option_upper_marginal_failure_tail
        (ι := Fin a) itemLaw k value hxTop_nonneg hvalue_le

/--
Source Theorem 1(i), scalar `h(a)` lower marginal bound for the finite-discrete
i.i.d. top-`k` expectation.
-/
theorem paper_theorem1_i_finite_discrete_scalar_lower_marginal_promoting_event
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k a : ℕ) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hxTop_nonneg : 0 ≤ xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    [∀ sample : Fin a → Ω,
      DecidablePred
        (fun newItem : Ω =>
          hasPredTopValuesWithSecondBound k xTop xSecond
              (fun i => value (sample i)) ∧
            value newItem = xTop)] :
    (xTop - xSecond) *
        finiteDiscreteTopMassPromotingEvent k a
          (EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
          (EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
      ≤
        finiteDiscreteIidTopKExpected Ω itemLaw k value (a + 1) -
          finiteDiscreteIidTopKExpected Ω itemLaw k value a := by
  simpa [finiteDiscreteIidTopKExpected,
    iidTopKExpectedOn_option_fin_eq_succ]
    using
      paper_theorem1_i_finite_discrete_iid_option_lower_marginal_promoting_event
        (ι := Fin a) itemLaw k value hk_pos hxTop_nonneg hxSecond_nonneg
        hsecond_le_top hsecond_lt_top hvalue_split

/--
Source Theorem 1(i), small-count lower marginal bound for the finite-discrete
i.i.d. top-`k` expectation.

Before the old sample has `k` coordinates, a new top-support item can always
be added to a maximizing old candidate set, so the marginal is at least
`xTop` times the top-support probability.
-/
theorem paper_theorem1_i_finite_discrete_scalar_lower_marginal_top_event_before_k
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k a : ℕ) (value : Ω → ℝ) {xTop : ℝ}
    (ha_lt_k : a < k)
    (hxTop_nonneg : 0 ≤ xTop) :
    xTop * EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop) ≤
      finiteDiscreteIidTopKExpected Ω itemLaw k value (a + 1) -
        finiteDiscreteIidTopKExpected Ω itemLaw k value a := by
  have hpair :=
    top_value_mul_pmfProb_le_pmfPairExp_topK_extend_sub_of_card_lt
      (ι := Fin a)
      (sampleLaw := EconCSLib.pmfProduct (Fin a) Ω itemLaw)
      itemLaw k value (xTop := xTop)
      (by simpa using ha_lt_k) hxTop_nonneg
  have hpair_eq :=
    pmfPairExp_topK_extend_sub_eq_iidTopKExpectedOn_option_sub
      (ι := Fin a) itemLaw k value
  have hoption :
      xTop * EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop) ≤
        iidTopKExpectedOn (Option (Fin a)) Ω itemLaw k value -
          iidTopKExpectedOn (Fin a) Ω itemLaw k value := by
    simpa [hpair_eq] using hpair
  simpa [finiteDiscreteIidTopKExpected,
    iidTopKExpectedOn_option_fin_eq_succ]
    using hoption

/--
Source Theorem 1(i), equations (81)-(83) binomial tail estimate.

For finite discrete `D`, the probability that fewer than `k` draws hit the top
support point is bounded by a fixed polynomial times the geometric non-top
tail.
-/
theorem paper_theorem1_i_finite_discrete_top_mass_failure_tail_bound
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a)
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (hrho_nonneg : 0 ≤ rho) (hrho_le_one : rho ≤ 1) :
    finiteDiscreteTopMassFailureTail k a q rho ≤
      (k : ℝ) * (a : ℝ) ^ k * rho ^ (a + 1 - k) :=
  finiteDiscreteTopMassFailureTail_le_polynomial_geometric
    hk_pos hk_le_a hq_nonneg hq_le_one hrho_nonneg hrho_le_one

/--
Source Theorem 1(i), binomial upper tail in certificate form with the fixed
`k-1` exponent shift absorbed into the constant.
-/
theorem paper_theorem1_i_finite_discrete_top_mass_failure_tail_bound_at_a
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a)
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_le_one : rho ≤ 1) :
    finiteDiscreteTopMassFailureTail k a q rho ≤
      ((k : ℝ) * (rho ^ (k - 1))⁻¹) * (a : ℝ) ^ k * rho ^ a :=
  finiteDiscreteTopMassFailureTail_le_polynomial_geometric_at_a
    hk_pos hk_le_a hq_nonneg hq_le_one hrho_pos hrho_le_one

/--
Source Theorem 1(i), off-by-one bridge for the upper marginal: the failure event
in the old `a-1` sample is controlled by the certificate tail at sample size
`a`, losing only the fixed factor `rho⁻¹`.
-/
theorem paper_theorem1_i_finite_discrete_top_mass_failure_tail_pred_le_inv_mul
    {k a : ℕ} {q rho : ℝ}
    (ha_pos : 0 < a) (hq_nonneg : 0 ≤ q) (hrho_pos : 0 < rho) :
    finiteDiscreteTopMassFailureTail k (a - 1) q rho ≤
      rho⁻¹ * finiteDiscreteTopMassFailureTail k a q rho :=
  finiteDiscreteTopMassFailureTail_pred_le_inv_mul
    ha_pos hq_nonneg hrho_pos

/--
Source Theorem 1(i), exact `k-1` top-count event used for the lower marginal
estimate in the finite-discrete branch.
-/
theorem paper_theorem1_i_finite_discrete_top_mass_promoting_event_lower_bound
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_pred_le_a : k - 1 ≤ a)
    (hq_nonneg : 0 ≤ q) (hrho_nonneg : 0 ≤ rho) :
    q ^ k * rho ^ (a + 1 - k) ≤
      finiteDiscreteTopMassPromotingEvent k a q rho :=
  finiteDiscreteTopMassPromotingEvent_lower_geometric
    hk_pos hk_pred_le_a hq_nonneg hrho_nonneg

/--
Source Theorem 1(i), exact `k-1` top-count lower event in certificate form with
the fixed exponent shift absorbed into the constant.
-/
theorem paper_theorem1_i_finite_discrete_top_mass_promoting_event_lower_bound_at_a
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a)
    (hq_nonneg : 0 ≤ q) (hrho_pos : 0 < rho) :
    q ^ k * (rho ^ (k - 1))⁻¹ * rho ^ a ≤
      finiteDiscreteTopMassPromotingEvent k a q rho :=
  finiteDiscreteTopMassPromotingEvent_lower_geometric_at_a
    hk_pos hk_le_a hq_nonneg hrho_pos

/--
Source Lemma D.1 endpoint / Definition 2 bridge.

Once the finite separable optimizer analysis supplies an asymptotic homogeneity
target for all optima, any selected sequence of finite optima has type shares
converging to the corresponding profile.
-/
theorem paper_lemmaD1_optimizer_sequence_limit_of_asymptotic_homogeneity
    {T : ℕ} {Mseq : ℕ → ConsumptionModel T}
    {G : GammaHomogeneityProfile T}
    (seq : OptimalAllocationSequence Mseq)
    (h : ConsumptionModel.AsymptoticHomogeneity Mseq G) :
    seq.toAllocationSequence.ConvergesToProfile G := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity h

/--
Source Theorem 1(i), finite-discrete i.i.d. conditional item values, exposed at
the reusable top-`k` certificate seam.
-/
theorem paper_theorem1_i_finite_discrete_sequence_homogeneity_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k (uniformProfile T)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptotic_homogeneity

/--
Source Theorem 1(i), finite-discrete proof seam below the abstract top-`k`
certificate.

For finite-discrete conditional values, the remaining distribution-specific
work is to prove a sublinear finite-FOC dominance estimate for unweighted count
gaps. Once that estimate is supplied, the reusable FOC bridge gives the paper's
`0`-homogeneity conclusion.
-/
theorem
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun _ : ItemType T => (1 : ℝ)) (uniformProfile T)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 1(i), top-`k` marginal proof seam for the finite-discrete branch.

This is the paper-facing version of the finite-optimization bridge: once the
finite-discrete order-statistic calculation proves the top-`k`
backward/forward marginal dominance for sublinear count gaps, the
`0`-homogeneity conclusion follows.
-/
theorem
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_topk_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert : TopKUniformSublinearFOCCertificate O likelihood k) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 1(i), eventual count-floor bridge for finite-discrete top-`k`
order-statistic estimates.

If large source counts have lower last-item marginal value than every
destination count at or below a fixed floor, then every sufficiently large
finite optimum gives every type more than that floor. This verifies the
interiority/floor side condition used by the eventual top-`k` FOC seam.
-/
theorem
    paper_theorem1_i_finite_discrete_eventual_count_floor_of_topk_marginal_dominance
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (hcert : TopKUniformCountFloorCertificate O likelihood k) :
    ∀ᶠ N in Filter.atTop,
      ∀ a : CountAllocation T, 0 < N →
        (O.toConsumptionModel likelihood k).IsOptimalAtTotal N a →
        ∀ t, hcert.floor < a.count t :=
  hcert.count_floor_eventually

/--
Source Theorem 1(i), eventual top-`k` marginal proof seam.

This is the form closest to the finite-discrete order-statistic calculation in
the paper: the large-gap marginal comparison and the count-floor fact may both
hold only eventually.  The finite-prefix bridge converts those eventual
estimates into the clean sublinear FOC certificate, yielding the paper's
`0`-homogeneity conclusion.
-/
theorem
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_eventual_topk_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert : TopKUniformEventualSublinearFOCCertificate O likelihood k) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 1(i), combined finite-discrete top-`k` proof seam.

This is the distribution-estimate interface left by the verified optimization
layer: prove a count-floor marginal-dominance certificate, prove a
zero-convergent large-gap marginal estimate above that floor, and the paper's
`0`-homogeneity conclusion follows.
-/
theorem
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_count_floor_and_large_gap
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hfloor : TopKUniformCountFloorCertificate O likelihood k)
    (base_error : ℕ → ℝ)
    (base_error_nonneg : ∀ N, 0 ≤ base_error N)
    (base_error_tends_to_zero : EconCSLib.Math.TendsToZero base_error)
    (large_gap_backward_lt_forward_after_floor :
      ∀ᶠ N in Filter.atTop,
        ∀ src dst qsrc qdst,
          qsrc ≤ N →
          qdst ≤ N →
          hfloor.floor < qsrc →
          hfloor.floor < qdst →
          base_error N * (N : ℝ) < (qsrc : ℝ) - (qdst : ℝ) →
          likelihood src *
              (O.expectedTopSum k src qsrc -
                O.expectedTopSum k src (qsrc - 1)) <
            likelihood dst *
              (O.expectedTopSum k dst (qdst + 1) -
                O.expectedTopSum k dst qdst)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  let hcert :=
    TopKUniformEventualSublinearFOCCertificate.of_count_floor_certificate
      hfloor base_error base_error_nonneg base_error_tends_to_zero
      large_gap_backward_lt_forward_after_floor
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 1(i), geometric marginal-bound proof seam.

This packages the finite-discrete order-statistic estimates in the source proof:
a geometric lower tail, a polynomial-times-geometric upper tail, a count-floor
dominance bound, and a sublinear integer gap whose polynomial-geometric product
is eventually small.  Those estimates imply the paper's `0`-homogeneity
conclusion.
-/
theorem
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_geometric_marginal_bounds
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert : TopKUniformGeometricMarginalBoundCertificate O likelihood k) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 1(i), geometric tail proof seam.

This form matches the finite-discrete proof more closely: a positive floor
lower bound and polynomial-geometric upper/lower marginal tails are enough to
derive the count-floor bridge, then the verified optimization layer yields the
paper's `0`-homogeneity conclusion.
-/
theorem
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_geometric_tail_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert : TopKUniformGeometricTailCertificate O likelihood k) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 1(i), scalar finite-discrete binomial-event proof seam.

This is the closest verified endpoint to the paper's scalar `h(a)` proof: once
the common top-`k` marginal of the finite-support distribution is bounded above
by the failure event and below by the exact `k-1` top-count promoting event,
the weighted finite optimizer still converges to equal representation.
-/
theorem
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_unweighted_binomial_event_bounds
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (q rho : ℝ)
    (hk_pos : 0 < k)
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (floor : ℕ) (hk_le_floor_succ : k ≤ floor + 1)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (smallForward backwardLoss forwardGain : ℝ)
    (smallForward_pos : 0 < smallForward)
    (backwardLoss_pos : 0 < backwardLoss)
    (forwardGain_pos : 0 < forwardGain)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      EconCSLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹)
    (unweighted_forward_lower_to_floor :
      ∀ dst qdst,
        qdst ≤ floor →
          smallForward ≤
            O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst)
    (unweighted_backward_upper_by_failure_tail :
      ∀ src qsrc,
        floor < qsrc →
          O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1) ≤
            backwardLoss * finiteDiscreteTopMassFailureTail k qsrc q rho)
    (unweighted_forward_lower_by_promoting_event :
      ∀ dst qdst,
        floor < qdst →
          forwardGain * finiteDiscreteTopMassPromotingEvent k qdst q rho ≤
            O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  let hcert :=
    TopKUniformGeometricTailCertificate.of_unweighted_binomial_event_bounds
      (O := O) (likelihood := likelihood) (k := k)
      q rho hk_pos hq_pos hq_le_one hrho_pos hrho_lt_one floor
      hk_le_floor_succ likelihoodLower likelihoodUpper
      likelihoodLower_pos likelihoodUpper_pos likelihoodLower_le
      likelihood_le_upper smallForward backwardLoss forwardGain
      smallForward_pos backwardLoss_pos forwardGain_pos gap
      gap_error_tends_to_zero gap_dominance_eventually
      unweighted_forward_lower_to_floor
      unweighted_backward_upper_by_failure_tail
      unweighted_forward_lower_by_promoting_event
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 1(i), scalar `h(a)` binomial-event proof seam.

This is the paper's i.i.d. conditional-value form: all types share the same
scalar expected top-`k` function `h`, and the only distribution-side work is to
prove the two scalar marginal bounds for `h`.
-/
theorem
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_scalar_binomial_event_bounds
    {T : ℕ} [NeZero T]
    (h : ℕ → ℝ) (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ => (TopKValueOracle.common T h).toConsumptionModel likelihood k))
    (q rho : ℝ)
    (hk_pos : 0 < k)
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (floor : ℕ) (hk_le_floor_succ : k ≤ floor + 1)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (smallForward backwardLoss forwardGain : ℝ)
    (smallForward_pos : 0 < smallForward)
    (backwardLoss_pos : 0 < backwardLoss)
    (forwardGain_pos : 0 < forwardGain)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      EconCSLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹)
    (scalar_forward_lower_to_floor :
      ∀ qdst,
        qdst ≤ floor →
          smallForward ≤ h (qdst + 1) - h qdst)
    (scalar_backward_upper_by_failure_tail :
      ∀ qsrc,
        floor < qsrc →
          h qsrc - h (qsrc - 1) ≤
            backwardLoss * finiteDiscreteTopMassFailureTail k qsrc q rho)
    (scalar_forward_lower_by_promoting_event :
      ∀ qdst,
        floor < qdst →
          forwardGain * finiteDiscreteTopMassPromotingEvent k qdst q rho ≤
            h (qdst + 1) - h qdst) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_unweighted_binomial_event_bounds
      (TopKValueOracle.common T h) likelihood k seq q rho hk_pos hq_pos
      hq_le_one hrho_pos hrho_lt_one floor hk_le_floor_succ
      likelihoodLower likelihoodUpper likelihoodLower_pos likelihoodUpper_pos
      likelihoodLower_le likelihood_le_upper smallForward backwardLoss
      forwardGain smallForward_pos backwardLoss_pos forwardGain_pos gap
      gap_error_tends_to_zero gap_dominance_eventually
      (by
        intro _dst qdst hqdst
        simpa using scalar_forward_lower_to_floor qdst hqdst)
      (by
        intro _src qsrc hqsrc
        simpa using scalar_backward_upper_by_failure_tail qsrc hqsrc)
      (by
        intro _dst qdst hqdst
        simpa using scalar_forward_lower_by_promoting_event qdst hqdst)

/--
Source Theorem 1(i), finite-discrete i.i.d. scalar marginal assembly.

This specializes the scalar binomial-event certificate to the actual
finite-support i.i.d. top-`k` expectation `h(a)`.  The top-support probability
`q`, non-top probability `rho`, upper marginal constant, and lower marginal
constant are tied to the item distribution; the verified order-statistic
lemmas discharge the large-count marginal bounds.  The remaining assumptions
are the paper's small-count floor lower bound and asymptotic gap schedule.
-/
theorem
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (TopKValueOracle.common T
            (finiteDiscreteIidTopKExpected Ω itemLaw k value)).toConsumptionModel
              likelihood k))
    (q rho : ℝ)
    (hq_def : q = EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (floor : ℕ) (hk_le_floor_succ : k ≤ floor + 1)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (smallForward backwardLoss forwardGain : ℝ)
    (smallForward_pos : 0 < smallForward)
    (backwardLoss_eq : backwardLoss = (k : ℝ) * xTop * rho⁻¹)
    (forwardGain_eq : forwardGain = xTop - xSecond)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      EconCSLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹)
    (scalar_forward_lower_to_floor :
      ∀ qdst,
        qdst ≤ floor →
          smallForward ≤
            finiteDiscreteIidTopKExpected Ω itemLaw k value (qdst + 1) -
              finiteDiscreteIidTopKExpected Ω itemLaw k value qdst) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  classical
  have hq_le_one : q ≤ 1 := by
    rw [hq_def]
    exact EconCSLib.pmfProb_le_one itemLaw (fun ω => value ω = xTop)
  have hrho_eq_one_sub : rho = 1 - q := by
    calc
      rho = EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop) :=
        hrho_def
      _ = 1 - EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop) := by
        exact EconCSLib.pmfProb_compl itemLaw (fun ω => value ω = xTop)
      _ = 1 - q := by
        rw [← hq_def]
  have hrho_lt_one : rho < 1 := by
    rw [hrho_eq_one_sub]
    linarith
  have backwardLoss_pos : 0 < backwardLoss := by
    rw [backwardLoss_eq]
    exact mul_pos (mul_pos (Nat.cast_pos.mpr hk_pos) hxTop_pos)
      (inv_pos.mpr hrho_pos)
  have forwardGain_pos : 0 < forwardGain := by
    rw [forwardGain_eq]
    exact sub_pos.mpr hsecond_lt_top
  exact
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_scalar_binomial_event_bounds
      (h := finiteDiscreteIidTopKExpected Ω itemLaw k value)
      likelihood k seq q rho hk_pos hq_pos hq_le_one hrho_pos hrho_lt_one
      floor hk_le_floor_succ likelihoodLower likelihoodUpper
      likelihoodLower_pos likelihoodUpper_pos likelihoodLower_le
      likelihood_le_upper smallForward backwardLoss forwardGain
      smallForward_pos backwardLoss_pos forwardGain_pos gap
      gap_error_tends_to_zero gap_dominance_eventually
      scalar_forward_lower_to_floor
      (by
        intro qsrc hfloor_lt
        have hqsrc_pos : 0 < qsrc :=
          lt_of_le_of_lt (Nat.zero_le floor) hfloor_lt
        have hsucc : qsrc - 1 + 1 = qsrc :=
          Nat.sub_add_cancel (Nat.succ_le_of_lt hqsrc_pos)
        have hupper :=
          paper_theorem1_i_finite_discrete_scalar_upper_marginal_failure_tail
            (itemLaw := itemLaw) (k := k) (a := qsrc - 1)
            (value := value) (xTop := xTop) hxTop_pos.le hvalue_le
        have hupper_qrho :
            finiteDiscreteIidTopKExpected Ω itemLaw k value
                  ((qsrc - 1) + 1) -
                finiteDiscreteIidTopKExpected Ω itemLaw k value (qsrc - 1) ≤
              (k : ℝ) * xTop *
                finiteDiscreteTopMassFailureTail k (qsrc - 1) q rho := by
          simpa [← hq_def, ← hrho_def] using hupper
        have htail :
            finiteDiscreteTopMassFailureTail k (qsrc - 1) q rho ≤
              rho⁻¹ * finiteDiscreteTopMassFailureTail k qsrc q rho :=
          paper_theorem1_i_finite_discrete_top_mass_failure_tail_pred_le_inv_mul
            (k := k) (a := qsrc) (q := q) (rho := rho)
            hqsrc_pos hq_pos.le hrho_pos
        have hscale_nonneg : 0 ≤ (k : ℝ) * xTop :=
          mul_nonneg (Nat.cast_nonneg k) hxTop_pos.le
        calc
          finiteDiscreteIidTopKExpected Ω itemLaw k value qsrc -
              finiteDiscreteIidTopKExpected Ω itemLaw k value (qsrc - 1)
              =
            finiteDiscreteIidTopKExpected Ω itemLaw k value
                ((qsrc - 1) + 1) -
              finiteDiscreteIidTopKExpected Ω itemLaw k value (qsrc - 1) := by
                rw [hsucc]
          _ ≤
              (k : ℝ) * xTop *
                finiteDiscreteTopMassFailureTail k (qsrc - 1) q rho :=
                hupper_qrho
          _ ≤
              (k : ℝ) * xTop *
                (rho⁻¹ * finiteDiscreteTopMassFailureTail k qsrc q rho) :=
                mul_le_mul_of_nonneg_left htail hscale_nonneg
          _ =
              ((k : ℝ) * xTop * rho⁻¹) *
                finiteDiscreteTopMassFailureTail k qsrc q rho := by
                ring
          _ =
              backwardLoss *
                finiteDiscreteTopMassFailureTail k qsrc q rho := by
                rw [backwardLoss_eq])
      (by
        intro qdst _hfloor_lt
        have hlower :=
          paper_theorem1_i_finite_discrete_scalar_lower_marginal_promoting_event
            (itemLaw := itemLaw) (k := k) (a := qdst)
            (value := value) (xTop := xTop) (xSecond := xSecond)
            hk_pos hxTop_pos.le hxSecond_nonneg hsecond_le_top hsecond_lt_top
            hvalue_split
        simpa [← hq_def, ← hrho_def, forwardGain_eq] using hlower)

/--
Source Theorem 1(i), finite-discrete i.i.d. scalar assembly with the small-count
floor discharged.

For `floor = k - 1`, every destination count at or below the floor has fewer
than `k` old items.  The verified small-count marginal lemma supplies the
uniform floor lower bound `xTop * q`, so the only remaining source-side
certificate is the asymptotic gap schedule.
-/
theorem
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (TopKValueOracle.common T
            (finiteDiscreteIidTopKExpected Ω itemLaw k value)).toConsumptionModel
              likelihood k))
    (q rho : ℝ)
    (hq_def : q = EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (backwardLoss forwardGain : ℝ)
    (backwardLoss_eq : backwardLoss = (k : ℝ) * xTop * rho⁻¹)
    (forwardGain_eq : forwardGain = xTop - xSecond)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      EconCSLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds
      itemLaw value likelihood k seq q rho hq_def hrho_def hk_pos hxTop_pos
      hxSecond_nonneg hsecond_le_top hsecond_lt_top hvalue_le hvalue_split
      hq_pos hrho_pos (k - 1) (by omega) likelihoodLower likelihoodUpper
      likelihoodLower_pos likelihoodUpper_pos likelihoodLower_le
      likelihood_le_upper (xTop * q) backwardLoss forwardGain
      (mul_pos hxTop_pos hq_pos) backwardLoss_eq forwardGain_eq gap
      gap_error_tends_to_zero gap_dominance_eventually
      (by
        intro qdst hqdst
        have hqdst_lt : qdst < k := by omega
        have hsmall :=
          paper_theorem1_i_finite_discrete_scalar_lower_marginal_top_event_before_k
            (itemLaw := itemLaw) (k := k) (a := qdst) (value := value)
            (xTop := xTop) hqdst_lt hxTop_pos.le
        simpa [← hq_def] using hsmall)

/--
Source Theorem 1(i), finite-discrete i.i.d. scalar assembly from a standard
gap-decay asymptotic.

This replaces the expanded constant-heavy large-gap dominance assumption with
the cleaner analytic obligation that `(N : ℝ)^k * rho^(gap N)` tends to zero.
The theorem verifies the surrounding positive constants and derives the
eventual inequality required by the geometric-tail certificate.
-/
theorem
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor_of_gap_decay
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (TopKValueOracle.common T
            (finiteDiscreteIidTopKExpected Ω itemLaw k value)).toConsumptionModel
              likelihood k))
    (q rho : ℝ)
    (hq_def : q = EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (backwardLoss forwardGain : ℝ)
    (backwardLoss_eq : backwardLoss = (k : ℝ) * xTop * rho⁻¹)
    (forwardGain_eq : forwardGain = xTop - xSecond)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      EconCSLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_polynomial_geometric_tends_to_zero :
      Filter.Tendsto
        (fun N : ℕ => (N : ℝ) ^ k * rho ^ (gap N))
        Filter.atTop (nhds 0)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  have forwardGain_pos : 0 < forwardGain := by
    rw [forwardGain_eq]
    exact sub_pos.mpr hsecond_lt_top
  have hright_pos :
      0 <
        (likelihoodLower * forwardGain) * q ^ k *
          (rho ^ (k - 1))⁻¹ := by
    positivity
  have gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹ := by
    let A : ℝ :=
      (likelihoodUpper * backwardLoss) *
        ((k : ℝ) * (rho ^ (k - 1))⁻¹)
    let B : ℝ :=
      (likelihoodLower * forwardGain) * q ^ k *
        (rho ^ (k - 1))⁻¹
    have hB_pos : 0 < B := by
      simpa [B] using hright_pos
    have hlim :
        Filter.Tendsto
          (fun N : ℕ => A * ((N : ℝ) ^ k * rho ^ (gap N)))
          Filter.atTop (nhds 0) :=
      by
        simpa using gap_polynomial_geometric_tends_to_zero.const_mul A
    have hevent : ∀ᶠ N : ℕ in Filter.atTop,
        A * ((N : ℝ) ^ k * rho ^ (gap N)) < B :=
      hlim.eventually (Iio_mem_nhds hB_pos)
    filter_upwards [hevent] with N hN
    simpa [A, B, mul_assoc] using hN
  exact
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor
      itemLaw value likelihood k seq q rho hq_def hrho_def hk_pos hxTop_pos
      hxSecond_nonneg hsecond_le_top hsecond_lt_top hvalue_le hvalue_split
      hq_pos hrho_pos likelihoodLower likelihoodUpper likelihoodLower_pos
      likelihoodUpper_pos likelihoodLower_le likelihood_le_upper backwardLoss
      forwardGain backwardLoss_eq forwardGain_eq gap gap_error_tends_to_zero
      gap_dominance_eventually

/--
Source Theorem 1(i), finite-discrete i.i.d. scalar assembly with the concrete
sublinear square-root gap schedule.

This closes the finite-discrete scalar top-support branch up to the explicit
finite-support assumptions in the statement: the floor is `k - 1`, the gap is
`Nat.sqrt N`, the backward and forward constants are the source-derived
`k * xTop * rho⁻¹` and `xTop - xSecond`, and the square-root gap is verified to
be sublinear while killing the polynomial-geometric upper tail.
-/
theorem
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_sqrt_gap
    {T : ℕ} [NeZero T] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (value : Ω → ℝ) {xTop xSecond : ℝ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (TopKValueOracle.common T
            (finiteDiscreteIidTopKExpected Ω itemLaw k value)).toConsumptionModel
              likelihood k))
    (q rho : ℝ)
    (hq_def : q = EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop))
    (hrho_def :
      rho = EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop))
    (hk_pos : 0 < k)
    (hxTop_pos : 0 < xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_le : ∀ ω, value ω ≤ xTop)
    (hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond)
    (hq_pos : 0 < q)
    (hrho_pos : 0 < rho)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  have hrho_eq_one_sub : rho = 1 - q := by
    calc
      rho = EconCSLib.pmfProb itemLaw (fun ω => ¬ value ω = xTop) :=
        hrho_def
      _ = 1 - EconCSLib.pmfProb itemLaw (fun ω => value ω = xTop) := by
        exact EconCSLib.pmfProb_compl itemLaw (fun ω => value ω = xTop)
      _ = 1 - q := by
        rw [← hq_def]
  have hrho_lt_one : rho < 1 := by
    rw [hrho_eq_one_sub]
    linarith
  exact
    paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor_of_gap_decay
      itemLaw value likelihood k seq q rho hq_def hrho_def hk_pos hxTop_pos
      hxSecond_nonneg hsecond_le_top hsecond_lt_top hvalue_le hvalue_split
      hq_pos hrho_pos likelihoodLower likelihoodUpper likelihoodLower_pos
      likelihoodUpper_pos likelihoodLower_le likelihood_le_upper
      ((k : ℝ) * xTop * rho⁻¹) (xTop - xSecond) rfl rfl
      (fun N => Nat.sqrt N) finiteDiscrete_nat_sqrt_gap_error_tendsToZero
      (finiteDiscrete_nat_sqrt_gap_polynomial_geometric_tends_to_zero
        k hrho_pos hrho_lt_one)

/--
Two-point finite-discrete top-one model used as a fully formalized instance of
source Theorem 1(i).  Conditional item values are Bernoulli with common success
probability `q`, so the expected top-one value for `a` items is
`1 - (1-q)^a`.
-/
noncomputable def theorem1TwoPointBernoulliTopOneModel {T : ℕ}
    (likelihood : ItemType T → ℝ) (q : ℝ) : ConsumptionModel T :=
  (BernoulliSatisfactionModel.mk likelihood (fun _ => q)).toConsumptionModel

/--
Source Theorem 1(i), fully formalized two-point finite-discrete top-one instance.

This closes the finite-discrete theorem for the Bernoulli `{0,1}` distribution
with fixed `k = 1`: every selected finite optimum converges to
`0`-homogeneity.
-/
theorem paper_theorem1_i_two_point_bernoulli_top_one_sequence_uniform_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (q : ℝ)
    (hq_pos : 0 < q) (hq_lt_one : q < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => theorem1TwoPointBernoulliTopOneModel likelihood q)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  let B : BernoulliSatisfactionModel T :=
    BernoulliSatisfactionModel.mk likelihood (fun _ => q)
  have hprob_pos : ∀ t, 0 < B.successProb t := by
    intro t
    simpa [B] using hq_pos
  have hprob_lt_one : ∀ t, B.successProb t < 1 := by
    intro t
    simpa [B] using hq_lt_one
  have hlike_pos_B : ∀ t, 0 < B.likelihood t := by
    intro t
    simpa [B] using hlike_pos t
  have hprob_eq : ∀ i j : ItemType T, B.successProb i = B.successProb j := by
    intro i j
    simp [B]
  have hasymp :
      ConsumptionModel.AsymptoticHomogeneity
        (fun _ => theorem1TwoPointBernoulliTopOneModel likelihood q)
        (uniformProfile T) := by
    simpa [B, theorem1TwoPointBernoulliTopOneModel] using
      iid_bernoulli_asymptotic_uniform_homogeneity
        B hprob_pos hprob_lt_one hlike_pos_B hprob_eq
  exact seq.convergesToProfile_of_asymptoticHomogeneity hasymp

/--
Source Theorem 1(i), direct equation (6) form for the verified two-point
finite-discrete top-one instance.
-/
theorem paper_theorem1_i_two_point_bernoulli_top_one_uniform_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (q : ℝ)
    (hq_pos : 0 < q) (hq_lt_one : q < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => theorem1TwoPointBernoulliTopOneModel likelihood q)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop (nhds (1 / (T : ℝ))) := by
  have hconv :=
    paper_theorem1_i_two_point_bernoulli_top_one_sequence_uniform_homogeneity
      likelihood q hq_pos hq_lt_one hlike_pos seq
  intro t
  simpa [AllocationSequence.representation, uniformProfile_targetShare] using
    hconv t

/--
Source Theorem 1(ii)-(iv), probability-to-optimization seam.

A reusable order-statistic scaled marginal limit gives an eventual uniform
upper/lower sandwich for every type's top-`k` marginal.
-/
theorem paper_theorem1_order_statistic_scaled_marginal_sandwich
    {T : ℕ}
    (O : TopKValueOracle T) (k : ℕ)
    (scale : ℕ → ℝ) (weight : ItemType T → ℝ)
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in Filter.atTop,
      ∀ t : ItemType T,
        (1 - ε) * (scale q * weight t) ≤
            O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q ∧
          O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q ≤
            (1 + ε) * (scale q * weight t) :=
  TopKScaledMarginalLimitCertificate.eventually_marginal_sandwich C hε

/--
Source Theorem 1(ii)-(iv), same-count marginal comparison seam.

Once the scaled marginal limit is available, a strict scaled-weight gap implies
an eventual strict ordering of same-count top-`k` marginals.
-/
theorem paper_theorem1_order_statistic_same_count_marginal_lt_of_weight_gap
    {T : ℕ}
    (O : TopKValueOracle T) (k : ℕ)
    (scale : ℕ → ℝ) (weight : ItemType T → ℝ)
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) {src dst : ItemType T}
    (hgap : (1 + ε) * weight src < (1 - ε) * weight dst) :
    ∀ᶠ q in Filter.atTop,
      O.expectedTopSum k src (q + 1) - O.expectedTopSum k src q <
        O.expectedTopSum k dst (q + 1) - O.expectedTopSum k dst q :=
  TopKScaledMarginalLimitCertificate.eventually_same_count_marginal_lt_of_weight_gap
    C hε hgap

/--
Source Theorem 1(ii), bounded upper-tail i.i.d. conditional item values,
exposed at the reusable top-`k` certificate seam.
-/
theorem paper_theorem1_ii_bounded_sequence_homogeneity_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (β : ℝ)
    (_hβ_pos : 0 < β)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k
        (gammaLikelihoodProfile likelihood (β / (β + 1)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (β / (β + 1))) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptotic_homogeneity

/--
Source Theorem 1(ii), bounded upper-tail branch from the Lemma D.1-style
sublinear FOC seam.

This is the optimization-facing bridge beneath the abstract certificate: the
remaining distribution work is to derive the scaled large-gap marginal
dominance from the bounded-support order-statistic asymptotic (paper equation
(75)).
-/
theorem paper_theorem1_ii_bounded_sequence_homogeneity_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (β : ℝ)
    (_hβ_pos : 0 < β)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (β / (β + 1)))
        (gammaLikelihoodProfile likelihood (β / (β + 1)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (β / (β + 1))) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 1(ii), bounded upper-tail branch from a floor-aware
Lemma D.1-style FOC seam.

This is the exact interface expected from the bounded-support order-statistic
asymptotic: eventual interiority plus eventual scaled large-gap marginal
dominance imply the paper's `β/(β+1)`-homogeneity conclusion.
-/
theorem
    paper_theorem1_ii_bounded_sequence_homogeneity_of_eventual_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (β : ℝ)
    (_hβ_pos : 0 < β)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledEventualSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (β / (β + 1)))
        (gammaLikelihoodProfile likelihood (β / (β + 1)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (β / (β + 1))) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Lemma D.2 to Theorem 1(ii), finite-sum assembly.

The analytic core of Lemma D.2 proves one `a^(-1/β)` asymptotic for each fixed
rank/index integral. This source-facing wrapper verifies the algebraic step
from those finitely many rank terms to the top-`k` bounded loss
`M k - h(a)`.
-/
theorem paper_lemmaD2_bounded_top_k_loss_asymptotic_of_rank_terms
    {β : ℝ} {k : ℕ}
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (C : BoundedLemmaD2FiniteSumCertificate β k term) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k term)
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale β a) :=
  boundedLemmaD2TopKLoss_asymptoticEquivalent term C

/--
Source Lemma D.2 to Theorem 1(ii), nested-display form of the finite-sum
assembly. This is the same result as
`paper_lemmaD2_bounded_top_k_loss_asymptotic_of_rank_terms`, with the index set
expanded as the paper's `i = 1, ..., k` and `j = 0, ..., i - 1` sum.
-/
theorem paper_lemmaD2_bounded_nested_top_k_loss_asymptotic_of_rank_terms
    {β : ℝ} {k : ℕ}
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (C : BoundedLemmaD2FiniteSumCertificate β k term) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => ∑ i : Fin k, ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a)
      (fun a =>
        (∑ i : Fin k, ∑ j : Fin (i.val + 1), C.coeff ⟨i, j⟩) *
          boundedTailScale β a) :=
  boundedLemmaD2NestedTopKLoss_asymptoticEquivalent term C

/--
Source Theorem 1(ii), equations (91)-(96) assembled. Given the reflection
identity from original upper order-statistic means to reflected Lemma D.2
terms, the finite top-`k` loss inherits the bounded `a^(-1/β)` asymptotic from
the fixed rank/index certificates.
-/
theorem paper_theorem1_ii_bounded_reflected_source_loss_asymptotic
    {β M : ℝ} {k : ℕ}
    (sourceMean : Fin k → ℕ → ℝ)
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a)
    (C : BoundedLemmaD2FiniteSumCertificate β k term) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale β a) :=
  boundedLemmaD2_reflected_source_loss_asymptoticEquivalent
    sourceMean term hsource C

/--
Source Lemma D.2, actual integral-term finite assembly. A proof that the
reflected CDF integral terms have the fixed-rank `a^(-1/β)` asymptotic implies
the finite double-sum loss asymptotic.
-/
theorem paper_lemmaD2_bounded_integral_top_k_loss_asymptotic
    {β : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2IntegralAsymptoticCertificate β k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale β a) :=
  boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent G C

/--
Source Lemma D.2, epsilon-sandwich consequence of the actual integral-term
asymptotic certificate. One eventual threshold works for every fixed `(i,j)`
index in the finite top-`k` proof.
-/
theorem paper_lemmaD2_bounded_integral_term_sandwich
    {β : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2IntegralAsymptoticCertificate β k G)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in Filter.atTop,
      ∀ p : BoundedLemmaD2Index k,
        (1 - ε) * (C.coeff p * boundedTailScale β a) ≤
            boundedLemmaD2IndexedIntegralTerm G p a ∧
          boundedLemmaD2IndexedIntegralTerm G p a ≤
            (1 + ε) * (C.coeff p * boundedTailScale β a) :=
  boundedLemmaD2IntegralAsymptoticCertificate_eventually_integral_sandwich
    C hε

/--
Source Lemma D.2, exponential kernel limit. This verifies the standard
`(1 - z/a)^a -> exp(-z)` step used after rescaling the bounded-tail CDF.
-/
theorem paper_lemmaD2_bounded_one_sub_div_pow_tendsto_exp (z : ℝ) :
    Filter.Tendsto
      (fun a : ℕ => (1 - z / (a : ℝ)) ^ a)
      Filter.atTop (nhds (Real.exp (-z))) :=
  bounded_one_sub_div_pow_tendsto_exp z

/--
Source Lemma D.2, fixed-rank exponential kernel limit. For fixed `j`, replacing
the exponent `a` by `a - j` leaves the `exp(-z)` limit unchanged.
-/
theorem paper_lemmaD2_bounded_one_sub_div_pow_sub_tendsto_exp
    (z : ℝ) (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ => (1 - z / (a : ℝ)) ^ (a - j))
      Filter.atTop (nhds (Real.exp (-z))) :=
  bounded_one_sub_div_pow_sub_tendsto_exp z j

/--
Source Lemma D.2, CDF rescaling step. A near-zero CDF power-law sandwich
applies after the substitution `x = y * a^(-1/β)` for every fixed `y > 0`.
-/
theorem paper_lemmaD2_bounded_rescaled_cdf_power_sandwich
    {G : ℝ → ℝ} {β c : ℝ}
    (C : BoundedTailCDFPowerSandwich G β c)
    {ε y : ℝ} (hε : 0 < ε) (hy_pos : 0 < y) :
    ∀ᶠ a in Filter.atTop,
      (1 - ε) * (c / β) * (y * boundedTailScale β a) ^ β ≤
          G (y * boundedTailScale β a) ∧
        G (y * boundedTailScale β a) ≤
          (1 + ε) * (c / β) * (y * boundedTailScale β a) ^ β :=
  C.eventually_rescaled_cdf_power_sandwich hε hy_pos

/--
Source Lemma D.2, simplified CDF rescaling step. The rescaled power term is
rewritten as `y^β * a^-1`.
-/
theorem paper_lemmaD2_bounded_rescaled_cdf_power_sandwich_inv_nat
    {G : ℝ → ℝ} {β c : ℝ}
    (C : BoundedTailCDFPowerSandwich G β c)
    {ε y : ℝ} (hε : 0 < ε) (hy_pos : 0 < y) :
    ∀ᶠ a : ℕ in Filter.atTop,
      (1 - ε) * (c / β) * (y ^ β * (a : ℝ) ^ (-1 : ℝ)) ≤
          G (y * boundedTailScale β a) ∧
        G (y * boundedTailScale β a) ≤
          (1 + ε) * (c / β) * (y ^ β * (a : ℝ) ^ (-1 : ℝ)) :=
  C.eventually_rescaled_cdf_power_sandwich_inv_nat hε hy_pos

/--
Source Lemma D.2, rescaled CDF sandwich after multiplying by `a`. This is the
constant sandwich around `(c / β) * y^β` used before the exponential kernel
limit.
-/
theorem paper_lemmaD2_bounded_rescaled_cdf_nat_mul_sandwich
    {G : ℝ → ℝ} {β c : ℝ}
    (C : BoundedTailCDFPowerSandwich G β c)
    {ε y : ℝ} (hε : 0 < ε) (hy_pos : 0 < y) :
    ∀ᶠ a : ℕ in Filter.atTop,
      (1 - ε) * ((c / β) * y ^ β) ≤
          (a : ℝ) * G (y * boundedTailScale β a) ∧
        (a : ℝ) * G (y * boundedTailScale β a) ≤
          (1 + ε) * ((c / β) * y ^ β) :=
  C.eventually_rescaled_cdf_nat_mul_sandwich hε hy_pos

/--
Source Lemma D.2, pointwise rescaled CDF limit:
`a * G(y * a^(-1/β)) -> (c / β) * y^β` for fixed `y > 0`.
-/
theorem paper_lemmaD2_bounded_rescaled_cdf_nat_mul_tendsto
    {G : ℝ → ℝ} {β c : ℝ}
    (C : BoundedTailCDFPowerSandwich G β c)
    {y : ℝ} (hy_pos : 0 < y) :
    Filter.Tendsto
      (fun a : ℕ => (a : ℝ) * G (y * boundedTailScale β a))
      Filter.atTop (nhds ((c / β) * y ^ β)) :=
  C.rescaled_cdf_nat_mul_tendsto hy_pos

/--
Source Lemma D.2, the rescaled split threshold
`delta / a^(-1/β)` tends to infinity.
-/
theorem paper_lemmaD2_bounded_tail_scale_delta_div_tendsto_atTop
    {β delta : ℝ} (hβ_pos : 0 < β) (hdelta_pos : 0 < delta) :
    Filter.Tendsto
      (fun a : ℕ => delta / boundedTailScale β a)
      Filter.atTop Filter.atTop :=
  boundedTailScale_delta_div_tendsto_atTop hβ_pos hdelta_pos

/--
Source Lemma D.2, local CDF power bounds after the substitution
`x = y*a^(-1/β)`.
-/
theorem paper_lemmaD2_bounded_rescaled_local_cdf_power_bounds
    {G : ℝ → ℝ} {β A B delta : ℝ}
    (hβ_pos : 0 < β)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ β ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ β) :
    ∀ᶠ a in Filter.atTop,
      ∀ {y : ℝ}, 0 < y →
        y < delta / boundedTailScale β a →
          A * (y ^ β * (a : ℝ) ^ (-1 : ℝ)) ≤
              G (y * boundedTailScale β a) ∧
            G (y * boundedTailScale β a) ≤
              B * (y ^ β * (a : ℝ) ^ (-1 : ℝ)) :=
  boundedLemmaD2_eventually_rescaled_local_cdf_power_bounds
    hβ_pos hG_lower hG_upper

/--
Source Lemma D.2, the asymptotic CDF sandwich supplies concrete local power
bounds on a right-neighborhood of zero.
-/
theorem paper_lemmaD2_bounded_exists_local_cdf_power_bounds
    {G : ℝ → ℝ} {β c : ℝ}
    (C : BoundedTailCDFPowerSandwich G β c) :
    ∃ delta A B : ℝ,
      0 < delta ∧ 0 < A ∧ 0 ≤ B ∧
        (∀ x : ℝ, 0 < x → x < delta → A * x ^ β ≤ G x) ∧
        (∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ β) :=
  C.exists_local_cdf_power_bounds

/--
Source Lemma D.2, scalar envelope bound for the fixed-rank binomial kernel
under rescaled local CDF power bounds.
-/
theorem paper_lemmaD2_bounded_binomial_kernel_norm_le_power_exp_of_rescaled_bounds
    {β A B y g : ℝ} {j a : ℕ}
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hy_pos : 0 < y) (ha_pos : 0 < a)
    (hlarge : 2 * j ≤ a)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1)
    (hg_lower : A * (y ^ β * (a : ℝ) ^ (-1 : ℝ)) ≤ g)
    (hg_upper : g ≤ B * (y ^ β * (a : ℝ) ^ (-1 : ℝ))) :
    ‖(Nat.choose a j : ℝ) * g ^ j * (1 - g) ^ (a - j)‖ ≤
      B ^ j * y ^ (β * (j : ℝ)) *
        Real.exp (-(A / 2) * y ^ β) :=
  boundedLemmaD2_binomial_kernel_norm_le_power_exp_of_rescaled_bounds
    hA_pos hB_nonneg hy_pos ha_pos hlarge
    hg_nonneg hg_le_one hg_lower hg_upper

/--
Source Lemma D.2, eventual gamma-shaped envelope for the rescaled kernel on
the growing near-zero window.
-/
theorem paper_lemmaD2_bounded_rescaled_kernel_eventually_norm_le_power_exp_on_growing
    {G : ℝ → ℝ} {β A B delta : ℝ} (j : ℕ)
    (hβ_pos : 0 < β)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ β ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ β) :
    ∀ᶠ a in Filter.atTop,
      ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        y < delta / boundedTailScale β a →
          ‖boundedLemmaD2RescaledKernel G β j a y‖ ≤
            B ^ j * y ^ (β * (j : ℝ)) *
              Real.exp (-(A / 2) * y ^ β) :=
  boundedLemmaD2RescaledKernel_eventually_norm_le_power_exp_on_growing
    j hβ_pos hA_pos hB_nonneg hG_nonneg hG_le_one hG_lower hG_upper

/--
Source Lemma D.2, rescaled exponential kernel limit with exponent `a`.
-/
theorem paper_lemmaD2_bounded_rescaled_cdf_one_sub_pow_tendsto_exp
    {G : ℝ → ℝ} {β c : ℝ}
    (C : BoundedTailCDFPowerSandwich G β c)
    {y : ℝ} (hy_pos : 0 < y) :
    Filter.Tendsto
      (fun a : ℕ =>
        (1 - G (y * boundedTailScale β a)) ^ a)
      Filter.atTop (nhds (Real.exp (-((c / β) * y ^ β)))) :=
  C.rescaled_cdf_one_sub_pow_tendsto_exp hy_pos

/--
Source Lemma D.2, fixed-rank rescaled exponential kernel limit with exponent
`a - j`.
-/
theorem paper_lemmaD2_bounded_rescaled_cdf_one_sub_pow_sub_tendsto_exp
    {G : ℝ → ℝ} {β c : ℝ}
    (C : BoundedTailCDFPowerSandwich G β c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ =>
        (1 - G (y * boundedTailScale β a)) ^ (a - j))
      Filter.atTop (nhds (Real.exp (-((c / β) * y ^ β)))) :=
  C.rescaled_cdf_one_sub_pow_sub_tendsto_exp hy_pos j

/--
Source Lemma D.2, pointwise binomial-kernel limit after the bounded-tail
substitution `x = y * a^(-1/β)`.
-/
theorem paper_lemmaD2_bounded_rescaled_cdf_binomial_kernel_tendsto
    {G : ℝ → ℝ} {β c : ℝ}
    (C : BoundedTailCDFPowerSandwich G β c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ =>
        (Nat.choose a j : ℝ) *
          (G (y * boundedTailScale β a)) ^ j *
          (1 - G (y * boundedTailScale β a)) ^ (a - j))
      Filter.atTop
      (nhds
        (Real.exp (-((c / β) * y ^ β)) *
          (((c / β) * y ^ β) ^ j) / j.factorial)) :=
  C.rescaled_cdf_binomial_kernel_tendsto hy_pos j

/--
Source Lemma D.2, pointwise convergence of the rescaled finite-`a` kernel to
the limiting gamma-kernel integrand.
-/
theorem paper_lemmaD2_bounded_rescaled_kernel_tendsto_limit
    {G : ℝ → ℝ} {β c : ℝ}
    (C : BoundedTailCDFPowerSandwich G β c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ => boundedLemmaD2RescaledKernel G β j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitKernel β c j y)) :=
  C.rescaled_kernel_tendsto_limit hy_pos j

/--
Source Lemma D.2, measurability of the rescaled finite-`a` kernel.
-/
theorem paper_lemmaD2_bounded_rescaled_kernel_aestronglyMeasurable
    {G : ℝ → ℝ} (hG : Measurable G) (β : ℝ) (j a : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => boundedLemmaD2RescaledKernel G β j a y)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  boundedLemmaD2RescaledKernel_aestronglyMeasurable hG β j a

/--
Source Lemma D.2, integrability of the gamma-shaped envelope
`x^q * exp(-b*x^p)` on `(0,∞)`.
-/
theorem paper_lemmaD2_bounded_gamma_envelope_integrableOn
    {p q b : ℝ} (hp : 0 < p) (hq : -1 < q) (hb : 0 < b) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ q * Real.exp (-b * x ^ p))
      (Set.Ioi (0 : ℝ)) :=
  integrableOn_rpow_mul_exp_neg_mul_rpow_of_pos hp hq hb

/-- Source Lemma D.2, measurability of the finite-`a` source integrand. -/
theorem paper_lemmaD2_bounded_integral_kernel_measurable
    {G : ℝ → ℝ} (hG : Measurable G) (j a : ℕ) :
    Measurable (fun x : ℝ => boundedLemmaD2IntegralKernel G j a x) :=
  boundedLemmaD2IntegralKernel_measurable hG j a

/--
Source Lemma D.2, CDF-range bound for the finite-`a` source integrand.
-/
theorem paper_lemmaD2_bounded_integral_kernel_norm_le_choose_of_cdf_range
    {G : ℝ → ℝ} (j a : ℕ) {x : ℝ}
    (hG_nonneg : 0 ≤ G x) (hG_le_one : G x ≤ 1) :
    ‖boundedLemmaD2IntegralKernel G j a x‖ ≤ (Nat.choose a j : ℝ) :=
  boundedLemmaD2IntegralKernel_norm_le_choose_of_cdf_range
    j a hG_nonneg hG_le_one

/--
Source Lemma D.2, bounded-support CDF conditions imply source-kernel
integrability once `a > j`.
-/
theorem paper_lemmaD2_bounded_integral_kernel_integrableOn_of_bounded_support
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    {j a : ℕ} (hja : j < a) :
    MeasureTheory.IntegrableOn
      (boundedLemmaD2IntegralKernel G j a)
      (Set.Ioi (0 : ℝ)) :=
  boundedLemmaD2IntegralKernel_integrableOn_of_bounded_support
    hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support hja

/--
Source Lemma D.2, eventual source-kernel integrability from bounded-support
CDF conditions.
-/
theorem paper_lemmaD2_bounded_integral_kernel_eventually_integrableOn_of_bounded_support
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (j : ℕ) :
    ∀ᶠ a in Filter.atTop,
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j a)
        (Set.Ioi (0 : ℝ)) :=
  boundedLemmaD2IntegralKernel_eventually_integrableOn_of_bounded_support
    hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support j

/--
Source Lemma D.2, bounded-support CDF conditions imply eventual integrability
for every finite-rank kernel in the fixed top-`k` source sum.
-/
theorem paper_lemmaD2_bounded_integral_kernel_eventually_fin_integrableOn_of_bounded_support
    {G : ℝ → ℝ} {k : ℕ} (hG_measurable : Measurable G)
    (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1) :
    ∀ᶠ a in Filter.atTop,
      ∀ i : Fin k, ∀ j ∈ Finset.Icc 0 i.val,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ)) := by
  filter_upwards [Filter.eventually_ge_atTop k] with a hka i j hj
  exact
    paper_lemmaD2_bounded_integral_kernel_integrableOn_of_bounded_support
      hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support
      (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2
        (lt_of_lt_of_le i.isLt hka))

/--
Source Lemma D.2, finite-support geometric bound for the above-`delta` tail
integral.
-/
theorem paper_lemmaD2_bounded_integral_term_above_le_geometric_support_bound
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    {delta M p : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdeltaM : delta ≤ M)
    (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    {j a : ℕ} (hja : j < a) :
    boundedLemmaD2IntegralTermAbove G j a delta ≤
      ((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) *
        (M - delta) :=
  boundedLemmaD2IntegralTermAbove_le_geometric_support_bound
    hG_measurable hdelta_nonneg hdeltaM hp_nonneg hp_le_one
    hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail hja

/--
Source Lemma D.2, the scalar binomial/geometric support bound is negligible
relative to the bounded-branch scale.
-/
theorem paper_lemmaD2_bounded_tail_scale_choose_geometric_tail_ratio_tendsto_zero
    {β p C : ℝ} (hβ_pos : 0 < β)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hC_nonneg : 0 ≤ C) (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ =>
        (((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) * C) /
          boundedTailScale β a)
      Filter.atTop (nhds 0) :=
  boundedTailScale_choose_geometric_tail_ratio_tendsto_zero
    hβ_pos hp_pos hp_lt_one hC_nonneg j

/--
Source Lemma D.2, finite-support geometric domination makes the above-`delta`
tail integral negligible relative to `a^(-1/β)`.
-/
theorem paper_lemmaD2_bounded_integral_term_above_negligible_of_geometric_support_bound
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    {β delta M p : ℝ} (hβ_pos : 0 < β)
    (hdelta_nonneg : 0 ≤ delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ =>
        boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale β a)
      Filter.atTop (nhds 0) :=
  boundedLemmaD2IntegralTermAbove_negligible_of_geometric_support_bound
    hG_measurable hβ_pos hdelta_nonneg hdeltaM hp_pos hp_lt_one
    hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail j

/--
Source Lemma D.2, change of variables `x = y*a^(-1/β)` for the exact source
integral term.
-/
theorem paper_lemmaD2_bounded_integral_term_changeOfVariables
    (G : ℝ → ℝ) (β : ℝ) (j a : ℕ)
    (hscale_pos : 0 < boundedTailScale β a) :
    boundedLemmaD2IntegralTerm G j a =
      boundedTailScale β a *
        ∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2RescaledKernel G β j a y :=
  boundedLemmaD2IntegralTerm_changeOfVariables G β j a hscale_pos

/--
Source Lemma D.2, near-zero change of variables `x = y*a^(-1/β)` for the
below-`delta` source integral term.
-/
theorem paper_lemmaD2_bounded_integral_term_below_changeOfVariables
    (G : ℝ → ℝ) (β : ℝ) (j a : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hscale_pos : 0 < boundedTailScale β a) :
    boundedLemmaD2IntegralTermBelow G j a delta =
      boundedTailScale β a *
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale β a),
          boundedLemmaD2RescaledKernel G β j a y :=
  boundedLemmaD2IntegralTermBelow_changeOfVariables
    G β j a hdelta_nonneg hscale_pos

/--
Source Lemma D.2, above-`delta` change of variables `x = y*a^(-1/β)` for
the source tail integral term.
-/
theorem paper_lemmaD2_bounded_integral_term_above_changeOfVariables
    (G : ℝ → ℝ) (β : ℝ) (j a : ℕ) {delta : ℝ}
    (hscale_pos : 0 < boundedTailScale β a) :
    boundedLemmaD2IntegralTermAbove G j a delta =
      boundedTailScale β a *
        ∫ y in Set.Ioi (delta / boundedTailScale β a),
          boundedLemmaD2RescaledKernel G β j a y :=
  boundedLemmaD2IntegralTermAbove_changeOfVariables
    G β j a hscale_pos

/--
Source Lemma D.2, eventual change of variables for the exact source integral
term.
-/
theorem paper_lemmaD2_bounded_integral_term_eventually_changeOfVariables
    (G : ℝ → ℝ) (β : ℝ) (j : ℕ) :
    ∀ᶠ a in Filter.atTop,
      boundedLemmaD2IntegralTerm G j a =
        boundedTailScale β a *
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G β j a y :=
  boundedLemmaD2IntegralTerm_eventually_changeOfVariables G β j

/--
Source Lemma D.2, eventual near-zero change of variables for the below-`delta`
source integral term.
-/
theorem paper_lemmaD2_bounded_integral_term_below_eventually_changeOfVariables
    (G : ℝ → ℝ) (β : ℝ) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta) :
    ∀ᶠ a in Filter.atTop,
      boundedLemmaD2IntegralTermBelow G j a delta =
        boundedTailScale β a *
          ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale β a),
            boundedLemmaD2RescaledKernel G β j a y :=
  boundedLemmaD2IntegralTermBelow_eventually_changeOfVariables
    G β j hdelta_nonneg

/--
Source Lemma D.2, eventual above-`delta` change of variables for the source
tail integral term.
-/
theorem paper_lemmaD2_bounded_integral_term_above_eventually_changeOfVariables
    (G : ℝ → ℝ) (β : ℝ) (j : ℕ) (delta : ℝ) :
    ∀ᶠ a in Filter.atTop,
      boundedLemmaD2IntegralTermAbove G j a delta =
        boundedTailScale β a *
          ∫ y in Set.Ioi (delta / boundedTailScale β a),
            boundedLemmaD2RescaledKernel G β j a y :=
  boundedLemmaD2IntegralTermAbove_eventually_changeOfVariables
    G β j delta

/--
Source Lemma D.2, exact split of the rescaled integral at the growing
threshold `delta / a^(-1/β)`.
-/
theorem paper_lemmaD2_bounded_rescaled_integral_split
    (G : ℝ → ℝ) (β : ℝ) (j a : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hscale_pos : 0 < boundedTailScale β a)
    (h_integrable :
      MeasureTheory.IntegrableOn
        (fun y : ℝ => boundedLemmaD2RescaledKernel G β j a y)
        (Set.Ioi (0 : ℝ))) :
    (∫ y in Set.Ioi (0 : ℝ),
        boundedLemmaD2RescaledKernel G β j a y) =
      (∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale β a),
        boundedLemmaD2RescaledKernel G β j a y) +
      (∫ y in Set.Ioi (delta / boundedTailScale β a),
        boundedLemmaD2RescaledKernel G β j a y) :=
  boundedLemmaD2RescaledIntegral_split
    G β j a hdelta_nonneg hscale_pos h_integrable

/--
Source Lemma D.2, eventual split of the rescaled integral at the growing
threshold `delta / a^(-1/β)`.
-/
theorem paper_lemmaD2_bounded_rescaled_integral_eventually_split
    (G : ℝ → ℝ) (β : ℝ) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.IntegrableOn
          (fun y : ℝ => boundedLemmaD2RescaledKernel G β j a y)
          (Set.Ioi (0 : ℝ))) :
    ∀ᶠ a in Filter.atTop,
      (∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2RescaledKernel G β j a y) =
        (∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale β a),
          boundedLemmaD2RescaledKernel G β j a y) +
        (∫ y in Set.Ioi (delta / boundedTailScale β a),
          boundedLemmaD2RescaledKernel G β j a y) :=
  boundedLemmaD2RescaledIntegral_eventually_split
    G β j hdelta_nonneg h_integrable

/--
Source Lemma D.2, growing near-zero rescaled-integral convergence directly
from local CDF power bounds near zero.
-/
theorem paper_lemmaD2_bounded_growing_rescaled_integral_tendsto_of_local_cdf_power_bounds
    {G : ℝ → ℝ} {β c A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G β c)
    (hG_measurable : Measurable G)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ β ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ β)
    (j : ℕ) :
    Filter.Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale β a),
          boundedLemmaD2RescaledKernel G β j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitCoeff β c j)) :=
  boundedLemmaD2GrowingRescaledIntegral_tendsto_of_local_cdf_power_bounds
    tail hG_measurable hdelta_pos hA_pos hB_nonneg
    hG_nonneg hG_le_one hG_lower hG_upper j

/--
Source Lemma D.2, growing near-zero rescaled-integral convergence from full
rescaled convergence and rescaled-tail convergence to zero.
-/
theorem paper_lemmaD2_bounded_growing_rescaled_integral_tendsto_of_full_and_tail
    {G : ℝ → ℝ} {β c : ℝ} (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.IntegrableOn
          (fun y : ℝ => boundedLemmaD2RescaledKernel G β j a y)
          (Set.Ioi (0 : ℝ)))
    (hfull :
      Filter.Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G β j a y)
        Filter.atTop (nhds (boundedLemmaD2LimitCoeff β c j)))
    (htail :
      Filter.Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (delta / boundedTailScale β a),
            boundedLemmaD2RescaledKernel G β j a y)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale β a),
          boundedLemmaD2RescaledKernel G β j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitCoeff β c j)) :=
  boundedLemmaD2GrowingRescaledIntegral_tendsto_of_full_and_tail
    j hdelta_nonneg h_integrable hfull htail

/--
Source Lemma D.2, growing near-zero rescaled-integral convergence from full
rescaled convergence and source-tail negligibility.
-/
theorem paper_lemmaD2_bounded_growing_rescaled_integral_tendsto_of_full_and_source_tail
    {G : ℝ → ℝ} {β c : ℝ} (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.IntegrableOn
          (fun y : ℝ => boundedLemmaD2RescaledKernel G β j a y)
          (Set.Ioi (0 : ℝ)))
    (hfull :
      Filter.Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G β j a y)
        Filter.atTop (nhds (boundedLemmaD2LimitCoeff β c j)))
    (htail_source :
      Filter.Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j a delta /
            boundedTailScale β a)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale β a),
          boundedLemmaD2RescaledKernel G β j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitCoeff β c j)) :=
  boundedLemmaD2GrowingRescaledIntegral_tendsto_of_full_and_source_tail
    j hdelta_nonneg h_integrable hfull htail_source

/--
Source Lemma D.2, below-`delta` asymptotic from convergence of the growing
rescaled near-zero integral.
-/
theorem paper_lemmaD2_bounded_integral_term_below_asymptotic_of_growing_rescaled_integral
    {G : ℝ → ℝ} {β c : ℝ} (hβ_pos : 0 < β)
    (hc_pos : 0 < c) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hgrowing :
      Filter.Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale β a),
            boundedLemmaD2RescaledKernel G β j a y)
        Filter.atTop (nhds (boundedLemmaD2LimitCoeff β c j))) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff β c j *
        boundedTailScale β a) :=
  boundedLemmaD2IntegralTermBelow_asymptotic_of_growing_rescaled_integral
    hβ_pos hc_pos j hdelta_nonneg hgrowing

/--
Source Lemma D.2, below-`delta` source asymptotic directly from local CDF
power bounds near zero.
-/
theorem paper_lemmaD2_bounded_integral_term_below_asymptotic_of_local_cdf_power_bounds
    {G : ℝ → ℝ} {β c A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G β c)
    (hG_measurable : Measurable G)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ β ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ β)
    (j : ℕ) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff β c j *
        boundedTailScale β a) :=
  boundedLemmaD2IntegralTermBelow_asymptotic_of_local_cdf_power_bounds
    tail hG_measurable hdelta_pos hA_pos hB_nonneg
    hG_nonneg hG_le_one hG_lower hG_upper j

/--
Source Lemma D.2, exact near-zero/tail split of the source integral term at
`delta`.
-/
theorem paper_lemmaD2_bounded_integral_term_split
    (G : ℝ → ℝ) (j a : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j a)
        (Set.Ioi (0 : ℝ))) :
    boundedLemmaD2IntegralTerm G j a =
      boundedLemmaD2IntegralTermBelow G j a delta +
        boundedLemmaD2IntegralTermAbove G j a delta :=
  boundedLemmaD2IntegralTerm_split G j a hdelta_nonneg h_integrable

/--
Source Lemma D.2, eventual near-zero/tail split from eventual source-kernel
integrability.
-/
theorem paper_lemmaD2_bounded_integral_term_eventually_split
    (G : ℝ → ℝ) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ))) :
    ∀ᶠ a in Filter.atTop,
      boundedLemmaD2IntegralTerm G j a =
        boundedLemmaD2IntegralTermBelow G j a delta +
          boundedLemmaD2IntegralTermAbove G j a delta :=
  boundedLemmaD2IntegralTerm_eventually_split
    G j hdelta_nonneg h_integrable

/--
Source Lemma D.2, gamma-integral value of the fixed-`j` limiting coefficient.
-/
theorem paper_lemmaD2_bounded_limit_coeff_eq_gamma
    {β c : ℝ} (hβ_pos : 0 < β) (hc_pos : 0 < c)
    (j : ℕ) :
    boundedLemmaD2LimitCoeff β c j =
      ((c / β) ^ j / (j.factorial : ℝ)) *
        ((c / β) ^ (-(β * (j : ℝ) + 1) / β) *
          (1 / β) *
          Real.Gamma ((β * (j : ℝ) + 1) / β)) :=
  boundedLemmaD2LimitCoeff_eq_gamma hβ_pos hc_pos j

/--
Source Lemma D.2, positivity of the fixed-`j` limiting coefficient.
-/
theorem paper_lemmaD2_bounded_limit_coeff_pos
    {β c : ℝ} (hβ_pos : 0 < β) (hc_pos : 0 < c)
    (j : ℕ) :
    0 < boundedLemmaD2LimitCoeff β c j :=
  boundedLemmaD2LimitCoeff_pos hβ_pos hc_pos j

/--
Source Theorem 1(ii), equations (91)-(96) with the actual Lemma D.2 integral
term. This is the bounded branch's main remaining analytic interface.
-/
theorem paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic
    {β M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2IntegralAsymptoticCertificate β k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale β a) :=
  boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent
    G sourceMean hsource C

/--
Source Lemma D.2, actual integral finite assembly with the exact gamma
limiting coefficients.
-/
theorem paper_lemmaD2_bounded_integral_top_k_loss_asymptotic_of_limit_coeff
    {β c : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2LimitIntegralAsymptoticCertificate β c k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c p.2.val) *
          boundedTailScale β a) :=
  boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent_of_limit_coeff_certificate
    G C

/--
Source Theorem 1(ii), equations (91)-(96) with the exact gamma limiting
coefficients supplied by the sharper Lemma D.2 certificate.
-/
theorem
    paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_limit_coeff
    {β c M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2LimitIntegralAsymptoticCertificate β c k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c p.2.val) *
          boundedTailScale β a) :=
  boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent_of_limit_coeff_certificate
    G sourceMean hsource C

/--
Source Lemma D.2, per-rank dominated-convergence certificate constructor from
measurability and an integrable envelope.
-/
noncomputable def paper_lemmaD2_bounded_dominated_kernel_certificate_of_measurable_bound
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (tail : BoundedTailCDFPowerSandwich G β c)
    (hG : Measurable G)
    (bound : ℝ → ℝ)
    (bound_integrable :
      MeasureTheory.Integrable bound
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (kernel_bound :
      ∀ᶠ a in Filter.atTop,
        ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
          ‖boundedLemmaD2RescaledKernel G β j a y‖ ≤ bound y) :
    BoundedLemmaD2DominatedKernelCertificate β c G j :=
  BoundedLemmaD2DominatedKernelCertificate.ofMeasurableBound
    tail hG bound bound_integrable kernel_bound

/--
Source Lemma D.2, finite-index dominated-convergence certificate constructor
from measurability and integrable envelopes.
-/
noncomputable def paper_lemmaD2_bounded_dominated_integral_certificate_of_measurable_bound
    {β c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hG : Measurable G)
    (bound : BoundedLemmaD2Index k → ℝ → ℝ)
    (bound_integrable :
      ∀ p : BoundedLemmaD2Index k,
        MeasureTheory.Integrable (bound p)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (kernel_bound :
      ∀ p : BoundedLemmaD2Index k,
        ∀ᶠ a in Filter.atTop,
          ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
            ‖boundedLemmaD2RescaledKernel G β p.2.val a y‖ ≤ bound p y) :
    BoundedLemmaD2DominatedIntegralAsymptoticCertificate β c k G :=
  BoundedLemmaD2DominatedIntegralAsymptoticCertificate.ofMeasurableBound
    tail k_pos hG bound bound_integrable kernel_bound

/--
Source Lemma D.2, dominated convergence for the rescaled finite-`a` kernels.
-/
theorem paper_lemmaD2_bounded_rescaled_integral_tendsto_of_dominated_certificate
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate β c G j) :
    Filter.Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2RescaledKernel G β j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitCoeff β c j)) :=
  C.rescaled_integral_tendsto

/--
Source Lemma D.2, the dominated-convergence certificate supplies eventual
integrability of the rescaled kernels on `(0,∞)`.
-/
theorem paper_lemmaD2_bounded_rescaled_kernel_eventually_integrableOn_of_dominated_certificate
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate β c G j) :
    ∀ᶠ a in Filter.atTop,
      MeasureTheory.IntegrableOn
        (fun y : ℝ => boundedLemmaD2RescaledKernel G β j a y)
        (Set.Ioi (0 : ℝ)) :=
  C.eventually_rescaledKernel_integrableOn

/--
Source Lemma D.2, dominated convergence gives the growing near-zero rescaled
integral convergence directly by truncating the rescaled kernels on the
expanding interval.
-/
theorem paper_lemmaD2_bounded_growing_rescaled_integral_tendsto_of_dominated_certificate
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate β c G j)
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    Filter.Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale β a),
          boundedLemmaD2RescaledKernel G β j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitCoeff β c j)) :=
  C.growing_rescaled_integral_tendsto hdelta_pos

/--
Source Lemma D.2, dominated convergence gives the below-`delta` source
asymptotic through the paper's growing-rescaled-integral route.
-/
theorem paper_lemmaD2_bounded_integral_term_below_asymptotic_of_dominated_certificate
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate β c G j)
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff β c j * boundedTailScale β a) :=
  C.integralTermBelow_asymptoticEquivalent hdelta_pos

/--
Source Lemma D.2, dominated convergence plus source-tail negligibility gives
the growing near-zero rescaled integral convergence.
-/
theorem paper_lemmaD2_bounded_growing_rescaled_integral_tendsto_of_dominated_certificate_and_source_tail
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate β c G j)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (htail_source :
      Filter.Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j a delta /
            boundedTailScale β a)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale β a),
          boundedLemmaD2RescaledKernel G β j a y)
      Filter.atTop (nhds (boundedLemmaD2LimitCoeff β c j)) :=
  C.growing_rescaled_integral_tendsto_of_source_tail
    hdelta_nonneg htail_source

/--
Source Lemma D.2, dominated convergence plus source-tail negligibility gives
the below-`delta` source asymptotic via the growing-rescaled-integral route.
-/
theorem paper_lemmaD2_bounded_integral_term_below_asymptotic_of_dominated_certificate_and_source_tail
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate β c G j)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (htail_source :
      Filter.Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j a delta /
            boundedTailScale β a)
        Filter.atTop (nhds 0)) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff β c j * boundedTailScale β a) :=
  C.integralTermBelow_asymptoticEquivalent_of_source_tail
    hdelta_nonneg htail_source

/--
Source Lemma D.2, per-rank integral asymptotic from the explicit
change-of-variables and dominated-convergence certificate.
-/
theorem paper_lemmaD2_bounded_integral_term_asymptotic_of_dominated_certificate
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate β c G j) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2IntegralTerm G j)
      (fun a => boundedLemmaD2LimitCoeff β c j * boundedTailScale β a) :=
  C.integralTerm_asymptoticEquivalent

/--
Source Lemma D.2, conversion from the finite-index dominated-convergence
certificate to the exact-gamma integral asymptotic certificate.
-/
noncomputable def paper_lemmaD2_bounded_limit_integral_certificate_of_dominated
    {β c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate β c k G) :
    BoundedLemmaD2LimitIntegralAsymptoticCertificate β c k G :=
  C.toLimitIntegralAsymptoticCertificate

/--
Source Lemma D.2, finite-index dominated-convergence certificate plus common
bounded-support geometric tail control gives the paper-style split finite
certificate through the growing near-zero rescaled interval.
-/
noncomputable def paper_lemmaD2_bounded_split_finite_certificate_of_dominated_integral_and_geometric_tail_via_growing
    {β c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate β c k G)
    {delta M p : ℝ}
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralFiniteCertificate β c k G :=
  C.toSplitIntegralFiniteCertificateOfGeometricTailViaGrowing
    hdelta_pos hdeltaM hp_pos hp_lt_one hG_measurable
    hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail

/--
Source Lemma D.2, finite-index paper-style split certificate directly from
the bounded-tail limit, local CDF power bounds, and bounded-support geometric
tail control.
-/
noncomputable def paper_lemmaD2_bounded_split_finite_certificate_of_local_cdf_power_bounds_and_geometric_tail
    {β c : ℝ} {k : ℕ} {G : ℝ → ℝ} {delta M p A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ β ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ β)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralFiniteCertificate β c k G :=
  BoundedLemmaD2SplitIntegralFiniteCertificate.ofLocalCDFPowerBoundsAndGeometricTail
    tail k_pos hdelta_pos hdeltaM hA_pos hB_nonneg hp_pos hp_lt_one
    hG_measurable hG_nonneg hG_le_one hG_lower hG_upper
    hG_eq_one_of_support hp_le_G_on_tail

/--
Source Lemma D.2, finite-index paper-style split certificate from the
bounded-tail CDF asymptotic, monotonicity of the reflected CDF, and bounded
support.
-/
noncomputable def paper_lemmaD2_bounded_split_finite_certificate_of_cdf_power_sandwich_monotone_bounded_support
    {β c : ℝ} {k : ℕ} {G : ℝ → ℝ} {M : ℝ}
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hM_pos : 0 < M)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1) :
    BoundedLemmaD2SplitIntegralFiniteCertificate β c k G :=
  BoundedLemmaD2SplitIntegralFiniteCertificate.ofCDFPowerSandwichMonotoneBoundedSupport
    tail k_pos hM_pos hG_measurable hG_mono hG_nonneg hG_le_one
    hG_eq_one_of_support

/--
Source Lemma D.2, actual integral finite assembly from the explicit
dominated-convergence and change-of-variables certificate.
-/
theorem paper_lemmaD2_bounded_integral_top_k_loss_asymptotic_of_dominated_certificate
    {β c : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate β c k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c p.2.val) *
          boundedTailScale β a) :=
  boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent_of_dominated_certificate
    G C

/--
Source Theorem 1(ii), equations (91)-(96) from the explicit
dominated-convergence and change-of-variables certificate.
-/
theorem
    paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_dominated_certificate
    {β c M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate β c k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c p.2.val) *
          boundedTailScale β a) :=
  boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent_of_dominated_certificate
    G sourceMean hsource C

/--
Source Lemma D.2, paper-style split certificate constructor from eventual
source-kernel integrability plus the near-zero and tail estimates.
-/
noncomputable def paper_lemmaD2_bounded_split_certificate_of_asymptotics
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta : ℝ}
    (hβ_pos : 0 < β) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta)
    (h_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ)))
    (below_asymptotic :
      EconCSLib.Math.AsymptoticEquivalent
        (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
        (fun a => boundedLemmaD2LimitCoeff β c j *
          boundedTailScale β a))
    (above_negligible :
      Filter.Tendsto
        (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale β a)
        Filter.atTop (nhds 0)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate β c G j :=
  BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofAsymptotics
    hβ_pos hc_pos hdelta_pos h_integrable
    below_asymptotic above_negligible

/--
Source Lemma D.2, paper-style split certificate constructor from the full
integral asymptotic plus tail negligibility.
-/
noncomputable def paper_lemmaD2_bounded_split_certificate_of_full_asymptotic_and_tail
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta : ℝ}
    (hβ_pos : 0 < β) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta)
    (h_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ)))
    (full_asymptotic :
      EconCSLib.Math.AsymptoticEquivalent
        (boundedLemmaD2IntegralTerm G j)
        (fun a => boundedLemmaD2LimitCoeff β c j *
          boundedTailScale β a))
    (above_negligible :
      Filter.Tendsto
        (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale β a)
        Filter.atTop (nhds 0)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate β c G j :=
  BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofFullAsymptoticAndTail
    hβ_pos hc_pos hdelta_pos h_integrable
    full_asymptotic above_negligible

/--
Source Lemma D.2, paper-style split certificate constructor from bounded
support plus the near-zero and tail estimates.
-/
noncomputable def paper_lemmaD2_bounded_split_certificate_of_bounded_support_asymptotics
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta : ℝ}
    (hβ_pos : 0 < β) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta)
    (hG_measurable : Measurable G) (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (below_asymptotic :
      EconCSLib.Math.AsymptoticEquivalent
        (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
        (fun a => boundedLemmaD2LimitCoeff β c j *
          boundedTailScale β a))
    (above_negligible :
      Filter.Tendsto
        (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale β a)
        Filter.atTop (nhds 0)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate β c G j :=
  BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofBoundedSupportAsymptotics
    hβ_pos hc_pos hdelta_pos hG_measurable M
    hG_nonneg hG_le_one hG_eq_one_of_support
    below_asymptotic above_negligible

/--
Source Lemma D.2, paper-style split certificate constructor from bounded
support, a positive CDF floor on the above-`delta` tail, and the near-zero
asymptotic.
-/
noncomputable def paper_lemmaD2_bounded_split_certificate_of_bounded_support_near_zero_asymptotic
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p : ℝ}
    (hβ_pos : 0 < β) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    (below_asymptotic :
      EconCSLib.Math.AsymptoticEquivalent
        (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
        (fun a => boundedLemmaD2LimitCoeff β c j *
          boundedTailScale β a)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate β c G j :=
  BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofBoundedSupportNearZeroAsymptotic
    hβ_pos hc_pos hdelta_pos hdeltaM hp_pos hp_lt_one hG_measurable
    hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail
    below_asymptotic

/--
Source Lemma D.2, per-rank paper-style split certificate directly from the
bounded-tail limit, local CDF power bounds, and bounded-support geometric tail
control.
-/
noncomputable def paper_lemmaD2_bounded_split_certificate_of_local_cdf_power_bounds_and_geometric_tail
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G β c)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ β ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ β)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate β c G j :=
  BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofLocalCDFPowerBoundsAndGeometricTail
    tail hdelta_pos hdeltaM hA_pos hB_nonneg hp_pos hp_lt_one
    hG_measurable hG_nonneg hG_le_one hG_lower hG_upper
    hG_eq_one_of_support hp_le_G_on_tail

/--
Source Lemma D.2, per-rank paper-style split certificate from the bounded-tail
CDF asymptotic, monotonicity of the reflected CDF, and bounded support.
-/
noncomputable def paper_lemmaD2_bounded_split_certificate_of_cdf_power_sandwich_monotone_bounded_support
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ} {M : ℝ}
    (tail : BoundedTailCDFPowerSandwich G β c)
    (hM_pos : 0 < M)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate β c G j :=
  BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofCDFPowerSandwichMonotoneBoundedSupport
    tail hM_pos hG_measurable hG_mono hG_nonneg hG_le_one
    hG_eq_one_of_support

/--
Source Lemma D.2, convert a dominated-convergence full-integral certificate
plus bounded-support geometric tail control into the paper-style split
certificate.
-/
noncomputable def paper_lemmaD2_bounded_split_certificate_of_dominated_kernel_and_geometric_tail
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p : ℝ}
    (D : BoundedLemmaD2DominatedKernelCertificate β c G j)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate β c G j :=
  BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofDominatedKernelAndGeometricTail
    D hdelta_pos hdeltaM hp_pos hp_lt_one hG_measurable
    hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail

/--
Source Lemma D.2, convert a dominated-convergence full-integral certificate
plus bounded-support geometric tail control into the paper-style split
certificate through the growing near-zero rescaled interval.
-/
noncomputable def paper_lemmaD2_bounded_split_certificate_of_dominated_kernel_and_geometric_tail_via_growing
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p : ℝ}
    (D : BoundedLemmaD2DominatedKernelCertificate β c G j)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate β c G j :=
  BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofDominatedKernelAndGeometricTailViaGrowing
    D hdelta_pos hdeltaM hp_pos hp_lt_one hG_measurable
    hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail

/--
Source Lemma D.2, per-rank integral asymptotic from the paper-style
near-zero/tail split certificate.
-/
theorem paper_lemmaD2_bounded_integral_term_asymptotic_of_split_certificate
    {β c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2SplitIntegralAsymptoticCertificate β c G j) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2IntegralTerm G j)
      (fun a => boundedLemmaD2LimitCoeff β c j * boundedTailScale β a) :=
  C.integralTerm_asymptoticEquivalent

/--
Source Lemma D.2, conversion from the paper-style split certificate to the
exact-gamma integral asymptotic certificate.
-/
noncomputable def paper_lemmaD2_bounded_limit_integral_certificate_of_split
    {β c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2SplitIntegralFiniteCertificate β c k G) :
    BoundedLemmaD2LimitIntegralAsymptoticCertificate β c k G :=
  C.toLimitIntegralAsymptoticCertificate

/--
Source Lemma D.2, actual integral finite assembly from the paper-style
near-zero/tail split certificate.
-/
theorem paper_lemmaD2_bounded_integral_top_k_loss_asymptotic_of_split_certificate
    {β c : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2SplitIntegralFiniteCertificate β c k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c p.2.val) *
          boundedTailScale β a) :=
  boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent_of_split_certificate
    G C

/--
Source Theorem 1(ii), equations (91)-(96) from the paper-style
near-zero/tail split certificate.
-/
theorem
    paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_split_certificate
    {β c M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2SplitIntegralFiniteCertificate β c k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c p.2.val) *
          boundedTailScale β a) :=
  boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent_of_split_certificate
    G sourceMean hsource C

/--
Source Theorem 1(ii), equations (91)-(96) from bounded-tail asymptotics,
local CDF power bounds, and bounded-support geometric tail control.
-/
theorem
    paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_local_cdf_power_bounds_and_geometric_tail
    {β c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {delta M₀ p A B : ℝ}
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M₀)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ β ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ β)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) :=
  paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_split_certificate
    G sourceMean hsource
    (paper_lemmaD2_bounded_split_finite_certificate_of_local_cdf_power_bounds_and_geometric_tail
      tail k_pos hdelta_pos hdeltaM hA_pos hB_nonneg hp_pos hp_lt_one
      hG_measurable hG_nonneg hG_le_one hG_lower hG_upper
      hG_eq_one_of_support hp_le_G_on_tail)

/--
Source Theorem 1(ii), equations (91)-(96) from the bounded-tail CDF
asymptotic, monotonicity of the reflected CDF, and bounded support.
-/
theorem
    paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    {β c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) :=
  paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_split_certificate
    G sourceMean hsource
    (paper_lemmaD2_bounded_split_finite_certificate_of_cdf_power_sandwich_monotone_bounded_support
      tail k_pos hM₀_pos hG_measurable hG_mono hG_nonneg hG_le_one
      hG_eq_one_of_support)

/--
Source Lemma 1, bounded-support top-`k` loss asymptotic, stated through the
reflected-CDF integral representation used in equations (91)-(96).
-/
theorem
    paper_lemma1_bounded_support_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    {β c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) :=
  paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    sourceMean hsource tail k_pos hM₀_pos hG_measurable hG_mono
    hG_nonneg hG_le_one hG_eq_one_of_support

/--
Source Lemma 1, bounded-support top-`k` loss asymptotic, stated directly in
Definition 3's bottom-indexed `μ_D(i,a)` interface.  The only extra work over
the reflected-CDF integral endpoint is the finite-prefix bridge from
`min k a` to the fixed `Fin k` sum.
-/
theorem
    paper_lemma1_bounded_support_order_statistic_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    {β c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (μ : ℕ → ℕ → ℝ)
    (hμ :
      ∀ a (i : Fin k),
        μ (a - i.val) a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - orderStatisticTopKSumFromMean μ k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) := by
  let sourceMean : Fin k → ℕ → ℝ := fun i a => μ (a - i.val) a
  have hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a := by
    intro a i
    exact hμ a i
  have hbase :=
    paper_lemma1_bounded_support_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
      sourceMean hsource tail k_pos hM₀_pos hG_measurable hG_mono
      hG_nonneg hG_le_one hG_eq_one_of_support
  refine EconCSLib.Math.AsymptoticEquivalent.congr_left_eventually ?_ hbase
  filter_upwards
    [paper_definition3_order_statistic_topk_loss_eventually_eq_fin_loss
      M μ k] with a ha
  simpa [sourceMean] using ha

/--
Source Lemma 1, bounded-support top-`k` loss asymptotic, stated for expected
order-statistic means induced by a family of finite real-sample laws.  The
remaining source obligation is the distribution-specific reflected-CDF
identity for those expected order statistics.
-/
theorem
    paper_lemma1_bounded_support_expected_order_statistic_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    {β c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (hsource :
      ∀ a (i : Fin k),
        expectedOrderStatisticMeanSeq sampleMeasure (a - i.val) a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) :=
  paper_lemma1_bounded_support_order_statistic_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    (expectedOrderStatisticMeanSeq sampleMeasure) hsource tail k_pos
    hM₀_pos hG_measurable hG_mono hG_nonneg hG_le_one
    hG_eq_one_of_support

/--
Source Lemma 1, bounded-support top-`k` loss asymptotic from the aggregate
measure-level reflected-bottom identity.  This is the natural probability
boundary for concrete iid bounded-support models: after integrability, the
sample-law proof only has to identify the single reflected-bottom expectation
with the Lemma D.2 nested integral sum.
-/
theorem
    paper_lemma1_bounded_support_expected_reflected_bottom_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    {β c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (hprob : ∀ a, MeasureTheory.IsProbabilityMeasure (sampleMeasure a))
    (h_order_integrable :
      ∀ᶠ a in Filter.atTop,
        ∀ i ∈ Finset.range (min k a),
          MeasureTheory.Integrable
            (fun sample => sampleOrderStatisticValue sample (a - i))
            (sampleMeasure a))
    (h_top_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.Integrable
          (fun sample => EconCSLib.Probability.sampleTopKSum sample k)
          (sampleMeasure a))
    (h_reflected :
      ∀ᶠ a in Filter.atTop,
        EconCSLib.Probability.expectedReflectedBottomKSum
            M (sampleMeasure a) k =
          ∑ i : Fin k, ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) := by
  let sourceMean : Fin k → ℕ → ℝ :=
    fun i a => M - ∑ j : Fin (i.val + 1),
      boundedLemmaD2IntegralTerm G j.val a
  have hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a := by
    intro a i
    rfl
  have hbase :=
    paper_lemma1_bounded_support_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
      sourceMean hsource tail k_pos hM₀_pos hG_measurable hG_mono
      hG_nonneg hG_le_one hG_eq_one_of_support
  refine EconCSLib.Math.AsymptoticEquivalent.congr_left_eventually ?_ hbase
  filter_upwards
    [Filter.eventually_ge_atTop k, h_order_integrable, h_top_integrable,
      h_reflected] with a hka horder htop href
  letI : MeasureTheory.IsProbabilityMeasure (sampleMeasure a) := hprob a
  have hbridge :=
    expectedOrderStatisticMeanSeq_topKEndpointLoss_eq_expectedReflectedBottomKSum
      M sampleMeasure (a := a) k horder htop
  have hmin : min k a = k := min_eq_left hka
  have hmin_real : min (k : ℝ) (a : ℝ) = (k : ℝ) := by
    exact min_eq_left (by exact_mod_cast hka)
  have htarget :
      (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k a =
        EconCSLib.Probability.expectedReflectedBottomKSum
          M (sampleMeasure a) k := by
    simpa [hmin, hmin_real] using hbridge
  calc
    (k : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k a
        =
      EconCSLib.Probability.expectedReflectedBottomKSum
        M (sampleMeasure a) k := htarget
    _ = ∑ i : Fin k, ∑ j : Fin (i.val + 1),
          boundedLemmaD2IntegralTerm G j.val a := href
    _ = (k : ℝ) * M - ∑ i : Fin k, sourceMean i a := by
          simp [sourceMean, Finset.sum_sub_distrib, Finset.sum_const,
            Fintype.card_fin]

/--
Bounded-support version of the aggregate reflected-bottom Lemma 1 wrapper.
Coordinatewise a.e. support in `[L, M]` discharges the order-statistic and
top-`k` integrability hypotheses; the only remaining distribution-specific
probability step is the reflected-CDF identity for
`expectedReflectedBottomKSum`.
-/
theorem
    paper_lemma1_bounded_support_expected_reflected_bottom_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    {β c M L : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (hprob : ∀ a, MeasureTheory.IsProbabilityMeasure (sampleMeasure a))
    (h_bounds :
      ∀ᶠ a in Filter.atTop,
        ∀ᵐ sample ∂sampleMeasure a, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M)
    (h_reflected :
      ∀ᶠ a in Filter.atTop,
        EconCSLib.Probability.expectedReflectedBottomKSum
            M (sampleMeasure a) k =
          ∑ i : Fin k, ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) := by
  have h_order_integrable :
      ∀ᶠ a in Filter.atTop,
        ∀ i ∈ Finset.range (min k a),
          MeasureTheory.Integrable
            (fun sample => sampleOrderStatisticValue sample (a - i))
            (sampleMeasure a) := by
    filter_upwards [h_bounds] with a hbounds
    letI : MeasureTheory.IsProbabilityMeasure (sampleMeasure a) := hprob a
    exact
      paper_definition3_sample_order_statistic_topk_range_integrable_of_ae_bounds
        L M (sampleMeasure a) k hbounds
  have h_top_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.Integrable
          (fun sample => EconCSLib.Probability.sampleTopKSum sample k)
          (sampleMeasure a) := by
    filter_upwards [h_bounds] with a hbounds
    letI : MeasureTheory.IsProbabilityMeasure (sampleMeasure a) := hprob a
    exact
      paper_definition3_sample_topk_sum_integrable_of_ae_bounds
        L M (sampleMeasure a) k hbounds
  exact
    paper_lemma1_bounded_support_expected_reflected_bottom_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
      sampleMeasure hprob h_order_integrable h_top_integrable h_reflected
      tail k_pos hM₀_pos hG_measurable hG_mono hG_nonneg hG_le_one
      hG_eq_one_of_support

/--
Bounded-support Lemma 1 wrapper from the threshold-count layer-cake integral.
Coordinatewise support gives the order-statistic and count-layer Fubini
integrability; the remaining probability work is the integral formula for the
reflected rank-count layer, which is the direct target for iid binomial-count
calculations.
-/
theorem
    paper_lemma1_bounded_support_expected_reflected_count_layer_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    {β c M L : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (hprob : ∀ a, MeasureTheory.IsProbabilityMeasure (sampleMeasure a))
    (h_bounds :
      ∀ᶠ a in Filter.atTop,
        ∀ᵐ sample ∂sampleMeasure a, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M)
    (h_layer_integral :
      ∀ᶠ a in Filter.atTop,
        (∫ x in Set.Ioi (0 : ℝ),
          ∫ sample,
            EconCSLib.Probability.reflectedBottomKRankCountLayer
              M k sample x ∂(sampleMeasure a)) =
          ∑ i : Fin k, ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) := by
  have h_reflected :
      ∀ᶠ a in Filter.atTop,
        EconCSLib.Probability.expectedReflectedBottomKSum
            M (sampleMeasure a) k =
          ∑ i : Fin k, ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a := by
    filter_upwards
      [h_bounds, h_layer_integral] with a hbounds hlayer_formula
    letI : MeasureTheory.IsProbabilityMeasure (sampleMeasure a) := hprob a
    have hlayer_int :
        MeasureTheory.Integrable
          (fun z : (Fin a → ℝ) × ℝ =>
            EconCSLib.Probability.reflectedBottomKRankCountLayer M k z.1 z.2)
          ((sampleMeasure a).prod
            (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :=
      EconCSLib.Probability.reflectedBottomKRankCountLayer_integrable_prod_of_ae_bounds
        M L (sampleMeasure a) k hbounds
    have hupper :
        ∀ᵐ sample ∂sampleMeasure a, ∀ i : Fin a, sample i ≤ M := by
      filter_upwards [hbounds] with sample hsample i
      exact (hsample i).2
    calc
      EconCSLib.Probability.expectedReflectedBottomKSum
          M (sampleMeasure a) k =
        ∫ x in Set.Ioi (0 : ℝ),
          ∫ sample,
            EconCSLib.Probability.reflectedBottomKRankCountLayer
              M k sample x ∂(sampleMeasure a) := by
          exact
            EconCSLib.Probability.expectedReflectedBottomKSum_eq_integral_rank_count_layer_of_integrable
              M (sampleMeasure a) k hupper hlayer_int
      _ = ∑ i : Fin k, ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a := hlayer_formula
  exact
    paper_lemma1_bounded_support_expected_reflected_bottom_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
      sampleMeasure hprob h_bounds h_reflected tail k_pos hM₀_pos
      hG_measurable hG_mono hG_nonneg hG_le_one hG_eq_one_of_support

/--
Iid product-measure evaluation of the reflected threshold-count layer's inner
expectation.  For a fixed threshold `x`, the reflected count is binomial with
success probability `P[M - X <= x]`.
-/
theorem paper_definition3_iid_reflected_count_layer_inner_integral_binomial
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {M : ℝ} {a k : ℕ} (x : ℝ) :
    ∫ sample : Fin a → ℝ,
        EconCSLib.Probability.reflectedBottomKRankCountLayer M k sample x
        ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure) =
      ∑ i : Fin (min k a),
        ∑ j ∈ Finset.Icc 0 i.val,
        (Nat.choose a j : ℝ) *
          (baseMeasure.real {y : ℝ | M - y ≤ x}) ^ j *
            (1 - baseMeasure.real {y : ℝ | M - y ≤ x}) ^ (a - j) := by
  classical
  let successSet : Set ℝ := {y : ℝ | M - y ≤ x}
  let sampleLaw : MeasureTheory.Measure (Fin a → ℝ) :=
    MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure)
  have hs : MeasurableSet successSet := by
    dsimp [successSet]
    exact measurableSet_le (measurable_const.sub measurable_id) measurable_const
  have hfun :
      (fun sample : Fin a → ℝ =>
        EconCSLib.Probability.reflectedBottomKRankCountLayer M k sample x) =
        fun sample : Fin a → ℝ =>
          ∑ i : Fin (min k a),
            if EconCSLib.Probability.iidSuccessCount successSet sample ≤ i.val
            then (1 : ℝ) else 0 := by
    funext sample
    simp [EconCSLib.Probability.reflectedBottomKRankCountLayer,
      EconCSLib.Probability.iidSuccessCount,
      EconCSLib.Probability.iidSuccessIndexSet,
      EconCSLib.Probability.topKRankEmbedding,
      EconCSLib.Probability.reflectedSample, successSet]
  calc
    ∫ sample : Fin a → ℝ,
        EconCSLib.Probability.reflectedBottomKRankCountLayer M k sample x
        ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure)
        =
        ∫ sample : Fin a → ℝ,
          ∑ i : Fin (min k a),
            if EconCSLib.Probability.iidSuccessCount successSet sample ≤ i.val
            then (1 : ℝ) else 0 ∂sampleLaw := by
          rw [hfun]
    _ =
        ∑ i : Fin (min k a),
          ∫ sample : Fin a → ℝ,
            (if EconCSLib.Probability.iidSuccessCount successSet sample ≤ i.val
              then (1 : ℝ) else 0) ∂sampleLaw := by
          exact MeasureTheory.integral_finset_sum Finset.univ
            (fun i _hi => by
              have hmeas :
                  MeasurableSet
                    {sample : Fin a → ℝ |
                      EconCSLib.Probability.iidSuccessCount successSet sample ≤
                        i.val} :=
                EconCSLib.Probability.iidSuccessCount_le_measurableSet
                  (n := a) hs i.val
              refine ((MeasureTheory.integrable_const (1 : ℝ)).indicator
                hmeas).congr ?_
              filter_upwards with sample
              by_cases hle :
                  EconCSLib.Probability.iidSuccessCount successSet sample ≤
                    i.val
              · simp [hle]
              · simp [hle])
    _ =
        ∑ i : Fin (min k a),
          sampleLaw.real
            {sample : Fin a → ℝ |
              EconCSLib.Probability.iidSuccessCount successSet sample ≤ i.val} := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          have hindicator :
              (fun sample : Fin a → ℝ =>
                if EconCSLib.Probability.iidSuccessCount successSet sample ≤ i.val
                then (1 : ℝ) else 0) =
                {sample : Fin a → ℝ |
                  EconCSLib.Probability.iidSuccessCount successSet sample ≤
                    i.val}.indicator
                  (fun _sample : Fin a → ℝ => (1 : ℝ)) := by
            funext sample
            by_cases hle :
                EconCSLib.Probability.iidSuccessCount successSet sample ≤ i.val
            · simp [hle]
            · simp [hle]
          rw [hindicator, MeasureTheory.integral_indicator_const]
          · simp [sampleLaw, mul_comm]
          · exact EconCSLib.Probability.iidSuccessCount_le_measurableSet
              (n := a) hs i.val
    _ =
        ∑ i : Fin (min k a),
          ∑ j ∈ Finset.Icc 0 i.val,
          (Nat.choose a j : ℝ) *
            (baseMeasure.real {y : ℝ | M - y ≤ x}) ^ j *
              (1 - baseMeasure.real {y : ℝ | M - y ≤ x}) ^ (a - j) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          have hi_le_a : i.val ≤ a :=
            le_trans (Nat.le_of_lt i.isLt) (min_le_right k a)
          have hmin_i : min i.val a = i.val := min_eq_left hi_le_a
          simpa [sampleLaw, successSet, hmin_i] using
            EconCSLib.Probability.iidProductMeasure_successCount_le_real
              (n := a) baseMeasure hs i.val

/--
Same iid reflected-count bridge after naming the reflected CDF as `G`.  This is
the pointwise integrand identity that feeds the bounded Lemma D.2 source
kernel.
-/
theorem paper_definition3_iid_reflected_count_layer_inner_integral_kernel
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {M : ℝ} {G : ℝ → ℝ} {a k : ℕ} (x : ℝ)
    (hGx : baseMeasure.real {y : ℝ | M - y ≤ x} = G x) :
    ∫ sample : Fin a → ℝ,
        EconCSLib.Probability.reflectedBottomKRankCountLayer M k sample x
        ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure) =
      ∑ i : Fin (min k a), ∑ j ∈ Finset.Icc 0 i.val,
        boundedLemmaD2IntegralKernel G j a x := by
  rw [paper_definition3_iid_reflected_count_layer_inner_integral_binomial
    baseMeasure (M := M) (a := a) (k := k) x]
  have hGx' : baseMeasure.real {y : ℝ | M ≤ x + y} = G x := by
    convert hGx using 2
    ext y
    constructor
    · intro hy
      change M - y ≤ x
      change M ≤ x + y at hy
      linarith
    · intro hy
      change M ≤ x + y
      change M - y ≤ x at hy
      linarith
  refine Finset.sum_congr rfl ?_
  intro i _hi
  refine Finset.sum_congr rfl ?_
  intro j _hj
  simp [boundedLemmaD2IntegralKernel, hGx']

/--
Outer threshold-integral assembly for the iid reflected count layer.  Once the
reflected CDF is identified with `G` and the finitely many Lemma D.2 kernels
are integrable, the expectation of the layer-cake count statistic is exactly
the finite sum of source integral terms.
-/
theorem paper_definition3_iid_reflected_count_layer_integral_kernel_of_integrable
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {M : ℝ} {G : ℝ → ℝ} {a k : ℕ}
    (hG :
      ∀ x : ℝ, 0 < x →
        baseMeasure.real {y : ℝ | M - y ≤ x} = G x)
    (h_kernel_integrable :
      ∀ i : Fin (min k a), ∀ j ∈ Finset.Icc 0 i.val,
        MeasureTheory.IntegrableOn
          (fun x : ℝ => boundedLemmaD2IntegralKernel G j a x)
          (Set.Ioi (0 : ℝ))) :
    (∫ x in Set.Ioi (0 : ℝ),
      ∫ sample : Fin a → ℝ,
        EconCSLib.Probability.reflectedBottomKRankCountLayer M k sample x
        ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure)) =
      ∑ i : Fin (min k a), ∑ j ∈ Finset.Icc 0 i.val,
        boundedLemmaD2IntegralTerm G j a := by
  let sampleLaw : MeasureTheory.Measure (Fin a → ℝ) :=
    MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure)
  calc
    (∫ x in Set.Ioi (0 : ℝ),
      ∫ sample : Fin a → ℝ,
        EconCSLib.Probability.reflectedBottomKRankCountLayer M k sample x
        ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure))
        =
        ∫ x in Set.Ioi (0 : ℝ),
          ∑ i : Fin (min k a), ∑ j ∈ Finset.Icc 0 i.val,
            boundedLemmaD2IntegralKernel G j a x := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          exact
            paper_definition3_iid_reflected_count_layer_inner_integral_kernel
              baseMeasure (M := M) (G := G) (a := a) (k := k) x
              (hG x hx)
    _ =
        ∑ i : Fin (min k a),
          ∫ x in Set.Ioi (0 : ℝ),
            ∑ j ∈ Finset.Icc 0 i.val,
              boundedLemmaD2IntegralKernel G j a x := by
          exact MeasureTheory.integral_finset_sum Finset.univ
            (fun i _hi =>
              MeasureTheory.integrable_finset_sum (Finset.Icc 0 i.val)
                (fun j hj => h_kernel_integrable i j hj))
    _ =
        ∑ i : Fin (min k a), ∑ j ∈ Finset.Icc 0 i.val,
          ∫ x in Set.Ioi (0 : ℝ),
            boundedLemmaD2IntegralKernel G j a x := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact MeasureTheory.integral_finset_sum (Finset.Icc 0 i.val)
            (fun j hj => h_kernel_integrable i j hj)
    _ =
      ∑ i : Fin (min k a), ∑ j ∈ Finset.Icc 0 i.val,
        boundedLemmaD2IntegralTerm G j a := by
        rfl

/--
Fixed-`k` version of the iid reflected count-layer integral assembly.  This is
the shape required by the bounded Lemma 1 wrapper after the eventual `k ≤ a`
prefix.
-/
theorem paper_definition3_iid_reflected_count_layer_integral_kernel_of_integrable_of_le
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {M : ℝ} {G : ℝ → ℝ} {a k : ℕ}
    (hka : k ≤ a)
    (hG :
      ∀ x : ℝ, 0 < x →
        baseMeasure.real {y : ℝ | M - y ≤ x} = G x)
    (h_kernel_integrable :
      ∀ i : Fin k, ∀ j ∈ Finset.Icc 0 i.val,
        MeasureTheory.IntegrableOn
          (fun x : ℝ => boundedLemmaD2IntegralKernel G j a x)
          (Set.Ioi (0 : ℝ))) :
    (∫ x in Set.Ioi (0 : ℝ),
      ∫ sample : Fin a → ℝ,
        EconCSLib.Probability.reflectedBottomKRankCountLayer M k sample x
        ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure)) =
      ∑ i : Fin k, ∑ j : Fin (i.val + 1),
        boundedLemmaD2IntegralTerm G j.val a := by
  have hmin : min k a = k := min_eq_left hka
  have h_kernel_integrable' :
      ∀ i : Fin (min k a), ∀ j ∈ Finset.Icc 0 i.val,
        MeasureTheory.IntegrableOn
          (fun x : ℝ => boundedLemmaD2IntegralKernel G j a x)
          (Set.Ioi (0 : ℝ)) := by
    intro i j hj
    let i' : Fin k := ⟨i.val, by simpa [hmin] using i.isLt⟩
    exact h_kernel_integrable i' j (by simpa [i'] using hj)
  have hbase :=
    paper_definition3_iid_reflected_count_layer_integral_kernel_of_integrable
      baseMeasure (M := M) (G := G) (a := a) (k := k) hG
      h_kernel_integrable'
  rw [hmin] at hbase
  calc
    (∫ x in Set.Ioi (0 : ℝ),
      ∫ sample : Fin a → ℝ,
        EconCSLib.Probability.reflectedBottomKRankCountLayer M k sample x
        ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure)) =
        ∑ i : Fin k, ∑ j ∈ Finset.Icc 0 i.val,
          boundedLemmaD2IntegralTerm G j a := hbase
    _ = ∑ i : Fin k, ∑ j : Fin (i.val + 1),
        boundedLemmaD2IntegralTerm G j.val a := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [← Nat.range_succ_eq_Icc_zero i.val]
        exact (Fin.sum_univ_eq_sum_range
          (fun j => boundedLemmaD2IntegralTerm G j a)
          (i.val + 1)).symm

/--
Bounded-support Lemma 1 wrapper specialized to an iid product sample law.
The remaining concrete-distribution obligations are coordinatewise support,
the reflected CDF identity `P[M - X <= x] = G x`, and eventual integrability
of the finite Lemma D.2 kernels.
-/
theorem
    paper_lemma1_bounded_support_iid_reflected_count_layer_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    {β c M L : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_bounds :
      ∀ᶠ a in Filter.atTop,
        ∀ᵐ sample ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure),
          ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M)
    (hG_reflected :
      ∀ x : ℝ, 0 < x →
        baseMeasure.real {y : ℝ | M - y ≤ x} = G x)
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) := by
  let sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ) :=
    fun a => MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure)
  have hprob : ∀ a, MeasureTheory.IsProbabilityMeasure (sampleMeasure a) := by
    intro a
    dsimp [sampleMeasure]
    infer_instance
  have h_layer_integral :
      ∀ᶠ a in Filter.atTop,
        (∫ x in Set.Ioi (0 : ℝ),
          ∫ sample,
            EconCSLib.Probability.reflectedBottomKRankCountLayer
              M k sample x ∂(sampleMeasure a)) =
          ∑ i : Fin k, ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a := by
    have h_kernel_integrable :
        ∀ᶠ a in Filter.atTop,
          ∀ i : Fin k, ∀ j ∈ Finset.Icc 0 i.val,
            MeasureTheory.IntegrableOn
              (boundedLemmaD2IntegralKernel G j a)
              (Set.Ioi (0 : ℝ)) :=
      paper_lemmaD2_bounded_integral_kernel_eventually_fin_integrableOn_of_bounded_support
        hG_measurable M₀ hG_nonneg hG_le_one hG_eq_one_of_support
    filter_upwards [Filter.eventually_ge_atTop k, h_kernel_integrable] with
      a hka hker
    simpa [sampleMeasure] using
      paper_definition3_iid_reflected_count_layer_integral_kernel_of_integrable_of_le
        baseMeasure (M := M) (G := G) (a := a) (k := k)
        hka hG_reflected hker
  simpa [sampleMeasure] using
    paper_lemma1_bounded_support_expected_reflected_count_layer_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
      sampleMeasure hprob h_bounds h_layer_integral tail k_pos hM₀_pos
      hG_measurable hG_mono hG_nonneg hG_le_one
      hG_eq_one_of_support

/--
Iid bounded-support Lemma 1 wrapper whose support hypothesis is the
one-dimensional source-law support.  The generic probability library lifts this
to coordinatewise product support.
-/
theorem
    paper_lemma1_bounded_support_iid_reflected_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    {β c M L : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hG_reflected :
      ∀ x : ℝ, 0 < x →
        baseMeasure.real {y : ℝ | M - y ≤ x} = G x)
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) := by
  have h_bounds :
      ∀ᶠ a in Filter.atTop,
        ∀ᵐ sample ∂MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure),
          ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M := by
    filter_upwards with a
    exact
      EconCSLib.Probability.iidProductMeasure_forall_bounds_ae
        baseMeasure h_base_bounds
  exact
    paper_lemma1_bounded_support_iid_reflected_count_layer_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
      baseMeasure h_bounds hG_reflected tail k_pos hM₀_pos hG_measurable
      hG_mono hG_nonneg hG_le_one hG_eq_one_of_support

/--
Iid bounded-support Lemma 1 wrapper with the reflected CDF fixed to the base
law's distribution function `x ↦ P[M - X <= x]`.  This removes the separate
reflected-CDF identity from the paper-facing boundary.
-/
theorem
    paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    {β c M L : ℝ} {k : ℕ} {M₀ : ℝ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}) β c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable :
      Measurable (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}))
    (hG_mono :
      Monotone (fun x : ℝ => baseMeasure.real {y : ℝ | M - y ≤ x}))
    (hG_nonneg :
      ∀ x : ℝ, 0 ≤ baseMeasure.real {y : ℝ | M - y ≤ x})
    (hG_le_one :
      ∀ x : ℝ, baseMeasure.real {y : ℝ | M - y ≤ x} ≤ 1)
    (hG_eq_one_of_support :
      ∀ x : ℝ, M₀ ≤ x →
        baseMeasure.real {y : ℝ | M - y ≤ x} = 1) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) := by
  exact
    paper_lemma1_bounded_support_iid_reflected_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
      baseMeasure h_base_bounds (by intro x _hx; rfl) tail k_pos hM₀_pos
      hG_measurable hG_mono hG_nonneg hG_le_one hG_eq_one_of_support

/--
Iid bounded-support Lemma 1 wrapper where all routine reflected-CDF facts are
derived from the base source-law support.  The remaining distribution-specific
analytic input is the Lemma D.2 tail sandwich for the reflected CDF.
-/
theorem
    paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail
    {β c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (EconCSLib.Probability.reflectedCDFMass baseMeasure M) β c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) := by
  exact
    paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
      (M₀ := M - L) baseMeasure h_base_bounds
      (by simpa [EconCSLib.Probability.reflectedCDFMass] using tail)
      k_pos hwidth_pos
      (by
        simpa [EconCSLib.Probability.reflectedCDFMass] using
          EconCSLib.Probability.reflectedCDFMass_measurable baseMeasure M)
      (by
        simpa [EconCSLib.Probability.reflectedCDFMass] using
          EconCSLib.Probability.reflectedCDFMass_mono baseMeasure M)
      (by
        intro x
        simpa [EconCSLib.Probability.reflectedCDFMass] using
          EconCSLib.Probability.reflectedCDFMass_nonneg baseMeasure M x)
      (by
        intro x
        simpa [EconCSLib.Probability.reflectedCDFMass] using
          EconCSLib.Probability.reflectedCDFMass_le_one baseMeasure M x)
      (by
        intro x hx
        simpa [EconCSLib.Probability.reflectedCDFMass] using
          EconCSLib.Probability.reflectedCDFMass_eq_one_of_ae_bounds
            baseMeasure h_base_bounds hx)

/--
Bounded-support iid source marginal asymptotic from Lemma 1 plus the explicit
scaled-drop regularity hypothesis needed to pass from loss to first
differences.
-/
theorem
    paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail_and_scaled_drop
    {β c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (EconCSLib.Probability.reflectedCDFMass baseMeasure M) β c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k q) -
                ((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k (q + 1))) /
              ((k : ℝ) * M -
                orderStatisticTopKSumFromMean
                  (expectedOrderStatisticMeanSeq
                    (fun a => MeasureTheory.Measure.pi
                      (fun _ : Fin a => baseMeasure))) k q))))
        Filter.atTop (nhds (1 / β))) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun q =>
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq
            (fun a => MeasureTheory.Measure.pi
              (fun _ : Fin a => baseMeasure))) k (q + 1) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k q)
      (fun q =>
        ((∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c p.2.val) / β) *
          boundedPowerMarginalScale β q) := by
  exact
    bounded_source_forward_marginal_asymptotic_of_loss_ae_and_scaled_drop
      tail.beta_pos
      (boundedLemmaD2LimitCoeff_sum_pos tail.beta_pos tail.c_pos k_pos)
      (paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail
        baseMeasure h_base_bounds tail k_pos hwidth_pos)
      hdrop

/--
Source Lemma 1, bounded-support iid route where the concrete law supplies an
eventual exact reflected-CDF power identity near zero.
-/
theorem
    paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power
    {β c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_reflected_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        EconCSLib.Probability.reflectedCDFMass baseMeasure M x =
          (c / β) * x ^ β)
    (hβ_pos : 0 < β)
    (hc_pos : 0 < c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) :=
  paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail
    baseMeasure h_base_bounds
    (BoundedTailCDFPowerSandwich.of_eventually_eq_const_mul_power
      hβ_pos hc_pos h_reflected_power)
    k_pos hwidth_pos

/--
Bounded-support iid source marginal asymptotic from an exact local reflected-CDF
power identity plus the explicit scaled-drop regularity hypothesis.
-/
theorem
    paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power_and_scaled_drop
    {β c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_reflected_power :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        EconCSLib.Probability.reflectedCDFMass baseMeasure M x =
          (c / β) * x ^ β)
    (hβ_pos : 0 < β)
    (hc_pos : 0 < c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k q) -
                ((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k (q + 1))) /
              ((k : ℝ) * M -
                orderStatisticTopKSumFromMean
                  (expectedOrderStatisticMeanSeq
                    (fun a => MeasureTheory.Measure.pi
                      (fun _ : Fin a => baseMeasure))) k q))))
        Filter.atTop (nhds (1 / β))) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun q =>
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq
            (fun a => MeasureTheory.Measure.pi
              (fun _ : Fin a => baseMeasure))) k (q + 1) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => baseMeasure))) k q)
      (fun q =>
        ((∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c p.2.val) / β) *
          boundedPowerMarginalScale β q) :=
  paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail_and_scaled_drop
    baseMeasure h_base_bounds
    (BoundedTailCDFPowerSandwich.of_eventually_eq_const_mul_power
      hβ_pos hc_pos h_reflected_power)
    k_pos hwidth_pos hdrop

/--
Source Lemma 1, concrete continuous uniform `[0,1]` iid instance.

The reflected CDF is exactly `G(x)=x` near zero, so this is the first fully
instantiated bounded source-law endpoint above the real-sample Definition 3
bridge.
-/
theorem paper_lemma1_uniform01_iid_reflected_cdf_count_layer_top_k_loss_asymptotic
    {k : ℕ} (k_pos : 0 < k) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq
              (fun a => MeasureTheory.Measure.pi
                (fun _ : Fin a => uniform01Measure))) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff 1 1 q.2.val) *
          boundedTailScale 1 a) := by
  simpa using
    paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power
      (β := 1) (c := 1) (M := 1) (L := 0) (k := k)
      uniform01Measure uniform01Measure_ae_bounds
      uniform01_reflectedCDFMass_eventually_eq_power
      (by norm_num) (by norm_num) k_pos (by norm_num)

/--
Source Lemma 1, bounded-support top-`k` loss asymptotic from per-rank
reflected lower order-statistic integral identities.  This is the next
distribution-facing boundary above the aggregate reflected-bottom theorem:
after the eventual `k ≤ a` prefix, the probability proof may evaluate each
fixed reflected order-statistic integral separately and Lean assembles the
top-`k` loss asymptotic.
-/
theorem
    paper_lemma1_bounded_support_expected_reflected_rank_integral_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    {β c M : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (hprob : ∀ a, MeasureTheory.IsProbabilityMeasure (sampleMeasure a))
    (h_order_integrable :
      ∀ᶠ a in Filter.atTop,
        ∀ i ∈ Finset.range (min k a),
          MeasureTheory.Integrable
            (fun sample => sampleOrderStatisticValue sample (a - i))
            (sampleMeasure a))
    (h_top_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.Integrable
          (fun sample => EconCSLib.Probability.sampleTopKSum sample k)
          (sampleMeasure a))
    (h_reflected_integrable :
      ∀ᶠ a in Filter.atTop,
        ∀ hka : k ≤ a,
          ∀ i : Fin k,
            MeasureTheory.Integrable
              (fun sample =>
                EconCSLib.Probability.ascendingOrderStatistic
                  (EconCSLib.Probability.reflectedSample M sample)
                  ⟨i.val, lt_of_lt_of_le i.isLt hka⟩)
              (sampleMeasure a))
    (h_rank_integral :
      ∀ᶠ a in Filter.atTop,
        ∀ hka : k ≤ a,
          ∀ i : Fin k,
            (∫ sample,
              EconCSLib.Probability.ascendingOrderStatistic
                (EconCSLib.Probability.reflectedSample M sample)
                ⟨i.val, lt_of_lt_of_le i.isLt hka⟩ ∂(sampleMeasure a)) =
              ∑ j : Fin (i.val + 1),
                boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) := by
  have h_reflected :
      ∀ᶠ a in Filter.atTop,
        EconCSLib.Probability.expectedReflectedBottomKSum
            M (sampleMeasure a) k =
          ∑ i : Fin k, ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a := by
    filter_upwards
      [Filter.eventually_ge_atTop k, h_reflected_integrable,
        h_rank_integral] with a hka href_int hrank
    calc
      EconCSLib.Probability.expectedReflectedBottomKSum
          M (sampleMeasure a) k =
        ∑ i : Fin k,
          ∫ sample,
            EconCSLib.Probability.ascendingOrderStatistic
              (EconCSLib.Probability.reflectedSample M sample)
              ⟨i.val, lt_of_lt_of_le i.isLt hka⟩ ∂(sampleMeasure a) :=
        EconCSLib.Probability.expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic_of_le
          M (sampleMeasure a) hka (href_int hka)
      _ = ∑ i : Fin k, ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a := by
        exact Finset.sum_congr rfl (fun i _hi => hrank hka i)
  exact
    paper_lemma1_bounded_support_expected_reflected_bottom_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
      sampleMeasure hprob h_order_integrable h_top_integrable h_reflected
      tail k_pos hM₀_pos hG_measurable hG_mono hG_nonneg hG_le_one
      hG_eq_one_of_support

/--
Bounded-support version of the per-rank reflected-integral Lemma 1 wrapper.
Coordinatewise a.e. support in `[L, M]` supplies both the order-statistic
integrability needed to form `μ_D` and the reflected-rank integrability needed
for expectation linearity.
-/
theorem
    paper_lemma1_bounded_support_expected_reflected_rank_integral_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support
    {β c M L : ℝ} {k : ℕ} {G : ℝ → ℝ} {M₀ : ℝ}
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (hprob : ∀ a, MeasureTheory.IsProbabilityMeasure (sampleMeasure a))
    (h_bounds :
      ∀ᶠ a in Filter.atTop,
        ∀ᵐ sample ∂sampleMeasure a, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ M)
    (h_rank_integral :
      ∀ᶠ a in Filter.atTop,
        ∀ hka : k ≤ a,
          ∀ i : Fin k,
            (∫ sample,
              EconCSLib.Probability.ascendingOrderStatistic
                (EconCSLib.Probability.reflectedSample M sample)
                ⟨i.val, lt_of_lt_of_le i.isLt hka⟩ ∂(sampleMeasure a)) =
              ∑ j : Fin (i.val + 1),
                boundedLemmaD2IntegralTerm G j.val a)
    (tail : BoundedTailCDFPowerSandwich G β c)
    (k_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a =>
        (k : ℝ) * M -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k a)
      (fun a =>
        (∑ q : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c q.2.val) *
          boundedTailScale β a) := by
  have h_order_integrable :
      ∀ᶠ a in Filter.atTop,
        ∀ i ∈ Finset.range (min k a),
          MeasureTheory.Integrable
            (fun sample => sampleOrderStatisticValue sample (a - i))
            (sampleMeasure a) := by
    filter_upwards [h_bounds] with a hbounds
    letI : MeasureTheory.IsProbabilityMeasure (sampleMeasure a) := hprob a
    exact
      paper_definition3_sample_order_statistic_topk_range_integrable_of_ae_bounds
        L M (sampleMeasure a) k hbounds
  have h_top_integrable :
      ∀ᶠ a in Filter.atTop,
        MeasureTheory.Integrable
          (fun sample => EconCSLib.Probability.sampleTopKSum sample k)
          (sampleMeasure a) := by
    filter_upwards [h_bounds] with a hbounds
    letI : MeasureTheory.IsProbabilityMeasure (sampleMeasure a) := hprob a
    exact
      paper_definition3_sample_topk_sum_integrable_of_ae_bounds
        L M (sampleMeasure a) k hbounds
  have h_reflected_integrable :
      ∀ᶠ a in Filter.atTop,
        ∀ hka : k ≤ a,
          ∀ i : Fin k,
            MeasureTheory.Integrable
              (fun sample =>
                EconCSLib.Probability.ascendingOrderStatistic
                  (EconCSLib.Probability.reflectedSample M sample)
                  ⟨i.val, lt_of_lt_of_le i.isLt hka⟩)
              (sampleMeasure a) := by
    filter_upwards [h_bounds] with a hbounds
    intro hka i
    letI : MeasureTheory.IsProbabilityMeasure (sampleMeasure a) := hprob a
    exact
      EconCSLib.Probability.reflectedAscendingOrderStatistic_integrable_of_ae_bounds
        M L (sampleMeasure a)
        (⟨i.val, lt_of_lt_of_le i.isLt hka⟩ : Fin a) hbounds
  exact
    paper_lemma1_bounded_support_expected_reflected_rank_integral_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
      sampleMeasure hprob h_order_integrable h_top_integrable
      h_reflected_integrable h_rank_integral tail k_pos hM₀_pos
      hG_measurable hG_mono hG_nonneg hG_le_one hG_eq_one_of_support

/--
Source Theorem 1(ii), exact bounded power-marginal checkpoint.

For a top-one oracle whose marginal value at count `q` is exactly
`q^-((β+1)/β)`, the Lemma D.1-style scaled FOC condition holds with an
`O(1/N)` error. This proves convergence to the paper's `β/(β+1)`
likelihood profile at the optimization layer; the remaining probability work
is to derive the same marginal law, or its asymptotic equivalent, from the
bounded-support order-statistic model.
-/
theorem paper_theorem1_ii_bounded_power_marginal_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (β : ℝ)
    (hβ_pos : 0 < β)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (boundedPowerMarginalOracle T β).toConsumptionModel likelihood 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (β / (β + 1))) := by
  exact
    paper_theorem1_ii_bounded_sequence_homogeneity_of_sublinear_foc_certificate
      (boundedPowerMarginalOracle T β) likelihood 1 β hβ_pos seq
      (boundedPowerMarginalSublinearFOCCertificate
        likelihood β hβ_pos hlike_pos)

/--
Source Theorem 1(ii), bounded-source loss-to-marginal bridge.

The added scaled-drop hypothesis is the discrete regularity condition needed to
turn Lemma 1's bounded loss asymptotic into the marginal scale used by the
power-marginal optimization checkpoint.
-/
theorem paper_theorem1_ii_bounded_forward_marginal_asymptotic_of_loss_ae_and_scaled_drop
    {h : ℕ → ℝ} {A C β : ℝ}
    (hβ_pos : 0 < β) (hC_pos : 0 < C)
    (hloss :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q => A - h q)
        (fun q => C * boundedTailScale β q))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            (((A - h q) - (A - h (q + 1))) / (A - h q))))
        Filter.atTop (nhds (1 / β))) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun q => h (q + 1) - h q)
      (fun q => (C / β) * boundedPowerMarginalScale β q) :=
  bounded_source_forward_marginal_asymptotic_of_loss_ae_and_scaled_drop
    hβ_pos hC_pos hloss hdrop

/--
Source Theorem 1(ii), bounded order-statistic scaled-marginal certificate from
a source-side marginal-asymptotic certificate.
-/
noncomputable def paper_theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_source
    {T : ℕ} {μ : ℕ → ℕ → ℝ} {k : ℕ} {β limitCoeff : ℝ}
    (C : BoundedOrderStatisticScaledMarginalCertificate μ k β limitCoeff) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T μ) k
      (boundedPowerMarginalScale β)
      (fun _ : ItemType T => limitCoeff) :=
  C.toTopKScaledMarginalLimitCertificate

/--
Source Theorem 1(ii), bounded order-statistic scaled-marginal certificate from
a source loss asymptotic plus the explicit scaled-drop regularity hypothesis.
-/
noncomputable def paper_theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_loss_ae_and_scaled_drop
    {T : ℕ} {μ : ℕ → ℕ → ℝ} {k : ℕ} {A C β : ℝ}
    (hβ_pos : 0 < β) (k_pos : 0 < k) (hC_pos : 0 < C)
    (hloss :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q : ℕ => A - orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => C * boundedTailScale β q))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            (((A - orderStatisticTopKSumFromMean μ k q) -
              (A - orderStatisticTopKSumFromMean μ k (q + 1))) /
              (A - orderStatisticTopKSumFromMean μ k q))))
        Filter.atTop (nhds (1 / β))) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T μ) k
      (boundedPowerMarginalScale β)
      (fun _ : ItemType T => C / β) :=
  (BoundedOrderStatisticScaledMarginalCertificate.ofLossAsymptoticAndScaledDrop
    hβ_pos k_pos hC_pos hloss hdrop).toTopKScaledMarginalLimitCertificate

/--
Source Theorem 1(ii), bounded iid reflected-CDF source law as a reusable
scaled-marginal certificate.

This composes the iid reflected-CDF Lemma 1 endpoint with the explicit
scaled-drop regularity condition and returns the optimization-facing
`TopKScaledMarginalLimitCertificate`.
-/
noncomputable def
    paper_theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_reflected_cdf_tail_and_scaled_drop
    {T : ℕ} {β c M L : ℝ} {k : ℕ}
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (tail :
      BoundedTailCDFPowerSandwich
        (EconCSLib.Probability.reflectedCDFMass baseMeasure M) β c)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k q) -
                ((k : ℝ) * M -
                  orderStatisticTopKSumFromMean
                    (expectedOrderStatisticMeanSeq
                      (fun a => MeasureTheory.Measure.pi
                        (fun _ : Fin a => baseMeasure))) k (q + 1))) /
              ((k : ℝ) * M -
                orderStatisticTopKSumFromMean
                  (expectedOrderStatisticMeanSeq
                    (fun a => MeasureTheory.Measure.pi
                      (fun _ : Fin a => baseMeasure))) k q))))
        Filter.atTop (nhds (1 / β))) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T
        (expectedOrderStatisticMeanSeq
          (fun a => MeasureTheory.Measure.pi
            (fun _ : Fin a => baseMeasure)))) k
      (boundedPowerMarginalScale β)
      (fun _ : ItemType T =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff β c p.2.val) / β) :=
  paper_theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_loss_ae_and_scaled_drop
    (T := T)
    (μ := expectedOrderStatisticMeanSeq
      (fun a => MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure)))
    (k := k) (A := (k : ℝ) * M)
    (C := ∑ p : BoundedLemmaD2Index k,
      boundedLemmaD2LimitCoeff β c p.2.val)
    (β := β)
    tail.beta_pos k_pos
    (boundedLemmaD2LimitCoeff_sum_pos tail.beta_pos tail.c_pos k_pos)
    (paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail
      baseMeasure h_base_bounds tail k_pos hwidth_pos)
    hdrop

/--
Source Theorem 1(ii), exact bounded power-marginal checkpoint in direct
equation (6) form.
-/
theorem paper_theorem1_ii_bounded_power_marginal_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (β : ℝ)
    (hβ_pos : 0 < β)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (boundedPowerMarginalOracle T β).toConsumptionModel likelihood 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (β / (β + 1)) /
            ∑ i : ItemType T, (likelihood i) ^ (β / (β + 1)))) := by
  have hnorm_pos :
      0 < ∑ i : ItemType T, (likelihood i) ^ (β / (β + 1)) := by
    exact Finset.sum_pos
      (fun i _ => Real.rpow_pos_of_pos (hlike_pos i) (β / (β + 1)))
      Finset.univ_nonempty
  have hconv :=
    paper_theorem1_ii_bounded_power_marginal_sequence_homogeneity
      likelihood β hβ_pos hlike_pos seq
  have hformula :=
    (paper_definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (β / (β + 1))
        (ne_of_gt hnorm_pos)).1 hconv
  intro t
  simpa using hformula t

/--
Source Theorem 1(ii), exact bounded power-marginal checkpoint as a reusable
scaled-marginal certificate.
-/
noncomputable def paper_theorem1_ii_bounded_power_marginal_scaled_marginal_certificate
    (T : ℕ) (β : ℝ) :
    TopKScaledMarginalLimitCertificate
      (boundedPowerMarginalOracle T β) 1
      (boundedPowerMarginalScale β)
      (fun _ : ItemType T => (1 : ℝ)) :=
  boundedPowerMarginalScaledMarginalLimitCertificate T β

/--
Source Theorem 1(iii), exponential-tail i.i.d. conditional item values,
exposed at the reusable top-`k` certificate seam.
-/
theorem paper_theorem1_iii_exponential_sequence_homogeneity_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (lambda : ℝ)
    (_hlambda_pos : 0 < lambda)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k
        (gammaLikelihoodProfile likelihood 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood 1) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptotic_homogeneity

/--
Source Theorem 1(iii), exponential-tail branch from the Lemma D.1-style
sublinear FOC seam.

The target weights are `p_t`, matching the paper's `1`-homogeneity conclusion;
the remaining distribution work is to derive scaled large-gap marginal
dominance from the logarithmic order-statistic asymptotic (paper equation
(76)).
-/
theorem paper_theorem1_iii_exponential_sequence_homogeneity_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (lambda : ℝ)
    (_hlambda_pos : 0 < lambda)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (1 : ℝ))
        (gammaLikelihoodProfile likelihood 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood 1) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 1(iii), exponential-tail branch from a floor-aware
Lemma D.1-style FOC seam.
-/
theorem
    paper_theorem1_iii_exponential_sequence_homogeneity_of_eventual_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (lambda : ℝ)
    (_hlambda_pos : 0 < lambda)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledEventualSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (1 : ℝ))
        (gammaLikelihoodProfile likelihood 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood 1) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 1(iii), exact top-one exponential instance.

For `k = 1`, the expected maximum of `q` rate-`lambda` exponential draws is
`H_q / lambda`. The exact marginal `1/(lambda*q)` verifies the Lemma D.1-style
scaled FOC condition with an `O(1/N)` error, so every finite optimum sequence
converges to the `γ = 1` likelihood profile.
-/
theorem paper_theorem1_iii_exponential_top_one_harmonic_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (lambda : ℝ)
    (hlambda_pos : 0 < lambda)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopOneHarmonicOracle T lambda).toConsumptionModel
            likelihood 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood 1) := by
  exact
    paper_theorem1_iii_exponential_sequence_homogeneity_of_sublinear_foc_certificate
      (exponentialTopOneHarmonicOracle T lambda) likelihood 1 lambda
      hlambda_pos seq
      (exponentialTopOneHarmonicSublinearFOCCertificate
        likelihood lambda hlambda_pos hlike_pos)

/--
Source Theorem 1(iii), exact top-one exponential direct equation (6) form.
-/
theorem paper_theorem1_iii_exponential_top_one_harmonic_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (lambda : ℝ)
    (hlambda_pos : 0 < lambda)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopOneHarmonicOracle T lambda).toConsumptionModel
            likelihood 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 : ℝ))) := by
  have hnorm_pos :
      0 < ∑ i : ItemType T, (likelihood i) ^ (1 : ℝ) := by
    exact Finset.sum_pos
      (fun i _ => by simpa [Real.rpow_one] using hlike_pos i)
      Finset.univ_nonempty
  have hconv :=
    paper_theorem1_iii_exponential_top_one_harmonic_sequence_homogeneity
      likelihood lambda hlambda_pos hlike_pos seq
  have hformula :=
    (paper_definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (1 : ℝ)
        (ne_of_gt hnorm_pos)).1 hconv
  intro t
  simpa using hformula t

/--
Source Lemma D.3, finite top-`k` exponential order-statistic marginal.

The marginal contribution of the `q+1`st iid exponential draw to the expected
sum of the largest `k` draws is `(1/lambda) * min(k,q+1)/(q+1)`.
-/
theorem paper_theorem1_iii_exponential_top_k_order_statistic_forward_marginal
    (lambda : ℝ) (k q : ℕ) :
    exponentialTopKOrderStatisticValue lambda k (q + 1) -
        exponentialTopKOrderStatisticValue lambda k q =
      (1 / lambda) *
        (((min k (q + 1) : ℕ) : ℝ) / (((q + 1 : ℕ) : ℝ))) :=
  exponentialTopKOrderStatistic_forward_marginal lambda k q

/--
Source Lemma D.3, finite top-`k` exponential order-statistic value.

The exact oracle can be written as the threshold-index sum
`∑_{j=1}^q (1/lambda) * min(k,j)/j`, matching the finite binomial integral
normal form used in the measure-level derivation.
-/
theorem paper_theorem1_iii_exponential_top_k_order_statistic_sum_Icc
    (lambda : ℝ) (k q : ℕ) :
    exponentialTopKOrderStatisticValue lambda k q =
      ∑ j ∈ Finset.Icc 1 q,
        (1 / lambda) *
          (((min k j : ℕ) : ℝ) / (j : ℝ)) :=
  exponentialTopKOrderStatisticValue_eq_sum_Icc lambda k q

/--
Source Lemma D.3, finite top-`k` exponential order-statistic value.

The exact oracle can equivalently be written as the double upper-tail harmonic
sum targeted by the threshold-count integration route.
-/
theorem paper_theorem1_iii_exponential_top_k_order_statistic_tail_harmonic_sum
    (lambda : ℝ) (k q : ℕ) :
    exponentialTopKOrderStatisticValue lambda k q =
      (1 / lambda) *
        ∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q, (1 / (j : ℝ)) :=
  exponentialTopKOrderStatisticValue_eq_tail_harmonic_sum lambda k q

/--
Source Lemma D.3, finite top-`k` exponential marginal nonnegativity.
-/
theorem paper_theorem1_iii_exponential_top_k_order_statistic_marginal_nonnegative
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (k q : ℕ) :
    0 ≤
      exponentialTopKOrderStatisticValue lambda k (q + 1) -
        exponentialTopKOrderStatisticValue lambda k q :=
  exponentialTopKOrderStatistic_forward_marginal_nonneg
    lambda hlambda_pos k q

/--
Source Lemma D.3, finite top-`k` exponential diminishing marginal values.
-/
theorem paper_theorem1_iii_exponential_top_k_order_statistic_marginal_antitone
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (k q : ℕ) :
    exponentialTopKOrderStatisticValue lambda k (q + 2) -
        exponentialTopKOrderStatisticValue lambda k (q + 1) ≤
      exponentialTopKOrderStatisticValue lambda k (q + 1) -
        exponentialTopKOrderStatisticValue lambda k q :=
  exponentialTopKOrderStatistic_forward_marginal_antitone_succ
    lambda hlambda_pos k q

/--
Source Lemma D.3, eventual strict diminishing marginal values for finite
top-`k` exponential order statistics.
-/
theorem
    paper_theorem1_iii_exponential_top_k_order_statistic_marginal_strict_antitone
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {k q : ℕ} (hk_pos : 0 < k) (hk_le : k ≤ q + 1) :
    exponentialTopKOrderStatisticValue lambda k (q + 2) -
        exponentialTopKOrderStatisticValue lambda k (q + 1) <
      exponentialTopKOrderStatisticValue lambda k (q + 1) -
        exponentialTopKOrderStatisticValue lambda k q :=
  exponentialTopKOrderStatistic_forward_marginal_strict_antitone_succ_of_le
    lambda hlambda_pos hk_pos hk_le

/--
Source Lemma D.3, finite top-`k` exponential harmonic closed form.

Once `q >= k > 0`, the exact marginal-spacings oracle equals
`(k/lambda) * (1 + H_q - H_k)`, the finite version of the paper's logarithmic
asymptotic.
-/
theorem paper_theorem1_iii_exponential_top_k_order_statistic_harmonic_closed_form
    (lambda : ℝ) {k q : ℕ} (hk_pos : 0 < k) (hkq : k ≤ q) :
    exponentialTopKOrderStatisticValue lambda k q =
      (1 / lambda) * ((k : ℝ) * (1 + harmonicReal q - harmonicReal k)) :=
  exponentialTopKOrderStatisticValue_eq_harmonic_of_k_le
    lambda hk_pos hkq

/--
Source Lemma D.3, near-full finite top-`k` exponential order-statistic value.

At `k = q - 1`, the exact oracle equals the full-sample mean minus the expected
minimum `1/(q*lambda)`.
-/
theorem paper_theorem1_iii_exponential_top_k_order_statistic_pred_card_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    exponentialTopKOrderStatisticValue lambda (q - 1) q =
      (1 / lambda) * (q : ℝ) - 1 / ((q : ℝ) * lambda) :=
  exponentialTopKOrderStatisticValue_pred_card
    lambda hlambda_pos

/--
Source Lemma D.3, finite top-`k` exponential logarithmic asymptotic.

The exact fixed-`k` order-statistic oracle differs from
`(k/lambda) * log q` by a convergent constant term.
-/
theorem paper_theorem1_iii_exponential_top_k_order_statistic_log_asymptotic
    (lambda : ℝ) (k : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        exponentialTopKOrderStatisticValue lambda k q -
          ((1 / lambda) * (k : ℝ)) * Real.log q)
      Filter.atTop
      (nhds
        (((1 / lambda) * (k : ℝ)) *
          (1 + Real.eulerMascheroniConstant - harmonicReal k))) :=
  exponentialTopKOrderStatisticValue_sub_log_tendsto lambda k

/--
Source Lemma D.3, scaled-marginal certificate for the finite top-`k`
exponential order-statistic oracle.
-/
noncomputable def paper_theorem1_iii_exponential_top_k_scaled_marginal_certificate
    (T : ℕ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda)
    (hk_pos : 0 < k) :
    TopKScaledMarginalLimitCertificate
      (exponentialTopKOrderStatisticOracle T lambda k) k
      (exponentialTopKOrderStatisticScale lambda k)
      (fun _ : ItemType T => (1 : ℝ)) :=
  exponentialTopKOrderStatisticScaledMarginalLimitCertificate
    T lambda k hlambda_pos hk_pos

/--
Source Lemma D.3, finite top-`k` exponential diminishing-returns model.
-/
theorem paper_theorem1_iii_exponential_top_k_order_statistic_diminishing_returns
    {T : ℕ} (likelihood : ItemType T → ℝ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda) :
    ((exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
      likelihood k).HasDiminishingReturns :=
  exponentialTopKOrderStatisticConsumptionModel_has_diminishing_returns
    likelihood lambda k hlambda_pos

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

The concrete top-`k` sum of a finite vector of exponential draws is measurable.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_k_sum_measurable
    {q : ℕ} (k : ℕ) :
    Measurable (exponentialFiniteSampleTopKSum (q := q) k) :=
  exponentialFiniteSampleTopKSum_measurable k

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

When the sample maximum is nonnegative, the top-`k` sum is bounded by
`k` times the sample maximum.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_k_sum_le_k_mul_max
    {q : ℕ} [NeZero q] (k : ℕ) (sample : Fin q → ℝ)
    (hmax_nonneg :
      0 ≤ EconCSLib.Probability.Exponential.finiteSampleMax sample) :
    exponentialFiniteSampleTopKSum k sample ≤
      (k : ℝ) * EconCSLib.Probability.Exponential.finiteSampleMax sample :=
  exponentialFiniteSampleTopKSum_le_k_mul_finiteSampleMax
    k sample hmax_nonneg

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

For `k = 1`, the at-most-one top-`k` sample statistic agrees with the finite
sample maximum whenever that maximum is nonnegative.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_one_sum_eq_max
    {q : ℕ} [NeZero q] (sample : Fin q → ℝ)
    (hmax_nonneg :
      0 ≤ EconCSLib.Probability.Exponential.finiteSampleMax sample) :
    exponentialFiniteSampleTopKSum 1 sample =
      EconCSLib.Probability.Exponential.finiteSampleMax sample :=
  exponentialFiniteSampleTopKSum_one_eq_finiteSampleMax sample hmax_nonneg

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

If `k` covers the whole finite sample and all coordinates are nonnegative, the
top-`k` statistic is the full sample sum.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_k_sum_eq_sum_of_card_le
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (hqk : q ≤ k) (h_nonneg : ∀ i, 0 ≤ sample i) :
    exponentialFiniteSampleTopKSum k sample = ∑ i, sample i :=
  exponentialFiniteSampleTopKSum_eq_sum_of_card_le
    k sample hqk h_nonneg

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

At `k = 0`, the at-most-`k` top-sum statistic is identically zero.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_k_zero_sum
    {q : ℕ} (sample : Fin q → ℝ) :
    exponentialFiniteSampleTopKSum 0 sample = 0 :=
  exponentialFiniteSampleTopKSum_zero sample

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

For nonnegative samples, the near-full top-`q-1` statistic is the full sample
sum minus the finite sample minimum.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_pred_card_eq_sum_sub_min
    {q : ℕ} [NeZero q] (sample : Fin q → ℝ)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    exponentialFiniteSampleTopKSum (q - 1) sample =
      (∑ i : Fin q, sample i) -
        EconCSLib.Probability.Exponential.finiteSampleMin sample :=
  exponentialFiniteSampleTopKSum_pred_card_eq_sum_sub_min
    sample h_nonneg

/--
Source Lemma D.3, iid exponential threshold-count bridge.

For a fixed nonnegative threshold `x`, the probability of any prescribed set of
coordinates exceeding `x` factors into exponential survival and CDF terms.
-/
theorem paper_theorem1_iii_exponential_success_index_set_probability
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (s : Finset (Fin q)) :
    ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
        {sample : Fin q → ℝ |
          successIndexSet (fun y : ℝ => x < y) sample = s} =
      (Real.exp (-(lambda * x))) ^ s.card *
        (1 - Real.exp (-(lambda * x))) ^ (q - s.card) :=
  exponentialProductMeasure_successIndexSet_eq_real
    lambda hlambda_pos x hx s

/--
Source Lemma D.3, iid exponential threshold-count bridge.

For a fixed nonnegative threshold `x`, the number of coordinates exceeding `x`
has the expected binomial mass formula under the iid exponential product measure.
-/
theorem paper_theorem1_iii_exponential_success_count_probability
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (j : ℕ) :
    ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
        {sample : Fin q → ℝ |
          (successIndexSet (fun y : ℝ => x < y) sample).card = j} =
      (Nat.choose q j : ℝ) *
        (Real.exp (-(lambda * x))) ^ j *
          (1 - Real.exp (-(lambda * x))) ^ (q - j) :=
  exponentialProductMeasure_successIndexSet_card_eq_real
    lambda hlambda_pos x hx j

/--
Source Lemma D.3, iid exponential threshold-count bridge.

The number of coordinates exceeding a fixed threshold is a measurable random
variable on the finite iid product sample space.
-/
theorem paper_theorem1_iii_exponential_success_count_measurable
    {q : ℕ} (x : ℝ) :
    Measurable
      (fun sample : Fin q → ℝ =>
        (successIndexSet (fun y : ℝ => x < y) sample).card) :=
  exponentialSuccessCount_measurable x

/--
Source Lemma D.3, iid exponential threshold-count bridge.

The real-valued truncated threshold-count random variable is measurable.
-/
theorem paper_theorem1_iii_exponential_success_count_min_real_measurable
    {q : ℕ} (x : ℝ) (k : ℕ) :
    Measurable
      (fun sample : Fin q → ℝ =>
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)) :=
  exponentialSuccessCount_min_real_measurable x k

/--
Source Lemma D.3, iid exponential threshold-count bridge.

For a fixed nonnegative threshold `x`, the number of coordinates exceeding `x`
has the expected binomial upper-tail formula under the iid exponential product
measure.
-/
theorem paper_theorem1_iii_exponential_success_count_tail_probability
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (r : ℕ) :
    ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
        {sample : Fin q → ℝ |
          r ≤ (successIndexSet (fun y : ℝ => x < y) sample).card} =
      ∑ j ∈ Finset.Icc r q,
        (Nat.choose q j : ℝ) *
          (Real.exp (-(lambda * x))) ^ j *
            (1 - Real.exp (-(lambda * x))) ^ (q - j) :=
  exponentialProductMeasure_successIndexSet_card_ge_real
    lambda hlambda_pos x hx r

/--
Source Lemma D.3, iid exponential threshold-count bridge.

For a fixed nonnegative threshold, the expectation of the truncated threshold
count `min k count` is the finite binomial sum obtained from the exact count
mass formula.
-/
theorem paper_theorem1_iii_exponential_success_count_min_integral_finite_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    ∫ sample,
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∑ j ∈ Finset.Icc 0 q,
        ((min k j : ℕ) : ℝ) *
          ((Nat.choose q j : ℝ) *
            (Real.exp (-(lambda * x))) ^ j *
              (1 - Real.exp (-(lambda * x))) ^ (q - j)) :=
  exponentialProductMeasure_successCount_min_integral_eq_finite_sum
    lambda hlambda_pos x hx k

/--
Source Lemma D.3, iid exponential threshold-count bridge.

For a fixed threshold, the expectation of the truncated threshold count is the
sum of the upper-tail probabilities `P(count >= r)`, for `1 <= r <= k`.
-/
theorem paper_theorem1_iii_exponential_success_count_min_integral_tail_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (k : ℕ) :
    ∫ sample,
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∑ r ∈ Finset.Icc 1 k,
        ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
          {sample : Fin q → ℝ |
            r ≤ (successIndexSet (fun y : ℝ => x < y) sample).card} :=
  exponentialProductMeasure_successCount_min_integral_eq_tail_sum
    lambda hlambda_pos x k

/--
Source Lemma D.3, iid exponential threshold-count bridge.

The fixed-threshold truncated-count expectation also has the binomial
upper-tail expansion obtained by summing `P(count >= r)` over `1 <= r <= k`.
-/
theorem paper_theorem1_iii_exponential_success_count_min_integral_tail_binomial_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    ∫ sample,
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∑ r ∈ Finset.Icc 1 k,
        ∑ j ∈ Finset.Icc r q,
          (Nat.choose q j : ℝ) *
            (Real.exp (-(lambda * x))) ^ j *
              (1 - Real.exp (-(lambda * x))) ^ (q - j) :=
  exponentialProductMeasure_successCount_min_integral_eq_tail_binomial_sum
    lambda hlambda_pos x hx k

/--
Source Lemma D.3, analytic binomial-mass integration support.

Each fixed positive binomial mass term in the threshold-count formula expands
to a finite alternating sum of exponential-tail integrals.
-/
theorem paper_theorem1_iii_exponential_binomial_mass_integral_alternating_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q j : ℕ} (hj_pos : 0 < j) (hjq : j ≤ q) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Nat.choose q j : ℝ) *
          (Real.exp (-(lambda * x))) ^ j *
            (1 - Real.exp (-(lambda * x))) ^ (q - j) =
      (Nat.choose q j : ℝ) *
        ∑ m ∈ Finset.range (q - j + 1),
          ((-1 : ℝ) ^ (m + (q - j)) *
            ((q - j).choose m : ℝ)) *
            (1 / (((q - m : ℕ) : ℝ) * lambda)) :=
  exponentialBinomialMass_integral_eq_alternating_sum
    lambda hlambda_pos hj_pos hjq

/--
Source Lemma D.3, analytic binomial-mass integration support.

Each fixed positive binomial mass term in the threshold-count formula
integrates to the reciprocal harmonic contribution `(1/lambda) * (1/j)`.
-/
theorem paper_theorem1_iii_exponential_binomial_mass_integral_closed_form
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q j : ℕ} (hj_pos : 0 < j) (hjq : j ≤ q) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Nat.choose q j : ℝ) *
          (Real.exp (-(lambda * x))) ^ j *
            (1 - Real.exp (-(lambda * x))) ^ (q - j) =
      (1 / lambda) * (1 / ((j : ℕ) : ℝ)) :=
  exponentialBinomialMass_integral_eq_inv_lambda_mul_inv
    lambda hlambda_pos hj_pos hjq

/--
Source Lemma D.3, deterministic threshold-count layer-cake support.

For a nonnegative finite sample, integrating the number of coordinates above a
threshold over positive thresholds recovers the full sample sum.
-/
theorem paper_theorem1_iii_exponential_success_count_integral_eq_sum
    {q : ℕ} (sample : Fin q → ℝ)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    ∫ x in Set.Ioi (0 : ℝ),
        ((successIndexSet (fun y : ℝ => x < y) sample).card : ℝ) =
      ∑ i : Fin q, sample i :=
  successCount_integral_eq_sum sample h_nonneg

/--
Source Lemma D.3, deterministic top-`k` threshold-count layer-cake bridge.

For a nonnegative finite sample, the concrete at-most-`k` top-sum equals the
integral over positive thresholds of the truncated exceedance count
`min k count{x_i > x}`.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_k_layer_cake
    {q : ℕ} (k : ℕ) (sample : Fin q → ℝ)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    exponentialFiniteSampleTopKSum k sample =
      ∫ x in Set.Ioi (0 : ℝ),
        ((min k
          (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ) :=
  exponentialFiniteSampleTopKSum_eq_integral_min_successCount
    k sample h_nonneg

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

The concrete top-`k` sum is integrable under the iid exponential product
measure.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_k_sum_integrable
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    MeasureTheory.Integrable
      (exponentialFiniteSampleTopKSum (q := q) k)
      ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q) :=
  exponentialFiniteSampleTopKSum_integrable
    (exponentialDistributionModel lambda hlambda_pos) k

/--
Source Lemma D.3, measure-facing top-`k` threshold-count layer-cake bridge.

Under the iid exponential product measure, the expected concrete top-`k`
sample statistic equals the expected deterministic layer-cake integral of the
truncated threshold count.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_k_integral_layer_cake
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∫ sample,
        (∫ x in Set.Ioi (0 : ℝ),
          ((min k
            (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ))
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q :=
  exponentialFiniteSampleTopKSum_integral_eq_thresholdLayerCakeIntegral
    lambda hlambda_pos k

/--
Source Lemma D.3, measure-facing Fubini bridge.

The joint threshold-count integrand is integrable, so the iid sample integral
and positive-threshold integral may be swapped.
-/
theorem paper_theorem1_iii_exponential_threshold_layer_cake_integral_swap
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        (∫ x in Set.Ioi (0 : ℝ),
          ((min k
            (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ))
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∫ x in Set.Ioi (0 : ℝ),
        (∫ sample,
          ((min k
            (successIndexSet (fun y : ℝ => x < y) sample).card : ℕ) : ℝ)
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q) :=
  thresholdLayerCakeIntegral_integral_swap lambda hlambda_pos k

/--
Source Lemma D.3, measure-facing binomial-tail reduction.

The concrete iid top-`k` expectation reduces to a one-dimensional integral of
the fixed-threshold binomial upper-tail sum.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_k_tail_binomial_integral
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      ∫ x in Set.Ioi (0 : ℝ),
        (∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q,
            (Nat.choose q j : ℝ) *
              (Real.exp (-(lambda * x))) ^ j *
                (1 - Real.exp (-(lambda * x))) ^ (q - j)) :=
  exponentialFiniteSampleTopKSum_integral_eq_tail_binomial_integral
    lambda hlambda_pos k

/--
Source Lemma D.3, measure-facing top-`k` harmonic reduction.

The concrete iid top-`k` expectation reduces to the same double upper-tail
harmonic sum as the closed finite exponential order-statistic oracle.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_k_tail_harmonic_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      (1 / lambda) *
        ∑ r ∈ Finset.Icc 1 k,
          ∑ j ∈ Finset.Icc r q, (1 / (j : ℝ)) :=
  exponentialFiniteSampleTopKSum_integral_eq_tail_harmonic_sum
    lambda hlambda_pos k

/--
Source Lemma D.3, measure-facing finite top-`k` sample statistic.

For every nonzero sample size `q`, the concrete iid exponential top-`k`
expectation matches the exact finite order-statistic oracle.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_k_integral_order_statistic
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] (k : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopKOrderStatisticValue lambda k q :=
  exponentialFiniteSampleTopKSum_integral_eq_orderStatisticValue
    lambda hlambda_pos k

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

The `k = 1` concrete top-`k` sample statistic has the same iid exponential
expectation as the finite maximum, namely `H_q/lambda`.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_one_integral_harmonic_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) 1 sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopOneHarmonicValue lambda q :=
  exponentialFiniteSampleTopKSum_one_integral_eq_harmonicValue
    lambda hlambda_pos

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

When `k ≥ q`, the concrete iid-sample top-`k` expectation matches the exact
finite exponential order-statistic oracle.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_k_card_le_integral_order_statistic
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] {k : ℕ} (hqk : q ≤ k) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) k sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopKOrderStatisticValue lambda k q :=
  exponentialFiniteSampleTopKSum_card_le_integral_eq_orderStatisticValue
    lambda hlambda_pos hqk

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

At `k = q - 1`, the concrete iid-sample top-`k` expectation matches the exact
finite exponential order-statistic oracle by subtracting the verified expected
minimum from the full-sample sum.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_pred_card_integral_order_statistic
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) (q - 1) sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopKOrderStatisticValue lambda (q - 1) q :=
  exponentialFiniteSampleTopPredCard_integral_eq_orderStatisticValue
    lambda hlambda_pos

/--
Source Theorem 1(iii), measure-facing finite top-`k` sample statistic.

At `k = 0`, the concrete iid-sample top-`k` expectation matches the exact
finite exponential order-statistic oracle.
-/
theorem paper_theorem1_iii_exponential_finite_sample_top_k_zero_integral_order_statistic
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (q : ℕ) :
    ∫ sample,
        exponentialFiniteSampleTopKSum (q := q) 0 sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopKOrderStatisticValue lambda 0 q :=
  exponentialFiniteSampleTopKSum_zero_integral_eq_orderStatisticValue
    lambda hlambda_pos q

/--
Source Theorem 1(iii), exact finite top-`k` exponential order-statistic
instance.

For every fixed positive `k`, the expected top-`k` oracle with marginal
increment `(1/lambda) * min(k,q)/q` verifies the Lemma D.1-style scaled FOC
condition with an `O(1/N)` error, so every finite optimum sequence converges to
the `γ = 1` likelihood profile.
-/
theorem paper_theorem1_iii_exponential_top_k_order_statistic_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda)
    (hk_pos : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
            likelihood k)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood 1) := by
  exact
    paper_theorem1_iii_exponential_sequence_homogeneity_of_sublinear_foc_certificate
      (exponentialTopKOrderStatisticOracle T lambda k) likelihood k lambda
      hlambda_pos seq
      (exponentialTopKOrderStatisticSublinearFOCCertificate
        likelihood lambda k hlambda_pos hk_pos hlike_pos)

/--
Source Theorem 1(iii), exact finite top-`k` exponential direct equation (6)
form.
-/
theorem paper_theorem1_iii_exponential_top_k_order_statistic_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda)
    (hk_pos : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
            likelihood k)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 : ℝ))) := by
  have hnorm_pos :
      0 < ∑ i : ItemType T, (likelihood i) ^ (1 : ℝ) := by
    exact Finset.sum_pos
      (fun i _ => by simpa [Real.rpow_one] using hlike_pos i)
      Finset.univ_nonempty
  have hconv :=
    paper_theorem1_iii_exponential_top_k_order_statistic_sequence_homogeneity
      likelihood lambda k hlambda_pos hk_pos hlike_pos seq
  have hformula :=
    (paper_definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (1 : ℝ)
        (ne_of_gt hnorm_pos)).1 hconv
  intro t
  simpa using hformula t

/--
Source Theorem 1(iii), iid product-measure maximum survival.

For `q` iid rate-`lambda` exponential draws and `x >= 0`, the probability that
the finite maximum exceeds `x` is the analytic expression
`1 - (1 - exp (-lambda*x))^q`.
-/
theorem paper_theorem1_iii_exponential_product_max_survival_eq_formula
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] {x : ℝ} (hx : 0 ≤ x) :
    1 - (((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
        {sample : Fin q → ℝ |
          EconCSLib.Probability.Exponential.finiteSampleMax sample ≤ x}).toReal =
      exponentialMaxSurvival lambda q x :=
  exponentialProductMaxSurvival_eq_formula lambda hlambda_pos hx

/--
Source Theorem 1(iii), exponential maximum survival algebra.

On the nonnegative line the rate-`lambda` exponential CDF gives maximum
survival `1 - (1 - exp (-lambda*x))^q`; this theorem records the finite
binomial expansion into exponential-tail terms used by the all-`q` integral
route.
-/
theorem paper_theorem1_iii_exponential_max_survival_binomial_expansion
    (lambda : ℝ) (q : ℕ) (x : ℝ) :
    exponentialMaxSurvival lambda q x =
      - ∑ m ∈ Finset.range q,
          (-1 : ℝ) ^ (m + q) *
            (Real.exp (-(lambda * x))) ^ (q - m) *
            (q.choose m : ℝ) :=
  exponentialMaxSurvival_expansion lambda q x

/--
Source Theorem 1(iii), exponential maximum survival term integral.

Every positive natural power produced by the binomial survival expansion has
the closed integral `1/(n*lambda)` over `[0,∞)`.
-/
theorem paper_theorem1_iii_exponential_survival_power_integral
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {n : ℕ} (hn : 0 < n) :
    ∫ x in Set.Ioi (0 : ℝ), (Real.exp (-(lambda * x))) ^ n =
      1 / ((n : ℝ) * lambda) :=
  exponentialSurvivalPower_integral lambda hlambda_pos hn

/--
Source Theorem 1(iii), exponential maximum survival integral reduced to a
finite alternating binomial sum.
-/
theorem paper_theorem1_iii_exponential_max_survival_integral_finite_sum
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (q : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), exponentialMaxSurvival lambda q x =
      - ∑ m ∈ Finset.range q,
          ((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
            (1 / (((q - m : ℕ) : ℝ) * lambda)) :=
  exponentialMaxSurvival_integral_eq_finite_sum lambda hlambda_pos q

/--
Source Theorem 1(iii), exponential finite alternating binomial sum collapsed to
the exact harmonic expected-maximum value.
-/
theorem paper_theorem1_iii_exponential_finite_sum_eq_harmonic_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (q : ℕ) :
    - ∑ m ∈ Finset.range q,
        ((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
          (1 / (((q - m : ℕ) : ℝ) * lambda)) =
      exponentialTopOneHarmonicValue lambda q := by
  simpa [exponentialTopOneHarmonicValue] using
    exponentialMaxSurvival_finite_sum_eq_harmonicValue lambda hlambda_pos q

/--
Source Theorem 1(iii), all-`q` exponential maximum survival integral in
harmonic closed form.
-/
theorem paper_theorem1_iii_exponential_max_survival_integral_harmonic_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (q : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), exponentialMaxSurvival lambda q x =
      exponentialTopOneHarmonicValue lambda q := by
  simpa [exponentialTopOneHarmonicValue] using
    exponentialMaxSurvival_integral_eq_harmonicValue lambda hlambda_pos q

/--
Source Theorem 1(iii), iid product-measure maximum survival integral in
harmonic closed form.
-/
theorem paper_theorem1_iii_exponential_product_max_survival_integral_harmonic_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ x in Set.Ioi (0 : ℝ),
        (1 - (((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
          {sample : Fin q → ℝ |
            EconCSLib.Probability.Exponential.finiteSampleMax sample ≤ x}).toReal) =
      exponentialTopOneHarmonicValue lambda q :=
  exponentialProductMaxSurvival_integral_eq_harmonicValue
    lambda hlambda_pos

/--
Source Theorem 1(iii), iid product-measure maximum tail integral in harmonic
closed form.

This exposes the layer-cake tail-probability side
`μ.real {sample | x < max sample}` for the finite iid maximum.
-/
theorem paper_theorem1_iii_exponential_product_max_tail_integral_harmonic_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ x in Set.Ioi (0 : ℝ),
        ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q).real
          {sample : Fin q → ℝ |
            x < EconCSLib.Probability.Exponential.finiteSampleMax sample} =
      exponentialTopOneHarmonicValue lambda q :=
  exponentialProductMaxTailIntegral_eq_harmonicValue
    lambda hlambda_pos

/--
Source Theorem 1(iii), conditional iid product-measure expected maximum in
harmonic closed form.

The remaining hypothesis is the standard integrability of the finite maximum;
the library discharges the a.e.-nonnegativity needed by layer cake.
-/
theorem paper_theorem1_iii_exponential_product_max_integral_harmonic_value_of_integrable
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q]
    (h_int : MeasureTheory.Integrable
      (EconCSLib.Probability.Exponential.finiteSampleMax (q := q))
      ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)) :
    ∫ sample,
        EconCSLib.Probability.Exponential.finiteSampleMax sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopOneHarmonicValue lambda q :=
  exponentialProductMaxIntegral_eq_harmonicValue_of_integrable
    lambda hlambda_pos h_int

/--
Source Theorem 1(iii), iid product-measure expected maximum in harmonic closed
form.
-/
theorem paper_theorem1_iii_exponential_product_max_integral_harmonic_value
    (lambda : ℝ) (hlambda_pos : 0 < lambda)
    {q : ℕ} [NeZero q] :
    ∫ sample,
        EconCSLib.Probability.Exponential.finiteSampleMax sample
          ∂(exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q =
      exponentialTopOneHarmonicValue lambda q :=
  exponentialProductMaxIntegral_eq_harmonicValue
    lambda hlambda_pos

/--
Source Theorem 1(iii), exponential top-one measure-facing base case.

For a single draw from the rate-`lambda` exponential model, integrating the
survival function of the model CDF over `[0,∞)` gives the exact `H_1/lambda`
harmonic value.
-/
theorem paper_theorem1_iii_exponential_single_draw_survival_integral
    (lambda : ℝ) (hlambda_pos : 0 < lambda) :
    ∫ x in Set.Ioi (0 : ℝ),
        (1 - ProbabilityTheory.cdf
          (exponentialDistributionModel lambda hlambda_pos).measure x) =
      exponentialTopOneHarmonicValue lambda 1 :=
  exponentialTopOneHarmonic_singleDraw_survival_integral lambda hlambda_pos

/--
Source Theorem 1(iii), exponential top-one log approximation.

For the exact harmonic oracle, `H_q/lambda` differs from the paper's
`(1/lambda) log q` approximation by a convergent constant term.
-/
theorem paper_theorem1_iii_exponential_top_one_harmonic_log_approximation
    (lambda : ℝ) :
    Filter.Tendsto
      (fun q : ℕ =>
        exponentialTopOneHarmonicValue lambda q -
          (1 / lambda) * Real.log q)
      Filter.atTop
      (nhds ((1 / lambda) * Real.eulerMascheroniConstant)) :=
  exponentialTopOneHarmonicValue_sub_log_tendsto lambda

/--
Source Theorem 1(iv), Pareto i.i.d. conditional item values, exposed at the
reusable top-`k` certificate seam.
-/
theorem paper_theorem1_iv_pareto_sequence_homogeneity_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (α : ℝ)
    (_hα_gt_one : 1 < α)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k
        (gammaLikelihoodProfile likelihood (α / (α - 1)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (α / (α - 1))) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptotic_homogeneity

/--
Source Theorem 1(iv), Pareto branch from the Lemma D.1-style sublinear FOC
seam.

The target weights are `p_t^(α/(α-1))`; the remaining distribution work is to
derive scaled large-gap marginal dominance from the Pareto order-statistic
asymptotic (paper equation (77)).
-/
theorem paper_theorem1_iv_pareto_sequence_homogeneity_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (α : ℝ)
    (_hα_gt_one : 1 < α)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (α / (α - 1)))
        (gammaLikelihoodProfile likelihood (α / (α - 1)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (α / (α - 1))) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 1(iv), Pareto branch from a floor-aware Lemma D.1-style FOC
seam.
-/
theorem
    paper_theorem1_iv_pareto_sequence_homogeneity_of_eventual_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (α : ℝ)
    (_hα_gt_one : 1 < α)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      PairwiseScaledEventualSublinearFOCCertificate
        (fun _ => O.toConsumptionModel likelihood k)
        (fun t : ItemType T => likelihood t ^ (α / (α - 1)))
        (gammaLikelihoodProfile likelihood (α / (α - 1)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (α / (α - 1))) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 1(iv), exact Pareto power-marginal checkpoint.

For a top-one oracle whose marginal value at count `q` is exactly
`q^-((α-1)/α)`, the Lemma D.1-style scaled FOC condition holds with an
`O(1/N)` error. This proves convergence to the paper's
`α/(α-1)` likelihood profile at the optimization layer; the remaining
probability work is to derive the same marginal law, or its asymptotic
equivalent, from the actual Pareto order-statistic model.
-/
theorem paper_theorem1_iv_pareto_power_marginal_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α : ℝ)
    (hα_gt_one : 1 < α)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (paretoPowerMarginalOracle T α).toConsumptionModel
            likelihood 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (α / (α - 1))) := by
  exact
    paper_theorem1_iv_pareto_sequence_homogeneity_of_sublinear_foc_certificate
      (paretoPowerMarginalOracle T α) likelihood 1 α hα_gt_one seq
      (paretoPowerMarginalSublinearFOCCertificate
        likelihood α hα_gt_one hlike_pos)

/--
Source Theorem 1(iv), exact Pareto power-marginal direct equation (6) form.
-/
theorem paper_theorem1_iv_pareto_power_marginal_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α : ℝ)
    (hα_gt_one : 1 < α)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (paretoPowerMarginalOracle T α).toConsumptionModel
            likelihood 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (α / (α - 1)) /
            ∑ i : ItemType T,
              (likelihood i) ^ (α / (α - 1)))) := by
  have hnorm_pos :
      0 < ∑ i : ItemType T,
        (likelihood i) ^ (α / (α - 1)) := by
    exact Finset.sum_pos
      (fun i _ => Real.rpow_pos_of_pos
        (hlike_pos i) (α / (α - 1)))
      Finset.univ_nonempty
  have hconv :=
    paper_theorem1_iv_pareto_power_marginal_sequence_homogeneity
      likelihood α hα_gt_one hlike_pos seq
  have hformula :=
    (paper_definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (α / (α - 1))
        (ne_of_gt hnorm_pos)).1 hconv
  intro t
  simpa using hformula t

/--
Source Theorem 1(iv), exact Pareto power-marginal checkpoint as a reusable
scaled-marginal certificate.
-/
noncomputable def paper_theorem1_iv_pareto_power_marginal_scaled_marginal_certificate
    (T : ℕ) (α : ℝ) :
    TopKScaledMarginalLimitCertificate
      (paretoPowerMarginalOracle T α) 1
      (paretoPowerMarginalScale α)
      (fun _ : ItemType T => (1 : ℝ)) :=
  paretoPowerMarginalScaledMarginalLimitCertificate T α

/--
Source Lemma D.4, fixed-rank Pareto finite-difference bridge.

This turns the paper-style value asymptotic and explicit scaled-drop limit for
one bottom-indexed rank into the per-rank marginal limit consumed by the
rank-by-rank Pareto source certificate.
-/
theorem paper_lemmaD4_pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop
    {μ : ℕ → ℕ → ℝ} {α C : ℝ} {r : ℕ}
    (hα : 1 < α) (hC : 0 < C)
    (hvalue :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q : ℕ => μ (q - r) q)
        (fun q : ℕ => C * ((q : ℝ) ^ (1 / α))))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((μ (q + 1 - r) (q + 1) - μ (q - r) q) /
              μ (q - r) q)))
        Filter.atTop (nhds (1 / α))) :
    Filter.Tendsto
      (fun q : ℕ =>
        (μ (q + 1 - r) (q + 1) - μ (q - r) q) /
          paretoPowerMarginalScale α q)
      Filter.atTop (nhds (C / α)) :=
  pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop hα hC hvalue hdrop

/--
Source Lemma D.4, fixed-rank Pareto finite-difference bridge with the
canonical gamma coefficient from the cited order-statistic facts.
-/
theorem paper_lemmaD4_pareto_rank_scaled_limit_of_canonical_value_asymptotic_and_scaled_drop
    {μ : ℕ → ℕ → ℝ} {α : ℝ} {r : ℕ}
    (hα : 1 < α)
    (hvalue :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q : ℕ => μ (q - r) q)
        (fun q : ℕ =>
          (Real.Gamma ((r : ℝ) + 1 - 1 / α) /
              Real.Gamma ((r : ℝ) + 1)) *
            ((q : ℝ) ^ (1 / α))))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((μ (q + 1 - r) (q + 1) - μ (q - r) q) /
              μ (q - r) q)))
        Filter.atTop (nhds (1 / α))) :
    Filter.Tendsto
      (fun q : ℕ =>
        (μ (q + 1 - r) (q + 1) - μ (q - r) q) /
          paretoPowerMarginalScale α q)
      Filter.atTop (nhds (paretoRankMarginalCoeff α r)) :=
  pareto_rank_scaled_limit_of_canonical_value_asymptotic_and_scaled_drop
    hα hvalue hdrop

/--
Source Lemma D.4, exact gamma-ratio fixed-rank sequence scaled limit.

This verifies the rank-level asymptotic produced by the cited gamma-ratio
formula before the separate measure-theoretic step identifying actual Pareto
order-statistic means with this sequence.
-/
theorem paper_lemmaD4_pareto_rank_gamma_ratio_mean_scaled_limit
    {α : ℝ} (hα : 1 < α) (r : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        (paretoRankGammaRatioMean α r (q + 1) -
            paretoRankGammaRatioMean α r q) /
          paretoPowerMarginalScale α q)
      Filter.atTop (nhds (paretoRankMarginalCoeff α r)) :=
  paretoRankGammaRatioMean_scaled_limit hα r

/--
Source Theorem 1(iv), Pareto order-statistic marginal asymptotic as a reusable
scaled-marginal certificate.  This exposes the exact source obligation left by
Lemma D.4/equation (77) in the paper's bottom-indexed `μ_D` interface.
-/
noncomputable def
    paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_source
    (T : ℕ) {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (C : ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T μ) k
      (paretoPowerMarginalScale α)
      (fun _ : ItemType T => limitCoeff) :=
  C.toTopKScaledMarginalLimitCertificate

/--
Source Theorem 1(iv), Pareto order-statistic marginal asymptotic stated in
the standard `AsymptoticEquivalent` form expected from Lemma D.4/equation (77).
-/
noncomputable def
    paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_asymptotic_equivalent
    (T : ℕ) {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (hα : 1 < α) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => limitCoeff * paretoPowerMarginalScale α q)) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T μ) k
      (paretoPowerMarginalScale α)
      (fun _ : ItemType T => limitCoeff) :=
  (ParetoOrderStatisticScaledMarginalCertificate.ofConstMulScaleAsymptoticEquivalent
    hα hk hcoeff hmargin).toTopKScaledMarginalLimitCertificate

/--
Source Theorem 1(iv), finite fixed-rank Pareto marginal-sum form.  This is the
paper-facing seam for proving Lemma D.4 rank-by-rank and then summing over the
fixed top-`k` window after the eventual `k ≤ q` prefix.
-/
noncomputable def
    paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_finite_rank_sum_asymptotic_equivalent
    (T : ℕ) {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (hα : 1 < α) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          ∑ i : Fin k,
            (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q))
        (fun q : ℕ => limitCoeff * paretoPowerMarginalScale α q)) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T μ) k
      (paretoPowerMarginalScale α)
      (fun _ : ItemType T => limitCoeff) :=
  (ParetoOrderStatisticScaledMarginalCertificate.ofFiniteRankMarginalSumAsymptoticEquivalent
    hα hk hcoeff hmargin).toTopKScaledMarginalLimitCertificate

/--
Source Theorem 1(iv), per-rank scaled-limit form.  It reduces the remaining
Pareto order-statistic calculation to one scaled limit for each fixed rank in
`Fin k`, plus the finite coefficient sum.
-/
noncomputable def
    paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_finite_rank_scaled_limits
    (T : ℕ) {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (rankCoeff : Fin k → ℝ)
    (hα : 1 < α) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hcoeff_sum : (∑ i : Fin k, rankCoeff i) = limitCoeff)
    (hrank :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun q : ℕ =>
            (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q) /
              paretoPowerMarginalScale α q)
          Filter.atTop (nhds (rankCoeff i))) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T μ) k
      (paretoPowerMarginalScale α)
      (fun _ : ItemType T => limitCoeff) :=
  (ParetoOrderStatisticScaledMarginalCertificate.ofFiniteRankScaledLimits
    rankCoeff hα hk hcoeff hcoeff_sum hrank).toTopKScaledMarginalLimitCertificate

/--
Source Theorem 1(iv), Pareto-specialized per-rank scaled-limit form with the
canonical Lemma D.4 gamma coefficients.
-/
noncomputable def
    paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_pareto_rank_scaled_limits
    (T : ℕ) {μ : ℕ → ℕ → ℝ} {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k)
    (hrank :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun q : ℕ =>
            (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q) /
              paretoPowerMarginalScale α q)
          Filter.atTop (nhds (paretoRankMarginalCoeff α i.val))) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T μ) k
      (paretoPowerMarginalScale α)
      (fun _ : ItemType T =>
        ∑ i : Fin k, paretoRankMarginalCoeff α i.val) :=
  (ParetoOrderStatisticScaledMarginalCertificate.ofParetoRankScaledLimits
    hα hk hrank).toTopKScaledMarginalLimitCertificate

/--
Source Corollary 1 parameter algebra for the bounded branch.

Every `0 < γ < 1` can be written as `β/(β+1)` with `β > 0`.
-/
theorem paper_corollary1_bounded_beta_for_gamma_between_zero_and_one
    {γ : ℝ} (hγ_pos : 0 < γ) (hγ_lt_one : γ < 1) :
    0 < γ / (1 - γ) ∧ (γ / (1 - γ)) / (γ / (1 - γ) + 1) = γ := by
  have hden_pos : 0 < 1 - γ := by linarith
  have hden_ne : 1 - γ ≠ 0 := hden_pos.ne'
  constructor
  · exact div_pos hγ_pos hden_pos
  · field_simp [hden_ne]
    ring

/--
Source Corollary 1 parameter algebra for the Pareto branch.

Every `γ > 1` can be written as `α/(α-1)` with `α > 1`.
-/
theorem paper_corollary1_pareto_alpha_for_gamma_gt_one
    {γ : ℝ} (hγ_gt_one : 1 < γ) :
    1 < γ / (γ - 1) ∧
      (γ / (γ - 1)) / (γ / (γ - 1) - 1) = γ := by
  have hden_pos : 0 < γ - 1 := by linarith
  have hden_ne : γ - 1 ≠ 0 := hden_pos.ne'
  constructor
  · rw [lt_div_iff₀ hden_pos]
    linarith
  · field_simp [hden_ne]
    ring

/--
Source Corollary 1 parameter split.

For every `γ ≥ 0`, the exponent is covered by one of the source families:
finite-discrete (`γ = 0`), bounded (`0 < γ < 1` via `β/(β+1)`), exponential
(`γ = 1`), or Pareto (`γ > 1` via `α/(α-1)`).
-/
theorem paper_corollary1_gamma_parameter_cases
    (γ : ℝ) (hγ_nonneg : 0 ≤ γ) :
    γ = 0 ∨
      (∃ β : ℝ, 0 < β ∧ β / (β + 1) = γ) ∨
      γ = 1 ∨
      (∃ α : ℝ, 1 < α ∧ α / (α - 1) = γ) := by
  by_cases hzero : γ = 0
  · exact Or.inl hzero
  · have hγ_pos : 0 < γ := lt_of_le_of_ne hγ_nonneg (Ne.symm hzero)
    rcases lt_trichotomy γ 1 with hlt | heq | hgt
    · right
      left
      obtain ⟨hβ_pos, hβ_eq⟩ :=
        paper_corollary1_bounded_beta_for_gamma_between_zero_and_one
          hγ_pos hlt
      exact ⟨γ / (1 - γ), hβ_pos, hβ_eq⟩
    · right
      right
      left
      exact heq
    · right
      right
      right
      obtain ⟨hα_gt_one, hα_eq⟩ :=
        paper_corollary1_pareto_alpha_for_gamma_gt_one hgt
      exact ⟨γ / (γ - 1), hα_gt_one, hα_eq⟩

/--
Source Corollary 1, bounded-branch concrete power-marginal realization for
any exponent `0 < γ < 1`.
-/
theorem paper_corollary1_bounded_power_marginal_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {γ : ℝ}
    (hγ_pos : 0 < γ) (hγ_lt_one : γ < 1)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (boundedPowerMarginalOracle T (γ / (1 - γ))).toConsumptionModel
            likelihood 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ γ /
            ∑ i : ItemType T, (likelihood i) ^ γ)) := by
  obtain ⟨hβ_pos, hβ_eq⟩ :=
    paper_corollary1_bounded_beta_for_gamma_between_zero_and_one
      hγ_pos hγ_lt_one
  have hformula :=
    paper_theorem1_ii_bounded_power_marginal_sequence_formula
      likelihood (γ / (1 - γ)) hβ_pos hlike_pos seq
  intro t
  simpa [hβ_eq] using hformula t

/--
Source Corollary 1, Pareto-branch concrete power-marginal realization for any
exponent `γ > 1`.
-/
theorem paper_corollary1_pareto_power_marginal_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {γ : ℝ}
    (hγ_gt_one : 1 < γ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (paretoPowerMarginalOracle T (γ / (γ - 1))).toConsumptionModel
            likelihood 1)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ γ /
            ∑ i : ItemType T, (likelihood i) ^ γ)) := by
  obtain ⟨hα_gt_one, hα_eq⟩ :=
    paper_corollary1_pareto_alpha_for_gamma_gt_one hγ_gt_one
  have hformula :=
    paper_theorem1_iv_pareto_power_marginal_sequence_formula
      likelihood (γ / (γ - 1)) hα_gt_one hlike_pos seq
  intro t
  simpa [hα_eq] using hformula t

/--
Source Corollary 1, exponential top-`k` order-statistic realization for
`γ = 1`.
-/
theorem paper_corollary1_exponential_top_k_order_statistic_gamma_one_sequence_formula
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda)
    (hk_pos : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
            likelihood k)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 : ℝ))) :=
  paper_theorem1_iii_exponential_top_k_order_statistic_sequence_formula
    likelihood lambda k hlambda_pos hk_pos hlike_pos seq

/--
Source Corollary 1, exposed at the reusable top-`k` certificate seam.
-/
theorem paper_corollary1_any_gamma_attainable_of_certificate
    {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) (γ : ℝ)
    (_hγ_nonneg : 0 ≤ γ)
    (seq :
      OptimalAllocationSequence (fun _ => O.toConsumptionModel likelihood k))
    (hcert :
      TopKAsymptoticHomogeneityCertificate O likelihood k
        (gammaLikelihoodProfile likelihood γ)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood γ) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptotic_homogeneity

/--
Certificate boundary for source Proposition 4.

`Profile` is the continuous relaxed recommendation profile space on the sphere,
`gamma` is the paper's large-`n` objective `Γ`, and `uniformProfile` is the
uniform distribution on the sphere. The remaining source work is the
measure-theoretic proof that these fields hold from the sphere, cosine-distance
kernel, full-support user measure, and Laplace-principle argument.
-/
structure Proposition4ContinuousSphereCertificate (Profile : Type*) where
  gamma : Profile → ℝ
  uniformProfile : Profile
  uniformValue : ℝ
  uniform_gamma_eq : gamma uniformProfile = uniformValue
  uniformValue_le_gamma : ∀ α : Profile, uniformValue ≤ gamma α

namespace Proposition4ContinuousSphereCertificate

theorem uniform_minimizes {Profile : Type*}
    (C : Proposition4ContinuousSphereCertificate Profile) :
    ∀ α : Profile, C.gamma C.uniformProfile ≤ C.gamma α := by
  intro α
  rw [C.uniform_gamma_eq]
  exact C.uniformValue_le_gamma α

end Proposition4ContinuousSphereCertificate

/--
Source Proposition 4, conditional continuous-sphere endpoint: the uniform
profile minimizes the large-`n` relaxed objective once the source analytic
certificate has supplied the uniform value and universal lower bound.
-/
theorem paper_proposition4_continuous_sphere_uniform_minimizes
    {Profile : Type*} (C : Proposition4ContinuousSphereCertificate Profile) :
    ∀ α : Profile, C.gamma C.uniformProfile ≤ C.gamma α :=
  C.uniform_minimizes

/--
Source Theorem 2(i), decaying Bernoulli success probabilities with `α < 1`,
exposed at the reusable model-sequence certificate seam.
-/
theorem paper_theorem2_i_decaying_bernoulli_sequence_homogeneity_of_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (_hα_lt_one : α < 1)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α))
    (hcert :
      DecayingBernoulliTopOneHomogeneityCertificate
        likelihood c d α (uniformProfile T)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptotic_homogeneity

/--
Source Theorem 2(i), product-asymptotic proof seam for `α < 1`.

It is enough to prove that any `o(N)`-violating unweighted count gap makes the
top-one finite FOC impossible; the reusable FOC bridge then gives uniform
asymptotic homogeneity.
-/
theorem
    paper_theorem2_i_decaying_bernoulli_sequence_homogeneity_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (_hα_lt_one : α < 1)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α))
    (hcert :
      DecayingBernoulliTopOneSublinearFOCCertificate likelihood c d α
        (fun _ : ItemType T => (1 : ℝ)) (uniformProfile T)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 2(i), eventual product-asymptotic proof seam for `0 < α < 1`.

After the raw Bernoulli survival-product estimates prove eventual large-gap
marginal dominance beyond a fixed count floor, the finite count-divergence and
FOC bridges give uniform asymptotic homogeneity.
-/
theorem
    paper_theorem2_i_decaying_bernoulli_sequence_homogeneity_of_eventual_product_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (_hα_pos : 0 < α) (_hα_lt_one : α < 1)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α))
    (hcert :
      DecayingBernoulliTopOneEventualSublinearFOCCertificate likelihood c d α
        (fun _ : ItemType T => (1 : ℝ)) (uniformProfile T)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 2(i), `0 < α < 1` top-one branch from the remaining scalar
growth condition.

The finite product proof has been reduced to showing that the chosen sublinear
gap schedule makes `(ε_N N - 1) q_N` dominate the finite log-likelihood ratios.
-/
theorem
    paper_theorem2_i_decaying_bernoulli_sequence_homogeneity_of_subunit_growth_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (_hα_pos : 0 < α) (_hα_lt_one : α < 1)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α))
    (hcert :
      DecayingBernoulliTopOneSubunitGrowthCertificate likelihood c d α) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 2(i), closed `0 < α < 1` top-one branch under explicit
nondegenerate probability assumptions.

The concrete sublinear gap schedule
`ε_N = (N + 1)^((α - 1) / 2)` makes `(ε_N N - 1) q_N` diverge, closing the
paper's product-tail route for this regime.
-/
theorem
    paper_theorem2_i_decaying_bernoulli_top_one_subunit_sequence_uniform_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    (DecayingBernoulliTopOneSubunitGrowthCertificate.of_positive_subunit_error
      likelihood c d α hα_pos hα_lt_one hc hd hfirst hlike_pos).asymptoticHomogeneity

/--
Source Theorem 2(i), closed `α = 0` subcase.

At `α = 0`, the rank-decay success probabilities are constant across ranks,
so the top-one model is exactly the i.i.d. Bernoulli model from Corollary 3.
-/
theorem paper_theorem2_i_decaying_bernoulli_top_one_alpha_zero_sequence_uniform_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d : ℝ)
    (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d 0)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  classical
  let B : BernoulliSatisfactionModel T :=
    { likelihood := likelihood
      successProb := fun _ => c }
  have hmodel :
      decayingBernoulliTopOneConsumptionModel likelihood c d 0 =
        B.toConsumptionModel := by
    simpa [B] using
      decayingBernoulliTopOneConsumptionModel_alpha_zero_eq_bernoulli
        likelihood c d
  let seqB : OptimalAllocationSequence (fun _ => B.toConsumptionModel) :=
    { allocation := seq.allocation
      optimal := by
        intro N
        simpa [hmodel] using seq.optimal N }
  have hB :
      ConsumptionModel.AsymptoticHomogeneity
        (fun _ => B.toConsumptionModel) (uniformProfile T) :=
    iid_bernoulli_asymptotic_uniform_homogeneity B
      (by intro t; exact hc_pos)
      (by intro t; exact hc_lt_one)
      (by intro t; exact hlike_pos t)
      (by intro i j; rfl)
  have hconv := seqB.convergesToProfile_of_asymptoticHomogeneity hB
  simpa [seqB, OptimalAllocationSequence.toAllocationSequence] using hconv

/--
Source Theorem 2(ii), decaying Bernoulli success probabilities with `α = 1`,
exposed at the reusable model-sequence certificate seam.
-/
theorem paper_theorem2_ii_decaying_bernoulli_sequence_homogeneity_of_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (_hα_eq_one : α = 1)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α))
    (hcert :
      DecayingBernoulliTopOneHomogeneityCertificate
        likelihood c d α (gammaLikelihoodProfile likelihood (1 / (1 + c)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / (1 + c))) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptotic_homogeneity

/--
Source Theorem 2(ii), product-asymptotic proof seam for `α = 1`.

The remaining analytic obligation is an `o(N)` scaled-gap dominance statement
for weights `p_t^(1/(1+c))`.
-/
theorem
    paper_theorem2_ii_decaying_bernoulli_sequence_homogeneity_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (_hα_eq_one : α = 1)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α))
    (hcert :
      DecayingBernoulliTopOneSublinearFOCCertificate likelihood c d α
        (fun t : ItemType T => likelihood t ^ (1 / (1 + c)))
        (gammaLikelihoodProfile likelihood (1 / (1 + c)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / (1 + c))) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 2(ii), eventual product-asymptotic proof seam for `α = 1`.

This is the floor-aware product-certificate interface for weights
`p_t^(1/(1+c))`.
-/
theorem
    paper_theorem2_ii_decaying_bernoulli_sequence_homogeneity_of_eventual_product_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (_hα_eq_one : α = 1)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α))
    (hcert :
      DecayingBernoulliTopOneEventualSublinearFOCCertificate likelihood c d α
        (fun t : ItemType T => likelihood t ^ (1 / (1 + c)))
        (gammaLikelihoodProfile likelihood (1 / (1 + c)))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / (1 + c))) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 2(ii), `α = 1` branch from the harmonic-log product growth
certificate.

This packages the raw-order and reverse-order scalar growth obligations for
weights `p_t^(1/(1+c))` into the reusable eventual FOC bridge.
-/
theorem
    paper_theorem2_ii_decaying_bernoulli_sequence_homogeneity_of_alpha_one_growth_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d : ℝ)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d 1))
    (hcert :
      DecayingBernoulliTopOneAlphaOneGrowthCertificate likelihood c d) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / (1 + c))) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 2(ii), closed `α = 1` top-one branch under explicit
nondegenerate probability assumptions.

The concrete sublinear gap schedule `ε_N = (N + 1)^(-1/4)` makes both the
raw shifted-count term and the reverse-order correction term negligible.
-/
theorem
    paper_theorem2_ii_decaying_bernoulli_top_one_alpha_one_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d 1 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / (1 + c))) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    (DecayingBernoulliTopOneAlphaOneGrowthCertificate.of_quarter_error
      (T := T) likelihood (c := c) (d := d) hc hd hfirst hlike_pos).asymptoticHomogeneity

/--
Source Theorem 2(iii), decaying Bernoulli success probabilities with `α > 1`,
exposed at the reusable model-sequence certificate seam.
-/
theorem paper_theorem2_iii_decaying_bernoulli_sequence_homogeneity_of_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (_hα_gt_one : 1 < α)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α))
    (hcert :
      DecayingBernoulliTopOneHomogeneityCertificate
        likelihood c d α (gammaLikelihoodProfile likelihood (1 / α))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / α)) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptotic_homogeneity

/--
Source Theorem 2(iii), product-asymptotic proof seam for `α > 1`.

The remaining analytic obligation is an `o(N)` scaled-gap dominance statement
for weights `p_t^(1/α)`.
-/
theorem
    paper_theorem2_iii_decaying_bernoulli_sequence_homogeneity_of_sublinear_foc_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (_hα_gt_one : 1 < α)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α))
    (hcert :
      DecayingBernoulliTopOneSublinearFOCCertificate likelihood c d α
        (fun t : ItemType T => likelihood t ^ (1 / α))
        (gammaLikelihoodProfile likelihood (1 / α))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / α)) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 2(iii), eventual product-asymptotic proof seam for `α > 1`.

This is the floor-aware product-certificate interface for weights
`p_t^(1/α)`.
-/
theorem
    paper_theorem2_iii_decaying_bernoulli_sequence_homogeneity_of_eventual_product_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (_hα_gt_one : 1 < α)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α))
    (hcert :
      DecayingBernoulliTopOneEventualSublinearFOCCertificate likelihood c d α
        (fun t : ItemType T => likelihood t ^ (1 / α))
        (gammaLikelihoodProfile likelihood (1 / α))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / α)) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 2(iii), `α > 1` top-one branch from the superunit product
growth certificate.

The certificate separates the raw-order shifted-count growth obligation from
the reverse-order inverse-survival-product correction.
-/
theorem
    paper_theorem2_iii_decaying_bernoulli_sequence_homogeneity_of_superunit_growth_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (_hα_gt_one : 1 < α)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α))
    (hcert :
      DecayingBernoulliTopOneSuperunitGrowthCertificate likelihood c d α) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / α)) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 2(iii), closed `α > 1` top-one branch under explicit
nondegenerate probability assumptions.

The concrete sublinear gap schedule
`ε_N = (N + 1)^(-(α - 1)/(2 * (α + 1)))` makes both the raw shifted-count term
and the reverse-order inverse-survival correction negligible.
-/
theorem
    paper_theorem2_iii_decaying_bernoulli_top_one_superunit_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (hα_gt_one : 1 < α) (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / α)) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    (DecayingBernoulliTopOneSuperunitGrowthCertificate.of_superunit_error
      (T := T) likelihood (c := c) (d := d) (α := α)
      hα_gt_one hc hd hfirst hlike_pos).asymptoticHomogeneity

/--
Source Theorem 2(iv), all-consumed decaying Bernoulli success probabilities,
exposed at the reusable model-sequence certificate seam.
-/
theorem paper_theorem2_iv_decaying_bernoulli_all_consumed_sequence_homogeneity_of_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliAllConsumedConsumptionModel likelihood c d α))
    (hcert :
      DecayingBernoulliAllConsumedHomogeneityCertificate
        likelihood c d α (gammaLikelihoodProfile likelihood (1 / α))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / α)) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptotic_homogeneity

/--
Source Theorem 2(iv), positive-decay all-consumed branch, from the finite
pairwise-scaled-count seam produced by Lemma D.1 and the paper's asymptotics.
-/
theorem
    paper_theorem2_iv_decaying_bernoulli_all_consumed_sequence_homogeneity_of_pairwise_scaled_certificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (_hα_pos : 0 < α)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliAllConsumedConsumptionModel likelihood c d α))
    (hcert :
      DecayingBernoulliAllConsumedPairwiseScaledCertificate likelihood c d α) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / α)) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    hcert.asymptoticHomogeneity

/--
Source Theorem 2(iv), closed positive-parameter all-consumed branch.

This follows a simpler finite FOC route than the paper's sum-asymptotic proof:
for `α > 0`, every optimum has pairwise bounded scaled counts
`a_t / p_t^(1/α)`, which gives the paper's `1/α`-homogeneity limit.
-/
theorem
    paper_theorem2_iv_decaying_bernoulli_all_consumed_positive_alpha_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α c d : ℝ)
    (hα : 0 < α) (hc : 0 < c) (hd : 0 ≤ d)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliAllConsumedConsumptionModel likelihood c d α)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / α)) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    (decayingBernoulliAllConsumedPairwiseScaledCertificate_of_positive_parameters
      likelihood c d α hα hc hd hlike_pos).asymptoticHomogeneity

/--
Source Theorem 2(iv), closed positive-parameter all-consumed case for
`α = 1`. The finite FOC gives a uniform bound on `a_t / p_t`, and the
pairwise-scaled bridge gives Definition 2 convergence to `1`-homogeneity.
-/
theorem paper_theorem2_iv_decaying_bernoulli_all_consumed_alpha_one_sequence_homogeneity
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ => decayingBernoulliAllConsumedConsumptionModel likelihood c d 1)) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood 1) := by
  have hconv :=
    paper_theorem2_iv_decaying_bernoulli_all_consumed_sequence_homogeneity_of_pairwise_scaled_certificate
      likelihood 1 c d (by norm_num : (0 : ℝ) < 1) seq
      (decayingBernoulliAllConsumedPairwiseScaledCertificate_alpha_one
        likelihood c d hc hd hlike_pos)
  simpa using hconv

/--
Theorem 2 finite FOC seam for the rank-decay Bernoulli top-one objective.
-/
theorem paper_theorem2_decaying_bernoulli_top_one_first_order_condition
    {T : ℕ} (likelihood : ItemType T → ℝ) (α c d : ℝ) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt :
      (decayingBernoulliTopOneConsumptionModel likelihood c d α).IsOptimalAtTotal N a)
    (hne : src ≠ dst)
    (hcan : EconCSLib.Allocation.CanMoveOne a src) :
    likelihood dst *
        (decayingBernoulliSuccess c d α (a.count dst) *
          ∏ i ∈ Finset.range (a.count dst),
            (1 - decayingBernoulliSuccess c d α i)) ≤
      likelihood src *
        (decayingBernoulliSuccess c d α (a.count src - 1) *
          ∏ i ∈ Finset.range (a.count src - 1),
            (1 - decayingBernoulliSuccess c d α i)) := by
  have h :=
    ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (M := decayingBernoulliTopOneConsumptionModel likelihood c d α)
      N hopt hne hcan
  change
    (rankBernoulliTopOneConsumptionModel likelihood
        (decayingBernoulliSuccess c d α)).weightedForwardMarginal
        dst (a.count dst) ≤
      (rankBernoulliTopOneConsumptionModel likelihood
        (decayingBernoulliSuccess c d α)).weightedBackwardMarginal
        src (a.count src) at h
  rw [rankBernoulliTopOneConsumptionModel_weightedForwardMarginal,
    rankBernoulliTopOneConsumptionModel_weightedBackwardMarginal
      (hq := hcan)] at h
  exact h

/--
Theorem 2 finite FOC seam for the rank-decay Bernoulli all-consumed objective.
-/
theorem paper_theorem2_decaying_bernoulli_all_consumed_first_order_condition
    {T : ℕ} (likelihood : ItemType T → ℝ) (α c d : ℝ) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt :
      (decayingBernoulliAllConsumedConsumptionModel likelihood c d α).IsOptimalAtTotal
        N a)
    (hne : src ≠ dst)
    (hcan : EconCSLib.Allocation.CanMoveOne a src) :
    likelihood dst * decayingBernoulliSuccess c d α (a.count dst) ≤
      likelihood src * decayingBernoulliSuccess c d α (a.count src - 1) := by
  have h :=
    ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (M := decayingBernoulliAllConsumedConsumptionModel likelihood c d α)
      N hopt hne hcan
  change
    (rankBernoulliAllConsumedConsumptionModel likelihood
        (decayingBernoulliSuccess c d α)).weightedForwardMarginal
        dst (a.count dst) ≤
      (rankBernoulliAllConsumedConsumptionModel likelihood
        (decayingBernoulliSuccess c d α)).weightedBackwardMarginal
        src (a.count src) at h
  rw [rankBernoulliAllConsumedConsumptionModel_weightedForwardMarginal,
    rankBernoulliAllConsumedConsumptionModel_weightedBackwardMarginal
      (hq := hcan)] at h
  exact h

namespace BernoulliSatisfactionModel

/--
Bernoulli fixed-total optimizer existence.
-/
theorem paper_bernoulli_finite_optimum_exists
    {T : ℕ} [Nonempty (ItemType T)]
    (B : BernoulliSatisfactionModel T) (N : ℕ) :
    ∃ a : CountAllocation T, B.toConsumptionModel.IsOptimalAtTotal N a := by
  exact B.toConsumptionModel.exists_isOptimalAtTotal N

/--
Bernoulli specialization of the finite first-order condition.
-/
theorem paper_bernoulli_optimum_first_order_condition
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a) (hne : src ≠ dst)
    (hcan : EconCSLib.Allocation.CanMoveOne a src) :
    B.likelihood dst * B.successProb dst *
        (1 - B.successProb dst) ^ (a.count dst) ≤
      B.likelihood src * B.successProb src *
        (1 - B.successProb src) ^ (a.count src - 1) := by
  exact B.forwardMarginal_le_backwardMarginal_of_optimum N hopt hne hcan

/--
Finite i.i.d. Bernoulli equal-representation balance theorem.
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

/--
Source Corollary 3: common-success-probability Bernoulli conditional values
give asymptotic `0`-homogeneity even when type likelihoods vary.
-/
theorem paper_corollary3_iid_bernoulli_asymptotic_uniform_homogeneity
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t)
    (hprob_eq : ∀ i j : ItemType T, B.successProb i = B.successProb j) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (uniformProfile T) := by
  exact iid_bernoulli_asymptotic_uniform_homogeneity
    B hprob_pos hprob_lt_one hlike_pos hprob_eq

/--
Source Corollary 3 in Definition 2 sequence-limit form.
-/
theorem paper_corollary3_iid_bernoulli_sequence_uniform_homogeneity
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t)
    (hprob_eq : ∀ i j : ItemType T, B.successProb i = B.successProb j)
    (seq :
      OptimalAllocationSequence (fun _ => B.toConsumptionModel)) :
    seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    (paper_corollary3_iid_bernoulli_asymptotic_uniform_homogeneity
      B hprob_pos hprob_lt_one hlike_pos hprob_eq)

end BernoulliSatisfactionModel

/--
Uniform `[0,1]`, `k = 1` finite first-order condition.
-/
theorem paper_uniform_top_one_optimum_first_order_condition
    {T : ℕ} (likelihood : ItemType T → ℝ) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hne : src ≠ dst)
    (hcan : EconCSLib.Allocation.CanMoveOne a src) :
    likelihood dst *
        (1 / ((a.count dst + 1 : ℝ) * (a.count dst + 2 : ℝ))) ≤
      likelihood src *
        (1 / ((a.count src : ℝ) * (a.count src + 1 : ℝ))) := by
  exact UniformTopOne.forwardMarginal_le_backwardMarginal_of_optimum
    likelihood N hopt hne hcan

/--
Proposition 2 audit: the relaxed optimizer formula printed in the paper sums
to `N - T`, not `N`.

This exposes the normalization-shift caveat recorded in the README.
-/
theorem paper_proposition_2_printed_relaxed_optimizer_total_mismatch
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0) :
    ∑ t : ItemType T, uniformSqrtPrintedOptTarget likelihood N t =
      (N : ℝ) - T := by
  exact sum_uniformSqrtPrintedOptTarget likelihood N hnorm

/--
Proposition 2 audit: the corrected shifted relaxed optimizer used by the Lean
finite theorem has total `N`.
-/
theorem paper_proposition_2_corrected_relaxed_optimizer_total
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0) :
    ∑ t : ItemType T, uniformSqrtRealOptTarget likelihood N t =
      (N : ℝ) := by
  exact sum_uniformSqrtRealOptTarget likelihood N hnorm

/--
Proposition 2 square-root homogeneity bridge.
-/
theorem paper_uniform_sqrt_homogeneity_of_count_closeness
    {T : ℕ} (likelihood : ItemType T → ℝ) (a : CountAllocation T)
    {N : ℕ} {C : ℝ}
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0)
    (hN : EconCSLib.Allocation.total a = N) (hNpos : 0 < N)
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
  have ht := hclose t
  have hshare := sqrtLikelihoodProfile.targetShare_eq likelihood t hnorm
  rwa [← hshare] at ht

/--
Proposition 2 sharp finite-bound bridge.

This isolates the remaining paper Lemma D.5-style obligation.  If a finite
top-`k` optimum is known to be within `T + 1` of the square-root homogeneity
target in every coordinate, then the paper's sharp finite `(T+1)/N`
homogeneity conclusion follows immediately.
-/
theorem paper_proposition_2_uniform_top_k_sharp_finite_of_count_closeness
    {T : ℕ} (likelihood : ItemType T → ℝ) (N k : ℕ)
    (hNpos : 0 < N)
    (a : CountAllocation T)
    (hopt : (uniformTopKConsumptionModel likelihood k).IsOptimalAtTotal N a)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0)
    (hclose :
      ∀ t,
        |(a.count t : ℝ) -
          (N : ℝ) *
            (Real.sqrt (likelihood t) /
              ∑ i : ItemType T, Real.sqrt (likelihood i))| ≤
          (Fintype.card (ItemType T) : ℝ) + 1) :
    (sqrtLikelihoodProfile likelihood).Approx a
      (((Fintype.card (ItemType T) : ℝ) + 1) / (N : ℝ)) := by
  exact paper_uniform_sqrt_homogeneity_of_count_closeness
    likelihood a hnorm hopt.1 hNpos hclose

/--
Proposition 2 paper-route sharp finite-bound bridge.

The proof sketch applies Lemma D.5 to the displayed relaxed optimizer.  Lean
tracks separately that the displayed optimizer has total `N - T`, but this
bridge records the exact implication the paper uses: coordinate closeness within
`T` of the displayed optimizer implies the paper's finite `(T+1)/N`
homogeneity conclusion.
-/
theorem paper_proposition_2_uniform_top_k_sharp_finite_of_printed_optimizer_closeness
    {T : ℕ} (likelihood : ItemType T → ℝ) (N k : ℕ)
    (hNpos : 0 < N)
    (a : CountAllocation T)
    (hopt : (uniformTopKConsumptionModel likelihood k).IsOptimalAtTotal N a)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0)
    (hclose_printed :
      ∀ t,
        |(a.count t : ℝ) - uniformSqrtPrintedOptTarget likelihood N t| ≤
          (Fintype.card (ItemType T) : ℝ)) :
    (sqrtLikelihoodProfile likelihood).Approx a
      (((Fintype.card (ItemType T) : ℝ) + 1) / (N : ℝ)) := by
  refine paper_proposition_2_uniform_top_k_sharp_finite_of_count_closeness
    likelihood N k hNpos a hopt hnorm ?_
  intro t
  have ht := hclose_printed t
  rw [abs_le] at ht ⊢
  constructor
  · unfold uniformSqrtPrintedOptTarget uniformSqrtTarget at ht
    linarith
  · unfold uniformSqrtPrintedOptTarget uniformSqrtTarget at ht
    linarith

/--
Source Proposition 2 finite `k = 1` analogue for the uniform top-one objective.

For any slate size `N` and positive number of types `T`, every optimal
allocation for identical uniform item values is approximately `1/2`-homogeneous
with finite rounding error `(2T + 2) / N`.

This is intentionally not named as the full source Proposition 2: the paper
allows all `k ≤ (m / ∑ᵢ √pᵢ) n - m - 1` and proves error `(m+1)/n`.
-/
theorem paper_proposition_2_uniform_top_one_finite_analogue {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hNpos : 0 < N)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (a : CountAllocation T)
    (h_interior : ∀ t, 1 ≤ uniformSqrtShiftedTarget likelihood N t)
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a) :
    (sqrtLikelihoodProfile likelihood).Approx a
      ((2 * (Fintype.card (ItemType T) : ℝ) + 2) / (N : ℝ)) := by
  have hnorm : ∑ i : ItemType T, Real.sqrt (likelihood i) ≠ 0 := by
    have hsum : 0 < ∑ i : ItemType T, likelihood i := by
      apply Finset.sum_pos
      · intro i _
        exact hlike_pos i
      · exact Finset.univ_nonempty
    exact sqrtLikelihoodProfile_normalizer_ne_zero likelihood hsum (fun i => le_of_lt (hlike_pos i))
  let lower := uniformSqrtLowerAnchor likelihood N
  let upper := uniformSqrtUpperAnchor likelihood N
  have horder : ∀ t, lower.count t ≤ upper.count t := by
    intro t
    unfold lower upper uniformSqrtLowerAnchor uniformSqrtUpperAnchor floorCountAnchor
    dsimp only
    have h1 : 1 ≤ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ := by
      exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (h_interior t))
    exact Nat.sub_le _ _
  have hcert : UniformTopOne.StrictRoundingExchangeCertificateBetween likelihood lower upper := by
    apply UniformTopOne.strictRoundingExchangeCertificateBetween_of_shifted_target likelihood lower upper (uniformSqrtScale likelihood N) (uniformSqrtShiftedTarget likelihood N)
    · unfold uniformSqrtScale
      have hden : (N + T : ℝ) ^ 2 > 0 := by positivity
      have hnum : 0 < (∑ i, Real.sqrt (likelihood i)) ^ 2 := by positivity
      positivity
    · intro t
      exact likelihood_eq_scale_mul_shiftedTarget_sq likelihood N t (fun i => le_of_lt (hlike_pos i)) hnorm
    · intro t
      exact uniformSqrtShiftedTarget_nonneg likelihood N t
    · intro t
      exact uniformSqrtUpperAnchor_shift_le likelihood N t
    · intro t _
      exact uniformSqrtLowerAnchor_le_shift likelihood N t h_interior
  have hno := UniformTopOne.noRoundingCrossingBetween_of_strictExchangeCertificate likelihood N hopt (fun t => le_of_lt (hlike_pos t)) horder hcert
  have h_total_lower : EconCSLib.Allocation.total lower ≤ N := by
    exact_mod_cast total_uniformSqrtLowerAnchor_le_N likelihood N hnorm h_interior
  have h_total_upper : EconCSLib.Allocation.total upper ≤ N + T := by
    exact_mod_cast total_uniformSqrtUpperAnchor_le likelihood N hnorm
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  have h_m : Fintype.card (ItemType T) = T := Fintype.card_fin T
  have h_total_a : EconCSLib.Allocation.total a = N := hopt.1
  have hNlt : N < EconCSLib.Allocation.total lower + Fintype.card (ItemType T) + 1 := by
    rw [h_m]
    by_cases h_int : ∀ t, uniformSqrtShiftedTarget likelihood N t = ⌊uniformSqrtShiftedTarget likelihood N t⌋₊
    · have heq := total_uniformSqrtLowerAnchor_eq_N_of_integers likelihood N hnorm h_interior h_int
      have hN_eq : (N : ℝ) = (EconCSLib.Allocation.total lower : ℝ) := heq.symm
      exact_mod_cast (by linarith : (N : ℝ) < (EconCSLib.Allocation.total lower : ℝ) + (T : ℝ) + 1)
    · push Not at h_int
      have hgt := total_uniformSqrtLowerAnchor_gt_N_sub_T_refined likelihood N hnorm h_interior h_int
      exact_mod_cast (by linarith : (N : ℝ) < (EconCSLib.Allocation.total lower : ℝ) + (T : ℝ) + 1)
  have hUlt : EconCSLib.Allocation.total upper < N + Fintype.card (ItemType T) + 1 := by
    rw [h_m]
    exact_mod_cast (by omega : EconCSLib.Allocation.total upper < N + T + 1)
  apply GammaHomogeneityProfile.approx_of_count_abs_error
  · exact h_total_a
  · exact hNpos
  intro t
  have h_share := GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero (sqrtLikelihoodProfile likelihood) t hnorm
  have h_target : (N : ℝ) * (sqrtLikelihoodProfile likelihood).targetShare t = uniformSqrtTarget likelihood N t := by
    unfold sqrtLikelihoodProfile uniformSqrtTarget GammaHomogeneityProfile.normalizer at *
    dsimp only at h_share
    rw [h_share]
  rw [h_target]
  have h_close := UniformRounding.count_close_of_no_rounding_crossing_between a lower upper h_total_a rfl rfl hNlt hUlt horder hno t
  have h_close_lower := uniformSqrtLowerAnchor_abs_close likelihood N t hnorm h_interior
  have h_close_upper := uniformSqrtUpperAnchor_abs_close likelihood N t hnorm
  rw [abs_lt] at h_close_lower h_close_upper
  rw [h_m] at h_close
  have h_l1 : (lower.count t : ℝ) < (a.count t : ℝ) + (T : ℝ) + 1 := by exact_mod_cast h_close.1
  have h_l2 : (a.count t : ℝ) < (upper.count t : ℝ) + (T : ℝ) + 1 := by exact_mod_cast h_close.2
  rw [abs_le]
  constructor
  · calc
      -(2 * (Fintype.card (ItemType T) : ℝ) + 2) = -(2 * (T : ℝ) + 2) := by rw [h_m]
      _ = -((T : ℝ) + 1) - ((T : ℝ) + 1) := by ring
      _ ≤ ((lower.count t : ℝ) - uniformSqrtTarget likelihood N t) - ((T : ℝ) + 1) := by linarith
      _ = (lower.count t : ℝ) - ((T : ℝ) + 1) - uniformSqrtTarget likelihood N t := by ring
      _ ≤ (a.count t : ℝ) - uniformSqrtTarget likelihood N t := by linarith
  · calc
      (a.count t : ℝ) - uniformSqrtTarget likelihood N t
        ≤ (upper.count t : ℝ) + (T : ℝ) + 1 - uniformSqrtTarget likelihood N t := by linarith
      _ = ((upper.count t : ℝ) - uniformSqrtTarget likelihood N t) + ((T : ℝ) + 1) := by ring
      _ ≤ ((T : ℝ) + 1) + ((T : ℝ) + 1) := by linarith
      _ = 2 * (T : ℝ) + 2 := by ring
      _ = 2 * (Fintype.card (ItemType T) : ℝ) + 2 := by rw [h_m]

/--
Source Proposition 2 all-eligible-`k` finite uniform theorem, up to the current
rounding constant.

For the exact uniform top-`k` order-statistic objective, if every square-root
real optimum coordinate is in the tail region (`k + 1` or larger after the
standard shift), every finite optimum is approximately `1/2`-homogeneous.

The paper states the sharper error `(T + 1) / N`; the current finite rounding
layer proves `(2T + 2) / N`.
-/
theorem paper_proposition_2_uniform_top_k_finite_analogue {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N k : ℕ)
    (hNpos : 0 < N)
    (hkpos : 0 < k)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (a : CountAllocation T)
    (hk_eligible :
      ∀ t, (k + 1 : ℝ) ≤ uniformSqrtShiftedTarget likelihood N t)
    (hopt : (uniformTopKConsumptionModel likelihood k).IsOptimalAtTotal N a) :
    (sqrtLikelihoodProfile likelihood).Approx a
      ((2 * (Fintype.card (ItemType T) : ℝ) + 2) / (N : ℝ)) := by
  have h_interior : ∀ t, 1 ≤ uniformSqrtShiftedTarget likelihood N t := by
    intro t
    have hk_nonneg : (0 : ℝ) ≤ k := by exact_mod_cast Nat.zero_le k
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
    exact le_trans hk1 (hk_eligible t)
  have hnorm : ∑ i : ItemType T, Real.sqrt (likelihood i) ≠ 0 := by
    have hsum : 0 < ∑ i : ItemType T, likelihood i := by
      apply Finset.sum_pos
      · intro i _
        exact hlike_pos i
      · exact Finset.univ_nonempty
    exact sqrtLikelihoodProfile_normalizer_ne_zero likelihood hsum (fun i => le_of_lt (hlike_pos i))
  let lower := uniformSqrtLowerAnchor likelihood N
  let upper := uniformSqrtUpperAnchor likelihood N
  have horder : ∀ t, lower.count t ≤ upper.count t := by
    intro t
    unfold lower upper uniformSqrtLowerAnchor uniformSqrtUpperAnchor floorCountAnchor
    dsimp only
    have h1 : 1 ≤ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ := by
      exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (h_interior t))
    exact Nat.sub_le _ _
  have hupper_tail : ∀ t, k ≤ upper.count t := by
    intro t
    unfold upper uniformSqrtUpperAnchor floorCountAnchor
    dsimp only
    have hf : k + 1 ≤ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ := by
      apply Nat.le_floor
      exact_mod_cast hk_eligible t
    exact le_trans (Nat.le_succ k) hf
  have hlower_tail : ∀ t, k ≤ lower.count t := by
    intro t
    unfold lower uniformSqrtLowerAnchor
    dsimp only
    have hf : k + 1 ≤ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ := by
      apply Nat.le_floor
      exact_mod_cast hk_eligible t
    omega
  have hcert :
      (uniformTopKConsumptionModel likelihood k).StrictRoundingExchangeCertificateBetween
        lower upper := by
    apply UniformTopK.strictRoundingExchangeCertificateBetween_of_shifted_target
      likelihood k lower upper (uniformSqrtScale likelihood N)
      (uniformSqrtShiftedTarget likelihood N)
    · exact hkpos
    · unfold uniformSqrtScale
      have hden : (N + T : ℝ) ^ 2 > 0 := by positivity
      have hnum : 0 < (∑ i, Real.sqrt (likelihood i)) ^ 2 := by positivity
      positivity
    · intro t
      exact likelihood_eq_scale_mul_shiftedTarget_sq likelihood N t (fun i => le_of_lt (hlike_pos i)) hnorm
    · intro t
      exact uniformSqrtShiftedTarget_nonneg likelihood N t
    · exact hupper_tail
    · exact hlower_tail
    · intro t
      exact uniformSqrtUpperAnchor_shift_le likelihood N t
    · intro t _
      exact uniformSqrtLowerAnchor_le_shift likelihood N t h_interior
  have hno :=
    ConsumptionModel.noRoundingCrossingBetween_of_strictExchangeCertificate
      (M := uniformTopKConsumptionModel likelihood k) (N := N)
      (a := a) (lower := lower) (upper := upper) hopt
      (uniformTopKConsumptionModel_has_diminishing_returns likelihood k)
      (fun t => le_of_lt (hlike_pos t)) horder hcert
  have h_total_lower : EconCSLib.Allocation.total lower ≤ N := by
    exact_mod_cast total_uniformSqrtLowerAnchor_le_N likelihood N hnorm h_interior
  have h_total_upper : EconCSLib.Allocation.total upper ≤ N + T := by
    exact_mod_cast total_uniformSqrtUpperAnchor_le likelihood N hnorm
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  have h_m : Fintype.card (ItemType T) = T := Fintype.card_fin T
  have h_total_a : EconCSLib.Allocation.total a = N := hopt.1
  have hNlt : N < EconCSLib.Allocation.total lower + Fintype.card (ItemType T) + 1 := by
    rw [h_m]
    by_cases h_int : ∀ t, uniformSqrtShiftedTarget likelihood N t = ⌊uniformSqrtShiftedTarget likelihood N t⌋₊
    · have heq := total_uniformSqrtLowerAnchor_eq_N_of_integers likelihood N hnorm h_interior h_int
      have hN_eq : (N : ℝ) = (EconCSLib.Allocation.total lower : ℝ) := heq.symm
      exact_mod_cast (by linarith : (N : ℝ) < (EconCSLib.Allocation.total lower : ℝ) + (T : ℝ) + 1)
    · push Not at h_int
      have hgt := total_uniformSqrtLowerAnchor_gt_N_sub_T_refined likelihood N hnorm h_interior h_int
      exact_mod_cast (by linarith : (N : ℝ) < (EconCSLib.Allocation.total lower : ℝ) + (T : ℝ) + 1)
  have hUlt : EconCSLib.Allocation.total upper < N + Fintype.card (ItemType T) + 1 := by
    rw [h_m]
    exact_mod_cast (by omega : EconCSLib.Allocation.total upper < N + T + 1)
  apply GammaHomogeneityProfile.approx_of_count_abs_error
  · exact h_total_a
  · exact hNpos
  intro t
  have h_share := GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero (sqrtLikelihoodProfile likelihood) t hnorm
  have h_target : (N : ℝ) * (sqrtLikelihoodProfile likelihood).targetShare t = uniformSqrtTarget likelihood N t := by
    unfold sqrtLikelihoodProfile uniformSqrtTarget GammaHomogeneityProfile.normalizer at *
    dsimp only at h_share
    rw [h_share]
  rw [h_target]
  have h_close := UniformRounding.count_close_of_no_rounding_crossing_between a lower upper h_total_a rfl rfl hNlt hUlt horder hno t
  have h_close_lower := uniformSqrtLowerAnchor_abs_close likelihood N t hnorm h_interior
  have h_close_upper := uniformSqrtUpperAnchor_abs_close likelihood N t hnorm
  rw [abs_lt] at h_close_lower h_close_upper
  rw [h_m] at h_close
  have h_l1 : (lower.count t : ℝ) < (a.count t : ℝ) + (T : ℝ) + 1 := by exact_mod_cast h_close.1
  have h_l2 : (a.count t : ℝ) < (upper.count t : ℝ) + (T : ℝ) + 1 := by exact_mod_cast h_close.2
  rw [abs_le]
  constructor
  · calc
      -(2 * (Fintype.card (ItemType T) : ℝ) + 2) = -(2 * (T : ℝ) + 2) := by rw [h_m]
      _ = -((T : ℝ) + 1) - ((T : ℝ) + 1) := by ring
      _ ≤ ((lower.count t : ℝ) - uniformSqrtTarget likelihood N t) - ((T : ℝ) + 1) := by linarith
      _ = (lower.count t : ℝ) - ((T : ℝ) + 1) - uniformSqrtTarget likelihood N t := by ring
      _ ≤ (a.count t : ℝ) - uniformSqrtTarget likelihood N t := by linarith
  · calc
      (a.count t : ℝ) - uniformSqrtTarget likelihood N t
        ≤ (upper.count t : ℝ) + (T : ℝ) + 1 - uniformSqrtTarget likelihood N t := by linarith
      _ = ((upper.count t : ℝ) - uniformSqrtTarget likelihood N t) + ((T : ℝ) + 1) := by ring
      _ ≤ ((T : ℝ) + 1) + ((T : ℝ) + 1) := by linarith
      _ = 2 * (T : ℝ) + 2 := by ring
      _ = 2 * (Fintype.card (ItemType T) : ℝ) + 2 := by rw [h_m]

/--
Proposition 2 top-`k` wrapper using the paper-style minimum square-root-share
eligibility condition.

The hypothesis corresponds to `k ≤ n * min_t sqrt(p_t)/∑ᵢ sqrt(p_i) - m - 1`.
The conclusion is still the current `(2T + 2) / N` rounding bound.
-/
theorem paper_proposition_2_uniform_top_k_finite_analogue_of_paper_bound
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N k : ℕ)
    (hNpos : 0 < N)
    (hkpos : 0 < k)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (a : CountAllocation T)
    (hbound :
      (k : ℝ) + 1 ≤ (N : ℝ) * uniformSqrtMinShare likelihood - T)
    (hopt : (uniformTopKConsumptionModel likelihood k).IsOptimalAtTotal N a) :
    (sqrtLikelihoodProfile likelihood).Approx a
      ((2 * (Fintype.card (ItemType T) : ℝ) + 2) / (N : ℝ)) := by
  have hnorm : ∑ i : ItemType T, Real.sqrt (likelihood i) ≠ 0 := by
    have hsum : 0 < ∑ i : ItemType T, likelihood i := by
      apply Finset.sum_pos
      · intro i _
        exact hlike_pos i
      · exact Finset.univ_nonempty
    exact sqrtLikelihoodProfile_normalizer_ne_zero likelihood hsum
      (fun i => le_of_lt (hlike_pos i))
  exact paper_proposition_2_uniform_top_k_finite_analogue
    likelihood N k hNpos hkpos hlike_pos a
    (uniformTopK_eligible_of_paper_min_share_bound likelihood N k hnorm hbound)
    hopt

/--
Asymptotic exact-rate consequence of the Proposition 2 top-`k` finite theorem
for any positive schedule `k(N)` satisfying the paper-style eligibility bound.
-/
theorem paper_proposition_2_uniform_top_k_asymptotic_of_paper_bound
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (kseq : ℕ → ℕ)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hkpos : ∀ N, 0 < N → 0 < kseq N)
    (hbound :
      ∀ N, 0 < N →
        (kseq N : ℝ) + 1 ≤
          (N : ℝ) * uniformSqrtMinShare likelihood - T) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun N => uniformTopKConsumptionModel likelihood (kseq N))
      (sqrtLikelihoodProfile likelihood) EconCSLib.Math.ExactInvRate := by
  let C : ℝ := 2 * (Fintype.card (ItemType T) : ℝ) + 2
  refine ⟨fun N => C / (N : ℝ), ?_, ?_⟩
  · have hC : 0 < C := by
      dsimp [C]
      positivity
    exact ⟨C, hC, fun N => rfl⟩
  · intro N a hN hopt
    exact paper_proposition_2_uniform_top_k_finite_analogue_of_paper_bound
      likelihood N (kseq N) hN (hkpos N hN) hlike_pos a
      (hbound N hN) hopt

/--
Source Proposition 2 asymptotic consequence in Definition 2 sequence-limit
form, for any admissible positive `k(N)` schedule.
-/
theorem paper_proposition_2_uniform_top_k_sequence_homogeneity_of_paper_bound
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (kseq : ℕ → ℕ)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hkpos : ∀ N, 0 < N → 0 < kseq N)
    (hbound :
      ∀ N, 0 < N →
        (kseq N : ℝ) + 1 ≤
          (N : ℝ) * uniformSqrtMinShare likelihood - T)
    (seq :
      OptimalAllocationSequence
        (fun N => uniformTopKConsumptionModel likelihood (kseq N))) :
    seq.toAllocationSequence.ConvergesToProfile
      (sqrtLikelihoodProfile likelihood) := by
  have htarget :
      ConsumptionModel.AsymptoticHomogeneity
        (fun N => uniformTopKConsumptionModel likelihood (kseq N))
        (sqrtLikelihoodProfile likelihood) :=
    ConsumptionModel.AsymptoticHomogeneityTarget.of_exactInvRate
      (paper_proposition_2_uniform_top_k_asymptotic_of_paper_bound
        likelihood kseq hlike_pos hkpos hbound)
  exact seq.convergesToProfile_of_asymptoticHomogeneity htarget

/--
Source Theorem 1(ii), fully formalized uniform bounded-support checkpoint.

The uniform `[0,1]` distribution has upper endpoint density exponent `β = 1`,
so the Theorem 1(ii) target exponent is `β / (β + 1) = 1/2`.  The exact
uniform top-`k` order-statistic algebra from Proposition 2 supplies the
sequence limit under the paper-style all-eligible `k(N)` bound.
-/
theorem paper_theorem1_ii_uniform_bounded_top_k_sequence_homogeneity_of_paper_bound
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (kseq : ℕ → ℕ)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hkpos : ∀ N, 0 < N → 0 < kseq N)
    (hbound :
      ∀ N, 0 < N →
        (kseq N : ℝ) + 1 ≤
          (N : ℝ) * uniformSqrtMinShare likelihood - T)
    (seq :
      OptimalAllocationSequence
        (fun N => uniformTopKConsumptionModel likelihood (kseq N))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / 2)) := by
  have hconv :=
    paper_proposition_2_uniform_top_k_sequence_homogeneity_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound seq
  have hnorm_sqrt :
      (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0 := by
    have hsum : 0 < ∑ i : ItemType T, likelihood i := by
      apply Finset.sum_pos
      · intro i _
        exact hlike_pos i
      · exact Finset.univ_nonempty
    exact sqrtLikelihoodProfile_normalizer_ne_zero likelihood hsum
      (fun i => le_of_lt (hlike_pos i))
  intro t
  have htarget :=
    paper_uniform_sqrt_profile_targetShare_eq_gamma_half likelihood t hnorm_sqrt
  simpa [htarget] using hconv t

/--
Source Theorem 1(ii), uniform bounded-support checkpoint in direct equation
(6) form.
-/
theorem paper_theorem1_ii_uniform_bounded_top_k_sequence_formula_of_paper_bound
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (kseq : ℕ → ℕ)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hkpos : ∀ N, 0 < N → 0 < kseq N)
    (hbound :
      ∀ N, 0 < N →
        (kseq N : ℝ) + 1 ≤
          (N : ℝ) * uniformSqrtMinShare likelihood - T)
    (seq :
      OptimalAllocationSequence
        (fun N => uniformTopKConsumptionModel likelihood (kseq N))) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 / 2 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 / 2 : ℝ))) := by
  have hconv :=
    paper_theorem1_ii_uniform_bounded_top_k_sequence_homogeneity_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound seq
  have hnorm_gamma :
      (∑ i : ItemType T, (likelihood i) ^ (1 / 2 : ℝ)) ≠ 0 := by
    have hsum_pos :
        0 < ∑ i : ItemType T, (likelihood i) ^ (1 / 2 : ℝ) := by
      apply Finset.sum_pos
      · intro i _
        exact Real.rpow_pos_of_pos (hlike_pos i) (1 / 2 : ℝ)
      · exact Finset.univ_nonempty
    exact ne_of_gt hsum_pos
  exact
    (paper_definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (1 / 2) hnorm_gamma).1 hconv

/--
Source Theorem 1(ii), uniform `[0,1]` order-statistic oracle checkpoint.

This is the same `γ = 1/2` sequence theorem as the closed-form uniform
objective, but stated at the Definition 3 order-statistic-mean oracle boundary.
-/
theorem paper_theorem1_ii_uniform_order_statistic_sequence_homogeneity_of_paper_bound
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (kseq : ℕ → ℕ)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hkpos : ∀ N, 0 < N → 0 < kseq N)
    (hbound :
      ∀ N, 0 < N →
        (kseq N : ℝ) + 1 ≤
          (N : ℝ) * uniformSqrtMinShare likelihood - T)
    (seq :
      OptimalAllocationSequence
        (fun N =>
          (TopKValueOracle.ofOrderStatisticMean T uniformAscendingOrderStatisticMean).toConsumptionModel
            likelihood (kseq N))) :
    seq.toAllocationSequence.ConvergesToProfile
      (gammaLikelihoodProfile likelihood (1 / 2)) := by
  let seqUniform :
      OptimalAllocationSequence
        (fun N => uniformTopKConsumptionModel likelihood (kseq N)) :=
    { allocation := seq.allocation
      optimal := by
        intro N
        simpa [paper_theorem1_ii_uniform_order_statistic_toConsumptionModel_eq]
          using seq.optimal N }
  have hconv :=
    paper_theorem1_ii_uniform_bounded_top_k_sequence_homogeneity_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound seqUniform
  simpa [seqUniform, OptimalAllocationSequence.toAllocationSequence,
    AllocationSequence.ConvergesToProfile, AllocationSequence.representation]
    using hconv

/--
Source Theorem 1(ii), uniform `[0,1]` order-statistic oracle checkpoint in
direct equation (6) form.
-/
theorem paper_theorem1_ii_uniform_order_statistic_sequence_formula_of_paper_bound
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (kseq : ℕ → ℕ)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hkpos : ∀ N, 0 < N → 0 < kseq N)
    (hbound :
      ∀ N, 0 < N →
        (kseq N : ℝ) + 1 ≤
          (N : ℝ) * uniformSqrtMinShare likelihood - T)
    (seq :
      OptimalAllocationSequence
        (fun N =>
          (TopKValueOracle.ofOrderStatisticMean T uniformAscendingOrderStatisticMean).toConsumptionModel
            likelihood (kseq N))) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (1 / 2 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (1 / 2 : ℝ))) := by
  have hconv :=
    paper_theorem1_ii_uniform_order_statistic_sequence_homogeneity_of_paper_bound
      likelihood kseq hlike_pos hkpos hbound seq
  have hnorm_gamma :
      (∑ i : ItemType T, (likelihood i) ^ (1 / 2 : ℝ)) ≠ 0 := by
    have hsum_pos :
        0 < ∑ i : ItemType T, (likelihood i) ^ (1 / 2 : ℝ) := by
      apply Finset.sum_pos
      · intro i _
        exact Real.rpow_pos_of_pos (hlike_pos i) (1 / 2 : ℝ)
      · exact Finset.univ_nonempty
    exact ne_of_gt hsum_pos
  exact
    (paper_definition2_gamma_homogeneity_sequence_iff
      seq.toAllocationSequence likelihood (1 / 2) hnorm_gamma).1 hconv

/--
Auxiliary heterogeneous-Bernoulli asymptotic interface.

This is not source Theorem 1.  In the paper, Theorem 1 is the i.i.d.
conditional-item-value theorem over finite discrete, bounded, exponential-tail,
and Pareto distributions.  This wrapper exposes the current Lean target for a
heterogeneous Bernoulli model.
-/
theorem paper_aux_heterogeneous_bernoulli_asymptotic_uniform_homogeneity
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : HeterogeneousBernoulliUniformHomogeneityCertificate B) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => B.toConsumptionModel) (uniformProfile T)
      EconCSLib.Math.ExactInvRate := by
  exact heterogeneous_bernoulli_asymptotic_uniform_homogeneity B hcert

/--
Auxiliary tail-index homogeneity interface.

This is not source Theorem 2.  In the paper, Theorem 2 is the decaying
Bernoulli-success-probability theorem.  This wrapper keeps the current abstract
tail-index target visible without assigning it a paper theorem number.
-/
theorem paper_aux_tail_index_homogeneity
    {T : ℕ} [NeZero T] (M : ConsumptionModel T) (α : ℝ)
    (hcert : TailIndexHomogeneityCertificate M α) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => M) (paretoProfile M.likelihood α)
      EconCSLib.Math.ExactInvRate := by
  exact homogeneity_of_tail_index M α hcert

/--
Auxiliary mixed Bernoulli-uniform homogeneity interface.

In a mixed model with Bernoulli and Uniform types, the Bernoulli types have 0-homogeneity
(share tends to zero) and the Uniform types split the remaining share with 1/2-homogeneity.

This is not source Theorem 3, which is the varying-success-probability Bernoulli
log-share theorem.
-/
theorem paper_aux_mixed_bernoulli_uniform_homogeneity
    (B : BernoulliSatisfactionModel 1) (Ulike : ItemType 1 → ℝ)
    (hcert : MixedBernoulliUniformHomogeneityCertificate B Ulike) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => mixedConsumptionModel B Ulike) (mixedTargetProfile (Ulike 0))
      EconCSLib.Math.ExactInvSqrtRate := by
  exact mixed_bernoulli_uniform_asymptotic_homogeneity B Ulike hcert

/--
Theorem 3 source target: varying Bernoulli success probabilities give limiting
representation proportional to `1 / log (1 / (1 - q_t))`.

This is the exact paper target, certificate-gated at the still-open
rounding/asymptotic proof layer.
-/
theorem paper_theorem3_varying_success_probability_log_share_of_certificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliLogShareCertificate B) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (theorem3LogShareProfile B) := by
  exact varying_bernoulli_log_share_asymptotic_of_certificate B hcert

/--
Theorem 3 source target from the finite pairwise-scaled-count seam.

This is closer to the paper proof: the remaining obligation is to derive the
pairwise scaled count bound from the Bernoulli log first-order inequalities.
-/
theorem paper_theorem3_varying_success_probability_log_share_of_pairwise_scaled_certificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliPairwiseScaledCertificate B) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (theorem3LogShareProfile B) := by
  exact varying_bernoulli_log_share_asymptotic_of_certificate B
    (varying_bernoulli_log_share_certificate_of_pairwise_scaled B hcert)

/--
Theorem 3 source target from the positive-count finite FOC seam.

This closes the algebra from the Bernoulli first-order condition to the
log-share limit under an explicit interior-optimum certificate. The remaining
paper proof work is to replace this strong all-positive-size certificate with
eventual interior plus finite-prefix handling.
-/
theorem paper_theorem3_varying_success_probability_log_share_of_positive_count_certificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliPositiveCountCertificate B) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (theorem3LogShareProfile B) := by
  exact varying_bernoulli_log_share_asymptotic_of_positive_count_certificate B hcert

/--
Theorem 3 source target from an eventual-interior finite FOC seam.

The finite prefix below the interior threshold is handled by the positive lower
bound on the log-share weights, so the certificate only needs positive counts
for sufficiently large optimal allocations.
-/
theorem paper_theorem3_varying_success_probability_log_share_of_eventual_positive_count_certificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliEventualPositiveCountCertificate B) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (theorem3LogShareProfile B) := by
  exact varying_bernoulli_log_share_asymptotic_of_eventual_positive_count_certificate B hcert

/--
Theorem 3 source target from pairwise large-count marginal dominance.

The only remaining obligation behind this wrapper is the analytic threshold
showing Bernoulli last-item marginals eventually fall below every first-item
marginal.
-/
theorem paper_theorem3_varying_success_probability_log_share_of_large_count_dominance_certificate
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hcert : VaryingBernoulliLargeCountDominanceCertificate B) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (theorem3LogShareProfile B) := by
  exact varying_bernoulli_log_share_asymptotic_of_large_count_dominance_certificate B hcert

/--
Source Theorem 3, varying Bernoulli success probabilities.

Under positive likelihoods and success probabilities in `(0,1)`, every
asymptotic sequence of finite Bernoulli optima has representation proportional
to `1 / log (1 / (1 - q_t))`.
-/
theorem paper_theorem3_varying_success_probability_log_share
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => B.toConsumptionModel) (theorem3LogShareProfile B) := by
  exact varying_bernoulli_log_share_asymptotic_of_primitive
    B hprob_pos hprob_lt_one hlike_pos

/--
Source Theorem 3 in Definition 2 sequence-limit form.
-/
theorem paper_theorem3_varying_success_probability_log_share_sequence
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t)
    (seq :
      OptimalAllocationSequence (fun _ => B.toConsumptionModel)) :
    seq.toAllocationSequence.ConvergesToProfile
      (theorem3LogShareProfile B) := by
  exact seq.convergesToProfile_of_asymptoticHomogeneity
    (paper_theorem3_varying_success_probability_log_share
      B hprob_pos hprob_lt_one hlike_pos)

/--
Source Theorem 3, all-consumed side.

If `best` maximizes the per-item Bernoulli value `p_t q_t`, then allocating
all `N` recommendations to `best` is optimal for the objective where all
recommended items are consumed.
-/
theorem paper_theorem3_all_consumed_argmax_optimum
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ) (best : ItemType T)
    (hbest :
      ∀ t, B.likelihood t * B.successProb t ≤
        B.likelihood best * B.successProb best) :
    (bernoulliAllConsumedModel B).IsOptimalAtTotal
      N (allOnTypeAllocation N best) := by
  exact bernoulli_all_consumed_argmax_isOptimalAtTotal B N best hbest

/--
Theorem 3 finite FOC seam: an optimum's log-scaled count for `src` is bounded
above by the log-scaled count for `dst` plus the finite likelihood offset.
-/
theorem paper_theorem3_log_scaled_count_pairwise_upper
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t)
    (src dst : ItemType T)
    (hsrc_pos : 0 < a.count src) :
    (a.count src : ℝ) * theorem3LogScale B src -
      (a.count dst : ℝ) * theorem3LogScale B dst ≤
      Real.log (B.likelihood src * B.successProb src) -
        Real.log (B.likelihood dst * B.successProb dst) +
        theorem3LogScale B src := by
  exact bernoulli_optimum_log_scaled_count_pairwise_upper
    B N hopt hprob_pos hprob_lt_one hlike_pos src dst hsrc_pos

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

end PRPKG24AccuracyDiversity
