import EconCSLib.Foundations.Math.Asymptotics
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

open Filter Topology
open scoped BigOperators

namespace EconCSLib
namespace Probability

noncomputable section

/-!
# Order-Statistic Certificate Interfaces

Reusable scaffolding for papers whose probability layer supplies expected
top-`k` values or marginal order-statistic asymptotics.  This file does not
prove distribution-specific bounded/exponential/Pareto integral asymptotics;
it gives those analytic results a stable target interface.

## Main declarations

- `TopKExpectationOracle`
- `TopKExpectationOracle.marginalTopK`
- `ascendingOrderStatistic`
- `ascendingOrderStatistic_measurable`
- `ascendingOrderStatistic_integrable_of_ae_bounds`
- `upperOrderStatistic_eq_endpoint_sub_reflectedAscending`
- `sampleTopKEndpointLoss_eq_reflectedBottomKSum`
- `sampleTopKSum_integrable_of_ae_bounds`
- `sampleTopKEndpointLoss_integrable_of_ae_bounds`
- `reflectedBottomKSum_integrable_of_ae_bounds`
- `ascendingOrderStatistic_eq_integral_rank_count_indicator`
- `reflectedBottomKSum_eq_integral_rank_count_indicator`
- `reflectedBottomKRankCountLayer_measurable_prod`
- `reflectedBottomKRankCountLayer_integrable_prod_of_ae_bounds`
- `expectedSampleTopKSum_eq_sum_expectedUpperOrderStatistic`
- `expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic`
- `expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic_of_le`
- `expectedSampleTopKEndpointLoss_eq_expectedReflectedBottomKSum`
- `orderStatisticTopKSumFromMean`
- `sampleOrderStatisticValue`
- `expectedSampleOrderStatisticMean`
- `expectedOrderStatisticMeanSeq`
- `topKSourceEndpointLoss_eq_reflectedTopKMeanSum`
- `TopKExpectationOracle.ScaledMarginalLimitCertificate`
- `TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_marginal_sandwich`
- `TopKExpectationOracle.ScaledMarginalLimitCertificate.marginal_lt_of_scaled_gap`
- `TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_same_count_marginal_lt_of_weight_gap`
-/

/-!
## Endpoint/reflection algebra

Several bounded-support order-statistic arguments work by reflecting source
draws around an upper endpoint `M`.  If each upper order-statistic mean is
`M` minus the corresponding reflected lower order-statistic mean, the top-`k`
source loss is exactly the sum of the reflected means.  The following small
interface keeps that finite algebra in the shared probability layer, leaving
distribution-specific integral identities to paper files.
-/

/--
Top-`k` loss from an upper endpoint, expressed using the `k` source
order-statistic means at a fixed sample count.
-/
def topKSourceEndpointLoss (M : ℝ) {k : ℕ} (sourceMean : Fin k → ℝ) : ℝ :=
  (k : ℝ) * M - ∑ i : Fin k, sourceMean i

/-- Sum of the reflected lower order-statistic means at a fixed sample count. -/
def reflectedTopKMeanSum {k : ℕ} (reflectedMean : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, reflectedMean i

/--
Reflection identity for bounded-support top-`k` order statistics: if every
source order-statistic mean is the upper endpoint minus its reflected mean,
then the total endpoint loss equals the reflected finite sum.
-/
theorem topKSourceEndpointLoss_eq_reflectedTopKMeanSum
    (M : ℝ) {k : ℕ}
    (sourceMean reflectedMean : Fin k → ℝ)
    (hsource : ∀ i : Fin k, sourceMean i = M - reflectedMean i) :
    topKSourceEndpointLoss M sourceMean =
      reflectedTopKMeanSum reflectedMean := by
  have hconst : (∑ _i : Fin k, M) = (k : ℝ) * M := by
    simp [Fintype.card_fin, nsmul_eq_mul, mul_comm]
  calc
    topKSourceEndpointLoss M sourceMean
        = (∑ _i : Fin k, M) - ∑ i : Fin k, sourceMean i := by
          rw [topKSourceEndpointLoss, hconst]
    _ = ∑ i : Fin k, (M - sourceMean i) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ i : Fin k, reflectedMean i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hsource i]
          ring
    _ = reflectedTopKMeanSum reflectedMean := by
          rw [reflectedTopKMeanSum]

/--
Sample-count-indexed wrapper for `topKSourceEndpointLoss`, matching common
paper notation where source means depend on the number of sampled items.
-/
def topKSourceEndpointLossSeq
    (M : ℝ) {k : ℕ} (sourceMean : Fin k → ℕ → ℝ) (a : ℕ) : ℝ :=
  topKSourceEndpointLoss M (fun i => sourceMean i a)

/-- Sample-count-indexed wrapper for `reflectedTopKMeanSum`. -/
def reflectedTopKMeanSumSeq
    {k : ℕ} (reflectedMean : Fin k → ℕ → ℝ) (a : ℕ) : ℝ :=
  reflectedTopKMeanSum (fun i => reflectedMean i a)

/-- Sequence form of `topKSourceEndpointLoss_eq_reflectedTopKMeanSum`. -/
theorem topKSourceEndpointLossSeq_eq_reflectedTopKMeanSumSeq
    (M : ℝ) {k : ℕ}
    (sourceMean reflectedMean : Fin k → ℕ → ℝ)
    (hsource : ∀ a (i : Fin k), sourceMean i a = M - reflectedMean i a)
    (a : ℕ) :
    topKSourceEndpointLossSeq M sourceMean a =
      reflectedTopKMeanSumSeq reflectedMean a :=
  topKSourceEndpointLoss_eq_reflectedTopKMeanSum M
    (fun i => sourceMean i a)
    (fun i => reflectedMean i a)
    (fun i => hsource a i)

/-!
## Tuple-level real order statistics

The declarations below are deliberately measure-free.  They provide the
pointwise sorted-sample layer that distribution-specific files can integrate
against.  The key bounded-support bridge is the reflection identity: the
`i`-th largest source sample is the endpoint minus the `i`-th smallest
reflected sample.
-/

/-- The `rank`-th smallest value in a finite real sample. -/
def ascendingOrderStatistic {n : ℕ} (sample : Fin n → ℝ) (rank : Fin n) : ℝ :=
  sample (Tuple.sort sample rank)

theorem ascendingOrderStatistic_mono {n : ℕ} (sample : Fin n → ℝ) :
    Monotone (ascendingOrderStatistic sample) := by
  simpa [ascendingOrderStatistic, Function.comp_def] using
    Tuple.monotone_sort sample

theorem ascendingOrderStatistic_filter_card_eq
    {n : ℕ} (sample : Fin n → ℝ) (x : ℝ) :
    (Finset.univ.filter
        (fun i : Fin n => ascendingOrderStatistic sample i ≤ x)).card =
      (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card := by
  classical
  rw [← Fintype.card_subtype
      (fun i : Fin n => ascendingOrderStatistic sample i ≤ x),
    ← Fintype.card_subtype (fun i : Fin n => sample i ≤ x)]
  refine Fintype.card_congr ?_
  exact
    { toFun := fun i =>
        ⟨Tuple.sort sample i.1, by
          simpa [ascendingOrderStatistic] using i.2⟩
      invFun := fun i =>
        ⟨(Tuple.sort sample).symm i.1, by
          simpa [ascendingOrderStatistic] using i.2⟩
      left_inv := by
        intro i
        exact Subtype.ext ((Tuple.sort sample).symm_apply_apply i.1)
      right_inv := by
        intro i
        exact Subtype.ext ((Tuple.sort sample).apply_symm_apply i.1) }

theorem ascendingOrderStatistic_le_iff_rank_lt_card_le
    {n : ℕ} (sample : Fin n → ℝ) (rank : Fin n) (x : ℝ) :
    ascendingOrderStatistic sample rank ≤ x ↔
      rank.val <
        (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card := by
  classical
  have hsorted :=
    Tuple.lt_card_le_iff_apply_le_of_monotone
      (j := rank) (f := ascendingOrderStatistic sample) (a := x)
      (ascendingOrderStatistic_mono sample)
  rw [← hsorted, ascendingOrderStatistic_filter_card_eq]

theorem coordinate_le_count_measurable {n : ℕ} (x : ℝ) :
    Measurable
      (fun sample : Fin n → ℝ =>
        (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card) := by
  classical
  have hsum :
      Measurable
        (fun sample : Fin n → ℝ =>
          ∑ i : Fin n, if sample i ≤ x then (1 : ℕ) else 0) := by
    exact Finset.measurable_sum Finset.univ
      (fun i _hi =>
        Measurable.ite
          (measurableSet_le (measurable_pi_apply i) measurable_const)
          measurable_const measurable_const)
  convert hsum using 1
  ext sample
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem ascendingOrderStatistic_measurable {n : ℕ} (rank : Fin n) :
    Measurable
      (fun sample : Fin n → ℝ => ascendingOrderStatistic sample rank) := by
  refine measurable_of_Iic ?_
  intro x
  have hset :
      (fun sample : Fin n → ℝ => ascendingOrderStatistic sample rank) ⁻¹'
          Set.Iic x =
        {sample : Fin n → ℝ |
          rank.val <
            (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card} := by
    ext sample
    simp [ascendingOrderStatistic_le_iff_rank_lt_card_le]
  rw [hset]
  exact measurableSet_lt measurable_const (coordinate_le_count_measurable x)

/-- The `rankFromTop`-th largest value in a finite real sample. -/
def upperOrderStatistic {n : ℕ} (sample : Fin n → ℝ)
    (rankFromTop : Fin n) : ℝ :=
  ascendingOrderStatistic sample rankFromTop.rev

theorem upperOrderStatistic_measurable {n : ℕ} (rankFromTop : Fin n) :
    Measurable
      (fun sample : Fin n → ℝ => upperOrderStatistic sample rankFromTop) :=
  ascendingOrderStatistic_measurable rankFromTop.rev

/-- Reflect a finite sample around an upper endpoint `M`. -/
def reflectedSample (M : ℝ) {n : ℕ} (sample : Fin n → ℝ) : Fin n → ℝ :=
  fun i => M - sample i

theorem reflectedSample_measurable (M : ℝ) {n : ℕ} :
    Measurable (fun sample : Fin n → ℝ => reflectedSample M sample) := by
  refine measurable_pi_lambda _ ?_
  intro i
  exact measurable_const.sub (measurable_pi_apply i)

theorem reflectedAscendingOrderStatistic_measurable
    (M : ℝ) {n : ℕ} (rank : Fin n) :
    Measurable
      (fun sample : Fin n → ℝ =>
        ascendingOrderStatistic (reflectedSample M sample) rank) :=
  (ascendingOrderStatistic_measurable rank).comp
    (reflectedSample_measurable M)

/--
Sorting the reflected sample in ascending order gives the endpoint minus the
source sample sorted in descending order.  This value-level statement is robust
to ties because `Tuple.unique_monotone` identifies the sorted value tuple.
-/
theorem ascendingOrderStatistic_reflectedSample
    (M : ℝ) {n : ℕ} (sample : Fin n → ℝ) (rank : Fin n) :
    ascendingOrderStatistic (reflectedSample M sample) rank =
      M - ascendingOrderStatistic sample rank.rev := by
  let σ : Equiv.Perm (Fin n) := Fin.revPerm.trans (Tuple.sort sample)
  have hmonoσ : Monotone ((reflectedSample M sample) ∘ σ) := by
    intro i j hij
    have hrev : j.rev ≤ i.rev := by
      rw [Fin.le_iff_val_le_val]
      simp only [Fin.val_rev]
      omega
    have hsort := ascendingOrderStatistic_mono sample hrev
    dsimp [ascendingOrderStatistic, reflectedSample, Function.comp_def, σ] at hsort ⊢
    linarith
  have hsorted :
      (reflectedSample M sample) ∘ σ =
        (reflectedSample M sample) ∘ Tuple.sort (reflectedSample M sample) :=
    Tuple.unique_monotone hmonoσ (Tuple.monotone_sort (reflectedSample M sample))
  have hrank := congr_fun hsorted rank
  simpa [ascendingOrderStatistic, reflectedSample, Function.comp_def, σ] using
    hrank.symm

/--
Bounded-support reflection for a single upper order statistic: the `i`-th
largest source value equals `M` minus the `i`-th smallest reflected value.
-/
theorem upperOrderStatistic_eq_endpoint_sub_reflectedAscending
    (M : ℝ) {n : ℕ} (sample : Fin n → ℝ) (rankFromTop : Fin n) :
    upperOrderStatistic sample rankFromTop =
      M - ascendingOrderStatistic (reflectedSample M sample) rankFromTop := by
  rw [ascendingOrderStatistic_reflectedSample]
  simp [upperOrderStatistic]

theorem ascendingOrderStatistic_le_of_forall_le
    {n : ℕ} {sample : Fin n → ℝ} {B : ℝ}
    (hB : ∀ i, sample i ≤ B) (rank : Fin n) :
    ascendingOrderStatistic sample rank ≤ B :=
  hB (Tuple.sort sample rank)

theorem le_ascendingOrderStatistic_of_forall_le
    {n : ℕ} {sample : Fin n → ℝ} {B : ℝ}
    (hB : ∀ i, B ≤ sample i) (rank : Fin n) :
    B ≤ ascendingOrderStatistic sample rank :=
  hB (Tuple.sort sample rank)

theorem upperOrderStatistic_le_of_forall_le
    {n : ℕ} {sample : Fin n → ℝ} {B : ℝ}
    (hB : ∀ i, sample i ≤ B) (rankFromTop : Fin n) :
    upperOrderStatistic sample rankFromTop ≤ B :=
  ascendingOrderStatistic_le_of_forall_le hB rankFromTop.rev

theorem le_upperOrderStatistic_of_forall_le
    {n : ℕ} {sample : Fin n → ℝ} {B : ℝ}
    (hB : ∀ i, B ≤ sample i) (rankFromTop : Fin n) :
    B ≤ upperOrderStatistic sample rankFromTop :=
  le_ascendingOrderStatistic_of_forall_le hB rankFromTop.rev

/-- Embed the first `min k n` top ranks into all sample ranks. -/
def topKRankEmbedding (k n : ℕ) (i : Fin (min k n)) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.isLt (min_le_right k n)⟩

/-- Pointwise top-`k` sum of the largest values in a finite real sample. -/
def sampleTopKSum {n : ℕ} (sample : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin (min k n),
    upperOrderStatistic sample (topKRankEmbedding k n i)

theorem sampleTopKSum_measurable {n : ℕ} (k : ℕ) :
    Measurable (fun sample : Fin n → ℝ => sampleTopKSum sample k) := by
  unfold sampleTopKSum
  exact Finset.measurable_sum Finset.univ
    (fun i _hi => upperOrderStatistic_measurable (topKRankEmbedding k n i))

theorem sampleTopKSum_le_of_forall_le
    {n : ℕ} {sample : Fin n → ℝ} {B : ℝ}
    (hB : ∀ i, sample i ≤ B) (k : ℕ) :
    sampleTopKSum sample k ≤ (min k n : ℝ) * B := by
  calc
    sampleTopKSum sample k
        ≤ ∑ _i : Fin (min k n), B := by
          unfold sampleTopKSum
          exact Finset.sum_le_sum
            (fun i _hi =>
              upperOrderStatistic_le_of_forall_le hB
                (topKRankEmbedding k n i))
    _ = (min k n : ℝ) * B := by
          simp [Fintype.card_fin, nsmul_eq_mul]

theorem sampleTopKSum_ge_of_forall_lower
    {n : ℕ} {sample : Fin n → ℝ} {L : ℝ}
    (hL : ∀ i, L ≤ sample i) (k : ℕ) :
    (min k n : ℝ) * L ≤ sampleTopKSum sample k := by
  calc
    (min k n : ℝ) * L = ∑ _i : Fin (min k n), L := by
          simp [Fintype.card_fin, nsmul_eq_mul]
    _ ≤ sampleTopKSum sample k := by
          unfold sampleTopKSum
          exact Finset.sum_le_sum
            (fun i _hi =>
              le_upperOrderStatistic_of_forall_le hL
                (topKRankEmbedding k n i))

theorem sampleTopKSum_nonneg_of_forall_nonneg
    {n : ℕ} {sample : Fin n → ℝ}
    (h_nonneg : ∀ i, 0 ≤ sample i) (k : ℕ) :
    0 ≤ sampleTopKSum sample k := by
  unfold sampleTopKSum
  exact Finset.sum_nonneg
    (fun i _hi =>
      le_upperOrderStatistic_of_forall_le h_nonneg
        (topKRankEmbedding k n i))

/-- Endpoint loss of the pointwise top-`k` sample sum. -/
def sampleTopKEndpointLoss (M : ℝ) {n : ℕ}
    (sample : Fin n → ℝ) (k : ℕ) : ℝ :=
  (min k n : ℝ) * M - sampleTopKSum sample k

theorem sampleTopKEndpointLoss_measurable (M : ℝ) {n : ℕ} (k : ℕ) :
    Measurable
      (fun sample : Fin n → ℝ => sampleTopKEndpointLoss M sample k) := by
  unfold sampleTopKEndpointLoss
  exact measurable_const.sub (sampleTopKSum_measurable k)

theorem sampleTopKEndpointLoss_nonneg_of_forall_le
    (M : ℝ) {n : ℕ} {sample : Fin n → ℝ}
    (hM : ∀ i, sample i ≤ M) (k : ℕ) :
    0 ≤ sampleTopKEndpointLoss M sample k := by
  unfold sampleTopKEndpointLoss
  exact sub_nonneg.mpr (sampleTopKSum_le_of_forall_le hM k)

theorem reflectedSample_nonneg_of_forall_le
    (M : ℝ) {n : ℕ} {sample : Fin n → ℝ}
    (hM : ∀ i, sample i ≤ M) (i : Fin n) :
    0 ≤ reflectedSample M sample i := by
  unfold reflectedSample
  exact sub_nonneg.mpr (hM i)

theorem reflectedSample_le_of_forall_lower
    (M L : ℝ) {n : ℕ} {sample : Fin n → ℝ}
    (hL : ∀ i, L ≤ sample i) (i : Fin n) :
    reflectedSample M sample i ≤ M - L := by
  unfold reflectedSample
  linarith [hL i]

/-- Sum of the first `min k n` reflected lower order statistics. -/
def reflectedBottomKSum (M : ℝ) {n : ℕ}
    (sample : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin (min k n),
    ascendingOrderStatistic (reflectedSample M sample) (topKRankEmbedding k n i)

theorem reflectedBottomKSum_measurable (M : ℝ) {n : ℕ} (k : ℕ) :
    Measurable
      (fun sample : Fin n → ℝ => reflectedBottomKSum M sample k) := by
  unfold reflectedBottomKSum
  exact Finset.measurable_sum Finset.univ
    (fun i _hi =>
      reflectedAscendingOrderStatistic_measurable
        M (topKRankEmbedding k n i))

theorem reflectedBottomKSum_nonneg_of_forall_le
    (M : ℝ) {n : ℕ} {sample : Fin n → ℝ}
    (hM : ∀ i, sample i ≤ M) (k : ℕ) :
    0 ≤ reflectedBottomKSum M sample k := by
  unfold reflectedBottomKSum
  exact Finset.sum_nonneg
    (fun i _hi =>
      le_ascendingOrderStatistic_of_forall_le
        (reflectedSample_nonneg_of_forall_le M hM)
        (topKRankEmbedding k n i))

theorem reflectedBottomKSum_le_of_forall_lower
    (M L : ℝ) {n : ℕ} {sample : Fin n → ℝ}
    (hL : ∀ i, L ≤ sample i) (k : ℕ) :
    reflectedBottomKSum M sample k ≤ (min k n : ℝ) * (M - L) := by
  calc
    reflectedBottomKSum M sample k
        ≤ ∑ _i : Fin (min k n), (M - L) := by
          unfold reflectedBottomKSum
          exact Finset.sum_le_sum
            (fun i _hi =>
              ascendingOrderStatistic_le_of_forall_le
                (reflectedSample_le_of_forall_lower M L hL)
                (topKRankEmbedding k n i))
    _ = (min k n : ℝ) * (M - L) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp

/--
Pointwise top-`k` reflection algebra: endpoint loss of the largest source
values equals the sum of the smallest reflected values.
-/
theorem sampleTopKEndpointLoss_eq_reflectedBottomKSum
    (M : ℝ) {n : ℕ} (sample : Fin n → ℝ) (k : ℕ) :
    sampleTopKEndpointLoss M sample k =
      reflectedBottomKSum M sample k := by
  simpa [sampleTopKEndpointLoss, sampleTopKSum, reflectedBottomKSum,
    topKSourceEndpointLoss, reflectedTopKMeanSum] using
    topKSourceEndpointLoss_eq_reflectedTopKMeanSum M
      (fun i : Fin (min k n) =>
        upperOrderStatistic sample (topKRankEmbedding k n i))
      (fun i : Fin (min k n) =>
        ascendingOrderStatistic (reflectedSample M sample)
          (topKRankEmbedding k n i))
      (fun i =>
        upperOrderStatistic_eq_endpoint_sub_reflectedAscending
          M sample (topKRankEmbedding k n i))

theorem sampleTopKEndpointLoss_le_of_forall_bounds
    (M L : ℝ) {n : ℕ} {sample : Fin n → ℝ}
    (hL : ∀ i, L ≤ sample i) (k : ℕ) :
    sampleTopKEndpointLoss M sample k ≤ (min k n : ℝ) * (M - L) := by
  rw [sampleTopKEndpointLoss_eq_reflectedBottomKSum]
  exact reflectedBottomKSum_le_of_forall_lower M L hL k

theorem ascendingOrderStatistic_integrable_of_ae_bounds
    (L U : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (rank : Fin n)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ U) :
    MeasureTheory.Integrable
      (fun sample : Fin n → ℝ => ascendingOrderStatistic sample rank) μ := by
  refine MeasureTheory.Integrable.of_mem_Icc L U
    (ascendingOrderStatistic_measurable rank).aemeasurable ?_
  filter_upwards [h_bounds] with sample hsample
  exact ⟨
    le_ascendingOrderStatistic_of_forall_le
      (fun i => (hsample i).1) rank,
    ascendingOrderStatistic_le_of_forall_le
      (fun i => (hsample i).2) rank⟩

theorem upperOrderStatistic_integrable_of_ae_bounds
    (L U : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (rankFromTop : Fin n)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ U) :
    MeasureTheory.Integrable
      (fun sample : Fin n → ℝ => upperOrderStatistic sample rankFromTop) μ :=
  ascendingOrderStatistic_integrable_of_ae_bounds
    L U μ rankFromTop.rev h_bounds

theorem reflectedAscendingOrderStatistic_integrable_of_ae_bounds
    (M L : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (rank : Fin n)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ M) :
    MeasureTheory.Integrable
      (fun sample : Fin n → ℝ =>
        ascendingOrderStatistic (reflectedSample M sample) rank) μ := by
  refine MeasureTheory.Integrable.of_mem_Icc 0 (M - L)
    (reflectedAscendingOrderStatistic_measurable M rank).aemeasurable ?_
  filter_upwards [h_bounds] with sample hsample
  exact ⟨
    le_ascendingOrderStatistic_of_forall_le
      (reflectedSample_nonneg_of_forall_le M
        (fun i => (hsample i).2)) rank,
    ascendingOrderStatistic_le_of_forall_le
      (reflectedSample_le_of_forall_lower M L
        (fun i => (hsample i).1)) rank⟩

theorem sampleTopKSum_integrable_of_ae_bounds
    (L U : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ U) :
    MeasureTheory.Integrable
      (fun sample : Fin n → ℝ => sampleTopKSum sample k) μ := by
  refine MeasureTheory.Integrable.of_mem_Icc
    ((min k n : ℝ) * L) ((min k n : ℝ) * U)
    (sampleTopKSum_measurable k).aemeasurable ?_
  filter_upwards [h_bounds] with sample hsample
  exact ⟨
    sampleTopKSum_ge_of_forall_lower
      (fun i => (hsample i).1) k,
    sampleTopKSum_le_of_forall_le
      (fun i => (hsample i).2) k⟩

theorem sampleTopKEndpointLoss_integrable_of_ae_bounds
    (M L : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ M) :
    MeasureTheory.Integrable
      (fun sample : Fin n → ℝ => sampleTopKEndpointLoss M sample k) μ := by
  refine MeasureTheory.Integrable.of_mem_Icc 0 ((min k n : ℝ) * (M - L))
    (sampleTopKEndpointLoss_measurable M k).aemeasurable ?_
  filter_upwards [h_bounds] with sample hsample
  exact ⟨
    sampleTopKEndpointLoss_nonneg_of_forall_le
      M (fun i => (hsample i).2) k,
    sampleTopKEndpointLoss_le_of_forall_bounds
      M L (fun i => (hsample i).1) k⟩

theorem reflectedBottomKSum_integrable_of_ae_bounds
    (M L : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ M) :
    MeasureTheory.Integrable
      (fun sample : Fin n → ℝ => reflectedBottomKSum M sample k) μ := by
  refine MeasureTheory.Integrable.of_mem_Icc 0 ((min k n : ℝ) * (M - L))
    (reflectedBottomKSum_measurable M k).aemeasurable ?_
  filter_upwards [h_bounds] with sample hsample
  exact ⟨
    reflectedBottomKSum_nonneg_of_forall_le
      M (fun i => (hsample i).2) k,
    reflectedBottomKSum_le_of_forall_lower
      M L (fun i => (hsample i).1) k⟩

theorem integral_Ioi_indicator_lt_eq
    (a : ℝ) (ha : 0 ≤ a) :
    ∫ x in Set.Ioi (0 : ℝ), (if x < a then (1 : ℝ) else 0) = a := by
  have hindicator :
      (fun x : ℝ => if x < a then (1 : ℝ) else 0) =
        (Set.Iio a).indicator (fun _x : ℝ => (1 : ℝ)) := by
    funext x
    by_cases hx : x < a <;> simp [hx]
  rw [hindicator, MeasureTheory.setIntegral_indicator measurableSet_Iio]
  have hset : Set.Ioi (0 : ℝ) ∩ Set.Iio a = Set.Ioo (0 : ℝ) a := by
    ext x
    simp [and_comm]
  rw [hset, MeasureTheory.setIntegral_const]
  simp [Real.volume_real_Ioo_of_le ha]

theorem thresholdIndicator_integrable_Ioi (a : ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => if x < a then (1 : ℝ) else 0)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hindicator :
      (fun x : ℝ => if x < a then (1 : ℝ) else 0) =
        (Set.Iio a).indicator (fun _x : ℝ => (1 : ℝ)) := by
    funext x
    by_cases hx : x < a <;> simp [hx]
  rw [hindicator]
  have hfinite :
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) (Set.Iio a) ≠ ⊤ := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iio]
    have hset : Set.Iio a ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) a := by
      ext x
      simp [and_comm]
    rw [hset, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  exact (MeasureTheory.integrableOn_const
    (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    (s := Set.Iio a) (C := (1 : ℝ)) hfinite).integrable_indicator
      measurableSet_Iio

theorem ascendingOrderStatistic_rank_count_le_iff
    {n : ℕ} (sample : Fin n → ℝ) (rank : Fin n) (x : ℝ) :
    (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card ≤ rank.val ↔
      x < ascendingOrderStatistic sample rank := by
  rw [← not_iff_not]
  push Not
  exact (ascendingOrderStatistic_le_iff_rank_lt_card_le sample rank x).symm

theorem ascendingOrderStatistic_rank_count_indicator_integrable
    {n : ℕ} (sample : Fin n → ℝ) (rank : Fin n) :
    MeasureTheory.Integrable
      (fun x : ℝ =>
        if (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card ≤ rank.val
        then (1 : ℝ) else 0)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine (thresholdIndicator_integrable_Ioi
    (ascendingOrderStatistic sample rank)).congr ?_
  filter_upwards with x
  have hiff := ascendingOrderStatistic_rank_count_le_iff sample rank x
  by_cases hcount :
      (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card ≤ rank.val
  · have hx : x < ascendingOrderStatistic sample rank := hiff.mp hcount
    simp [hcount, hx]
  · have hx : ¬ x < ascendingOrderStatistic sample rank := by
      intro hx
      exact hcount (hiff.mpr hx)
    simp [hcount, hx]

theorem ascendingOrderStatistic_eq_integral_rank_count_indicator
    {n : ℕ} (sample : Fin n → ℝ) (rank : Fin n)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    ascendingOrderStatistic sample rank =
      ∫ x in Set.Ioi (0 : ℝ),
        if (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card ≤ rank.val
        then (1 : ℝ) else 0 := by
  have hstat_nonneg : 0 ≤ ascendingOrderStatistic sample rank :=
    le_ascendingOrderStatistic_of_forall_le h_nonneg rank
  rw [← integral_Ioi_indicator_lt_eq
    (ascendingOrderStatistic sample rank) hstat_nonneg]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro x _hx
  have hiff := ascendingOrderStatistic_rank_count_le_iff sample rank x
  by_cases hcount :
      (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card ≤ rank.val
  · have hx : x < ascendingOrderStatistic sample rank := hiff.mp hcount
    simp [hcount, hx]
  · have hx : ¬ x < ascendingOrderStatistic sample rank := by
      intro hx
      exact hcount (hiff.mpr hx)
    simp [hcount, hx]

theorem reflectedBottomKSum_eq_integral_rank_count_indicator
    (M : ℝ) {n : ℕ} (sample : Fin n → ℝ) (k : ℕ)
    (hM : ∀ i, sample i ≤ M) :
    reflectedBottomKSum M sample k =
      ∫ x in Set.Ioi (0 : ℝ),
        ∑ i : Fin (min k n),
          if (Finset.univ.filter
              (fun j : Fin n => reflectedSample M sample j ≤ x)).card ≤
              (topKRankEmbedding k n i).val
          then (1 : ℝ) else 0 := by
  have h_nonneg : ∀ i : Fin n, 0 ≤ reflectedSample M sample i :=
    reflectedSample_nonneg_of_forall_le M hM
  calc
    reflectedBottomKSum M sample k =
        ∑ i : Fin (min k n),
          ∫ x in Set.Ioi (0 : ℝ),
            if (Finset.univ.filter
                (fun j : Fin n => reflectedSample M sample j ≤ x)).card ≤
                (topKRankEmbedding k n i).val
            then (1 : ℝ) else 0 := by
          unfold reflectedBottomKSum
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact ascendingOrderStatistic_eq_integral_rank_count_indicator
            (reflectedSample M sample) (topKRankEmbedding k n i) h_nonneg
    _ = ∫ x in Set.Ioi (0 : ℝ),
        ∑ i : Fin (min k n),
          if (Finset.univ.filter
              (fun j : Fin n => reflectedSample M sample j ≤ x)).card ≤
              (topKRankEmbedding k n i).val
          then (1 : ℝ) else 0 := by
          rw [MeasureTheory.integral_finset_sum]
          intro i _hi
          exact ascendingOrderStatistic_rank_count_indicator_integrable
            (reflectedSample M sample) (topKRankEmbedding k n i)

/--
Threshold-count layer whose positive-threshold integral recovers the reflected
bottom-`k` sum.  The event counts reflected coordinates below threshold `x`;
for rank `r`, the indicator is active exactly when the `r`th reflected order
statistic is above `x`.
-/
def reflectedBottomKRankCountLayer
    (M : ℝ) {n : ℕ} (k : ℕ) (sample : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin (min k n),
    if (Finset.univ.filter
        (fun j : Fin n => reflectedSample M sample j ≤ x)).card ≤
        (topKRankEmbedding k n i).val
    then (1 : ℝ) else 0

theorem reflectedBottomKRankCountLayer_nonneg
    (M : ℝ) {n : ℕ} (k : ℕ) (sample : Fin n → ℝ) (x : ℝ) :
    0 ≤ reflectedBottomKRankCountLayer M k sample x := by
  classical
  unfold reflectedBottomKRankCountLayer
  exact Finset.sum_nonneg (fun i _hi => by split <;> norm_num)

theorem reflectedBottomKRankCountLayer_le_card
    (M : ℝ) {n : ℕ} (k : ℕ) (sample : Fin n → ℝ) (x : ℝ) :
    reflectedBottomKRankCountLayer M k sample x ≤ (min k n : ℝ) := by
  classical
  unfold reflectedBottomKRankCountLayer
  calc
    (∑ i : Fin (min k n),
        if (Finset.univ.filter
            (fun j : Fin n => reflectedSample M sample j ≤ x)).card ≤
            (topKRankEmbedding k n i).val
        then (1 : ℝ) else 0)
        ≤ ∑ _i : Fin (min k n), (1 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          split <;> norm_num
    _ = (min k n : ℝ) := by simp

theorem reflectedCoordinate_le_threshold_count_measurable_prod
    (M : ℝ) {n : ℕ} :
    Measurable
      (fun z : (Fin n → ℝ) × ℝ =>
        (Finset.univ.filter
          (fun i : Fin n => reflectedSample M z.1 i ≤ z.2)).card) := by
  classical
  have hsum :
      Measurable
        (fun z : (Fin n → ℝ) × ℝ =>
          ∑ i : Fin n,
            if reflectedSample M z.1 i ≤ z.2 then (1 : ℕ) else 0) := by
    exact Finset.measurable_sum Finset.univ
      (fun i _hi =>
        Measurable.ite
          (measurableSet_le
            (measurable_const.sub
              ((measurable_pi_apply i).comp measurable_fst))
            measurable_snd)
          measurable_const measurable_const)
  convert hsum using 1
  ext z
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem reflectedRankCountIndicator_measurable_prod
    (M : ℝ) {n : ℕ} (rank : ℕ) :
    Measurable
      (fun z : (Fin n → ℝ) × ℝ =>
        if (Finset.univ.filter
            (fun i : Fin n => reflectedSample M z.1 i ≤ z.2)).card ≤ rank
        then (1 : ℝ) else 0) := by
  exact Measurable.ite
    (measurableSet_le
      (reflectedCoordinate_le_threshold_count_measurable_prod M)
      measurable_const)
    measurable_const measurable_const

theorem reflectedBottomKRankCountLayer_measurable_prod
    (M : ℝ) {n : ℕ} (k : ℕ) :
    Measurable
      (fun z : (Fin n → ℝ) × ℝ =>
        reflectedBottomKRankCountLayer M k z.1 z.2) := by
  unfold reflectedBottomKRankCountLayer
  exact Finset.measurable_sum Finset.univ
    (fun i _hi =>
      reflectedRankCountIndicator_measurable_prod
        M (topKRankEmbedding k n i).val)

theorem reflectedBottomKRankCountLayer_integrable_Ioi
    (M : ℝ) {n : ℕ} (k : ℕ) (sample : Fin n → ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => reflectedBottomKRankCountLayer M k sample x)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  unfold reflectedBottomKRankCountLayer
  exact MeasureTheory.integrable_finset_sum Finset.univ
    (fun i _hi =>
      ascendingOrderStatistic_rank_count_indicator_integrable
        (reflectedSample M sample) (topKRankEmbedding k n i))

theorem reflectedBottomKSum_eq_integral_rank_count_layer
    (M : ℝ) {n : ℕ} (sample : Fin n → ℝ) (k : ℕ)
    (hM : ∀ i, sample i ≤ M) :
    reflectedBottomKSum M sample k =
      ∫ x in Set.Ioi (0 : ℝ),
        reflectedBottomKRankCountLayer M k sample x := by
  simpa [reflectedBottomKRankCountLayer] using
    reflectedBottomKSum_eq_integral_rank_count_indicator M sample k hM

theorem reflectedBottomKRankCountLayer_integrable_prod_of_ae_bounds
    (M L : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ M) :
    MeasureTheory.Integrable
      (fun z : (Fin n → ℝ) × ℝ =>
        reflectedBottomKRankCountLayer M k z.1 z.2)
      (μ.prod (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
  let ν := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let f : (Fin n → ℝ) × ℝ → ℝ :=
    fun z => reflectedBottomKRankCountLayer M k z.1 z.2
  have hf_meas : Measurable f := by
    simpa [f] using reflectedBottomKRankCountLayer_measurable_prod (M := M) (n := n) k
  have hsections :
      ∀ᵐ sample ∂μ,
        MeasureTheory.Integrable (fun x : ℝ => f (sample, x)) ν := by
    filter_upwards with sample
    simpa [f, ν] using
      reflectedBottomKRankCountLayer_integrable_Ioi M k sample
  have hinner_eq :
      (fun sample : Fin n → ℝ => ∫ x, ‖f (sample, x)‖ ∂ν) =ᵐ[μ]
        fun sample : Fin n → ℝ => reflectedBottomKSum M sample k := by
    filter_upwards [h_bounds] with sample hsample
    have hnorm :
        ∫ x, ‖f (sample, x)‖ ∂ν =
          ∫ x, f (sample, x) ∂ν := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      have hnonneg : 0 ≤ f (sample, x) := by
        simpa [f] using reflectedBottomKRankCountLayer_nonneg M k sample x
      simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      ∫ x, ‖f (sample, x)‖ ∂ν =
          ∫ x, f (sample, x) ∂ν := hnorm
      _ =
          ∫ x in Set.Ioi (0 : ℝ),
            reflectedBottomKRankCountLayer M k sample x := by
            rfl
      _ = reflectedBottomKSum M sample k := by
            exact (reflectedBottomKSum_eq_integral_rank_count_layer
              M sample k (fun i => (hsample i).2)).symm
  have hinner_int :
      MeasureTheory.Integrable
        (fun sample : Fin n → ℝ => ∫ x, ‖f (sample, x)‖ ∂ν) μ := by
    exact (reflectedBottomKSum_integrable_of_ae_bounds M L μ k h_bounds).congr
      hinner_eq.symm
  have hf_int : MeasureTheory.Integrable f (μ.prod ν) := by
    exact (MeasureTheory.integrable_prod_iff hf_meas.aestronglyMeasurable).2
      ⟨hsections, hinner_int⟩
  simpa [ν, f] using hf_int

/-!
## Expected finite-sample order statistics

These declarations are still distribution-agnostic: the sample law is any
probability measure on finite real tuples.  Distribution files can instantiate
the measure as an iid product law and then prove measurability/integrability or
closed forms separately.
-/

/-- Expected ascending order statistic under a finite-sample law. -/
def expectedAscendingOrderStatistic {n : ℕ}
    (μ : MeasureTheory.Measure (Fin n → ℝ)) (rank : Fin n) : ℝ :=
  ∫ sample, ascendingOrderStatistic sample rank ∂μ

/-- Expected upper order statistic under a finite-sample law. -/
def expectedUpperOrderStatistic {n : ℕ}
    (μ : MeasureTheory.Measure (Fin n → ℝ)) (rankFromTop : Fin n) : ℝ :=
  ∫ sample, upperOrderStatistic sample rankFromTop ∂μ

/-- Expected pointwise top-`k` sum under a finite-sample law. -/
def expectedSampleTopKSum {n : ℕ}
    (μ : MeasureTheory.Measure (Fin n → ℝ)) (k : ℕ) : ℝ :=
  ∫ sample, sampleTopKSum sample k ∂μ

/-- Expected reflected bottom-`k` sum under a finite-sample law. -/
def expectedReflectedBottomKSum (M : ℝ) {n : ℕ}
    (μ : MeasureTheory.Measure (Fin n → ℝ)) (k : ℕ) : ℝ :=
  ∫ sample, reflectedBottomKSum M sample k ∂μ

theorem expectedReflectedBottomKSum_eq_integral_rank_count_layer_of_integrable
    (M : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ)) (k : ℕ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (hM : ∀ᵐ sample ∂μ, ∀ i, sample i ≤ M)
    (h_layer_integrable :
      MeasureTheory.Integrable
        (fun z : (Fin n → ℝ) × ℝ =>
          reflectedBottomKRankCountLayer M k z.1 z.2)
        (μ.prod (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))) :
    expectedReflectedBottomKSum M μ k =
      ∫ x in Set.Ioi (0 : ℝ),
        ∫ sample, reflectedBottomKRankCountLayer M k sample x ∂μ := by
  let ν := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let f : (Fin n → ℝ) → ℝ → ℝ :=
    fun sample x => reflectedBottomKRankCountLayer M k sample x
  have h_layer_integrable' :
      MeasureTheory.Integrable (Function.uncurry f) (μ.prod ν) := by
    simpa [ν, f, Function.uncurry] using h_layer_integrable
  have hpoint :
      (fun sample : Fin n → ℝ => reflectedBottomKSum M sample k) =ᵐ[μ]
        fun sample : Fin n → ℝ => ∫ x, f sample x ∂ν := by
    filter_upwards [hM] with sample hsample
    simpa [ν, f] using
      reflectedBottomKSum_eq_integral_rank_count_layer M sample k hsample
  calc
    expectedReflectedBottomKSum M μ k =
        ∫ sample, reflectedBottomKSum M sample k ∂μ := by
          rfl
    _ = ∫ sample, (∫ x, f sample x ∂ν) ∂μ := by
          exact MeasureTheory.integral_congr_ae hpoint
    _ = ∫ x, (∫ sample, f sample x ∂μ) ∂ν := by
          exact MeasureTheory.integral_integral_swap
            (μ := μ) (ν := ν) (f := f) h_layer_integrable'
    _ = ∫ x in Set.Ioi (0 : ℝ),
        ∫ sample, reflectedBottomKRankCountLayer M k sample x ∂μ := by
          rfl

/--
Linearity of expectation for the reflected bottom-`k` sum: the aggregate
reflected endpoint-loss term is the sum of the expected lower order statistics
of the reflected sample.
-/
theorem expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic
    (M : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ)) (k : ℕ)
    (h_integrable :
      ∀ i : Fin (min k n),
        MeasureTheory.Integrable
          (fun sample =>
            ascendingOrderStatistic (reflectedSample M sample)
              (topKRankEmbedding k n i))
          μ) :
    expectedReflectedBottomKSum M μ k =
      ∑ i : Fin (min k n),
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample)
            (topKRankEmbedding k n i) ∂μ := by
  unfold expectedReflectedBottomKSum reflectedBottomKSum
  exact MeasureTheory.integral_finset_sum Finset.univ
    (fun i _hi => h_integrable i)

/--
Fixed-`k` version of
`expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic`, for the
eventual asymptotic regime where the sample size is at least `k`.
-/
theorem expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic_of_le
    (M : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ)) {k : ℕ}
    (hkn : k ≤ n)
    (h_integrable :
      ∀ i : Fin k,
        MeasureTheory.Integrable
          (fun sample =>
            ascendingOrderStatistic (reflectedSample M sample)
              ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩)
          μ) :
    expectedReflectedBottomKSum M μ k =
      ∑ i : Fin k,
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample)
            ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ ∂μ := by
  have hmin : min k n = k := min_eq_left hkn
  have h_integrable' :
      ∀ i : Fin (min k n),
        MeasureTheory.Integrable
          (fun sample =>
            ascendingOrderStatistic (reflectedSample M sample)
              (topKRankEmbedding k n i))
          μ := by
    intro i
    let i' : Fin k := ⟨i.val, by simpa [hmin] using i.isLt⟩
    simpa [topKRankEmbedding, i'] using h_integrable i'
  have hlin :=
    expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic
      M μ k h_integrable'
  have hsum :
      (∑ i : Fin (min k n),
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample)
            (topKRankEmbedding k n i) ∂μ) =
        ∑ i : Fin k,
          ∫ sample,
            ascendingOrderStatistic (reflectedSample M sample)
              ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ ∂μ := by
    let e : Fin (min k n) ≃ Fin k := finCongr hmin
    exact Fintype.sum_equiv e
      (fun i : Fin (min k n) =>
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample)
            (topKRankEmbedding k n i) ∂μ)
      (fun i : Fin k =>
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample)
            ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ ∂μ)
      (by
        intro i
        have hval : (e i).val = i.val := by
          simp [e]
        have hrank :
            topKRankEmbedding k n i =
              (⟨(e i).val, lt_of_lt_of_le (e i).isLt hkn⟩ : Fin n) := by
          apply Fin.ext
          simp [topKRankEmbedding, hval]
        simp [hrank])
  exact hlin.trans hsum

/--
Linearity of expectation for the tuple-level top-`k` sum: the expected sum of
upper order statistics is the sum of expected upper order statistics.
-/
theorem expectedSampleTopKSum_eq_sum_expectedUpperOrderStatistic
    {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ)) (k : ℕ)
    (h_integrable :
      ∀ i : Fin (min k n),
        MeasureTheory.Integrable
          (fun sample => upperOrderStatistic sample (topKRankEmbedding k n i))
          μ) :
    expectedSampleTopKSum μ k =
      ∑ i : Fin (min k n),
        expectedUpperOrderStatistic μ (topKRankEmbedding k n i) := by
  unfold expectedSampleTopKSum expectedUpperOrderStatistic sampleTopKSum
  exact MeasureTheory.integral_finset_sum Finset.univ
    (fun i _hi => h_integrable i)

/--
Expected form of the single-rank bounded-support reflection identity.
-/
theorem expectedUpperOrderStatistic_eq_endpoint_sub_expectedReflectedAscending
    (M : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsProbabilityMeasure μ] (rankFromTop : Fin n)
    (h_integrable :
      MeasureTheory.Integrable
        (fun sample =>
          ascendingOrderStatistic (reflectedSample M sample) rankFromTop)
        μ) :
    expectedUpperOrderStatistic μ rankFromTop =
      M -
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample) rankFromTop ∂μ := by
  unfold expectedUpperOrderStatistic
  calc
    ∫ sample, upperOrderStatistic sample rankFromTop ∂μ
        = ∫ sample,
            M - ascendingOrderStatistic (reflectedSample M sample) rankFromTop
            ∂μ := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall
              (fun sample =>
                upperOrderStatistic_eq_endpoint_sub_reflectedAscending
                  M sample rankFromTop))
    _ = M -
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample) rankFromTop ∂μ := by
          rw [MeasureTheory.integral_sub
            (MeasureTheory.integrable_const M) h_integrable]
          simp [MeasureTheory.integral_const, MeasureTheory.probReal_univ]

/--
Expected bounded-support reflection identity for the top-`k` sample sum:
endpoint loss of the expected top-`k` value equals the expected sum of the
bottom reflected order statistics.
-/
theorem expectedSampleTopKEndpointLoss_eq_expectedReflectedBottomKSum
    (M : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsProbabilityMeasure μ] (k : ℕ)
    (h_integrable :
      MeasureTheory.Integrable (fun sample => sampleTopKSum sample k) μ) :
    (min k n : ℝ) * M - expectedSampleTopKSum μ k =
      expectedReflectedBottomKSum M μ k := by
  unfold expectedSampleTopKSum expectedReflectedBottomKSum
  calc
    (min k n : ℝ) * M - ∫ sample, sampleTopKSum sample k ∂μ
        = ∫ sample, (min k n : ℝ) * M - sampleTopKSum sample k ∂μ := by
          rw [MeasureTheory.integral_sub
            (MeasureTheory.integrable_const ((min k n : ℝ) * M))
            h_integrable]
          simp [MeasureTheory.integral_const, MeasureTheory.probReal_univ]
    _ = ∫ sample, sampleTopKEndpointLoss M sample k ∂μ := rfl
    _ = ∫ sample, reflectedBottomKSum M sample k ∂μ := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall
              (fun sample =>
                sampleTopKEndpointLoss_eq_reflectedBottomKSum M sample k))

/-!
## Bottom-indexed paper order-statistic means

Some papers state order-statistic expectations as a global function
`μ rank sampleSize`, with one-based ranks from the bottom.  The bridge below
connects that notation to the tuple-level `sampleTopKSum` API above.
-/

/--
Top-`k` sum from bottom-indexed expected order-statistic means.  The rank
argument is one-based: rank `a` is the largest item in an `a`-sample.
-/
def orderStatisticTopKSumFromMean
    (μ : ℕ → ℕ → ℝ) (k a : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (min k a), μ (a - i) a

@[simp] theorem orderStatisticTopKSumFromMean_zero_samples
    (μ : ℕ → ℕ → ℝ) (k : ℕ) :
    orderStatisticTopKSumFromMean μ k 0 = 0 := by
  simp [orderStatisticTopKSumFromMean]

@[simp] theorem orderStatisticTopKSumFromMean_zero_k
    (μ : ℕ → ℕ → ℝ) (a : ℕ) :
    orderStatisticTopKSumFromMean μ 0 a = 0 := by
  simp [orderStatisticTopKSumFromMean]

theorem orderStatisticTopKSumFromMean_eq_source_sum
    (μ : ℕ → ℕ → ℝ) (k a : ℕ) :
    orderStatisticTopKSumFromMean μ k a =
      ∑ i ∈ Finset.range (min k a), μ (a - i) a := rfl

/--
When the sample count is at least `k`, the bottom-indexed top-`k`
order-statistic sum is the `Fin k` sum over the upper order-statistic means.
-/
theorem orderStatisticTopKSumFromMean_eq_fin_sum_of_le
    (μ : ℕ → ℕ → ℝ) {k a : ℕ} (hka : k ≤ a) :
    orderStatisticTopKSumFromMean μ k a =
      ∑ i : Fin k, μ (a - i.val) a := by
  unfold orderStatisticTopKSumFromMean
  rw [min_eq_left hka]
  exact (Fin.sum_univ_eq_sum_range (fun i => μ (a - i) a) k).symm

/--
Fixed-`k` endpoint-loss form of
`orderStatisticTopKSumFromMean_eq_fin_sum_of_le`.
-/
theorem orderStatisticTopKLossFromMean_eq_fin_loss_of_le
    (M : ℝ) (μ : ℕ → ℕ → ℝ) {k a : ℕ} (hka : k ≤ a) :
    (k : ℝ) * M - orderStatisticTopKSumFromMean μ k a =
      (k : ℝ) * M - ∑ i : Fin k, μ (a - i.val) a := by
  rw [orderStatisticTopKSumFromMean_eq_fin_sum_of_le μ hka]

/--
The `rank`-th smallest value of a concrete `a`-sample, using a one-based rank
convention.  Out-of-range ranks are set to zero; the top-`k` bridge only
evaluates valid ranks.
-/
def sampleOrderStatisticValue {a : ℕ}
    (sample : Fin a → ℝ) (rank : ℕ) : ℝ :=
  if hrank : 0 < rank ∧ rank ≤ a then
    ascendingOrderStatistic sample ⟨rank - 1, by omega⟩
  else 0

theorem sampleOrderStatisticValue_measurable {a : ℕ} (rank : ℕ) :
    Measurable
      (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample rank) := by
  by_cases hrank : 0 < rank ∧ rank ≤ a
  · simpa [sampleOrderStatisticValue, hrank] using
      ascendingOrderStatistic_measurable (⟨rank - 1, by omega⟩ : Fin a)
  · simp [sampleOrderStatisticValue, hrank]

theorem sampleOrderStatisticValue_integrable_of_ae_bounds
    (L U : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (rank : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    MeasureTheory.Integrable
      (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample rank) μ := by
  by_cases hrank : 0 < rank ∧ rank ≤ a
  · simpa [sampleOrderStatisticValue, hrank] using
      ascendingOrderStatistic_integrable_of_ae_bounds
        L U μ (⟨rank - 1, by omega⟩ : Fin a) h_bounds
  · simp [sampleOrderStatisticValue, hrank]

theorem sampleOrderStatisticValue_topKRange_integrable_of_ae_bounds
    (L U : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    ∀ i ∈ Finset.range (min k a),
      MeasureTheory.Integrable
        (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample (a - i)) μ := by
  intro i _hi
  exact sampleOrderStatisticValue_integrable_of_ae_bounds
    L U μ (a - i) h_bounds

/--
Pointwise bridge: the bottom-indexed order-statistic sum induced by a concrete
sorted tuple equals the tuple-level top-`k` sample sum.
-/
theorem orderStatisticTopKSumFromSample_eq_sampleTopKSum
    {a : ℕ} (sample : Fin a → ℝ) (k : ℕ) :
    orderStatisticTopKSumFromMean
        (fun rank sampleSize =>
          if sampleSize = a then sampleOrderStatisticValue sample rank else 0)
        k a =
      sampleTopKSum sample k := by
  unfold orderStatisticTopKSumFromMean sampleTopKSum
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_lt : i < min k a := Finset.mem_range.mp hi
  have hi_lt_k : i < k := lt_of_lt_of_le hi_lt (min_le_left k a)
  have hi_lt_a : i < a := lt_of_lt_of_le hi_lt (min_le_right k a)
  have hrank_pos : 0 < a - i := Nat.sub_pos_of_lt hi_lt_a
  have hrank_le : a - i ≤ a := Nat.sub_le a i
  simp [sampleOrderStatisticValue, hrank_pos, hrank_le, hi_lt_k, hi_lt_a]
  unfold upperOrderStatistic
  congr 1

/--
Expected bottom-indexed order-statistic mean induced by a sample law on `a`
real draws.  The value is intended at `sampleSize = a`; other sample sizes are
set to zero so the function has a global `ℕ → ℕ → ℝ` shape.
-/
def expectedSampleOrderStatisticMean {a : ℕ}
    (μ : MeasureTheory.Measure (Fin a → ℝ)) (rank sampleSize : ℕ) : ℝ :=
  if sampleSize = a then
    ∫ sample, sampleOrderStatisticValue sample rank ∂μ
  else 0

/--
Expectation form of the pointwise bridge: if the bottom-indexed mean function
is induced by integrating sample order statistics, then its top-`k` sum is the
expected tuple-level top-`k` sample sum.
-/
theorem expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum
    {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ)) (k : ℕ)
    (h_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i)) μ) :
    orderStatisticTopKSumFromMean
        (expectedSampleOrderStatisticMean μ) k a =
      expectedSampleTopKSum μ k := by
  calc
    orderStatisticTopKSumFromMean
        (expectedSampleOrderStatisticMean μ) k a
        = ∑ i ∈ Finset.range (min k a),
            ∫ sample, sampleOrderStatisticValue sample (a - i) ∂μ := by
          unfold orderStatisticTopKSumFromMean expectedSampleOrderStatisticMean
          simp
    _ = ∫ sample,
          ∑ i ∈ Finset.range (min k a),
            sampleOrderStatisticValue sample (a - i) ∂μ := by
          rw [MeasureTheory.integral_finset_sum]
          exact h_integrable
    _ = ∫ sample,
          orderStatisticTopKSumFromMean
            (fun rank sampleSize =>
              if sampleSize = a then sampleOrderStatisticValue sample rank else 0)
            k a ∂μ := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall
              (fun sample => by
                simp [orderStatisticTopKSumFromMean]))
    _ = expectedSampleTopKSum μ k := by
          unfold expectedSampleTopKSum
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall
              (fun sample =>
                orderStatisticTopKSumFromSample_eq_sampleTopKSum sample k))

/--
Expected bounded-support top-`k` reflection in the bottom-indexed mean
interface.
-/
theorem expectedSampleOrderStatisticTopKEndpointLoss_eq_expectedReflectedBottomKSum
    (M : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsProbabilityMeasure μ] (k : ℕ)
    (h_order_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i)) μ)
    (h_top_integrable :
      MeasureTheory.Integrable
        (fun sample => sampleTopKSum sample k) μ) :
    (min k a : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedSampleOrderStatisticMean μ) k a =
      expectedReflectedBottomKSum M μ k := by
  rw [expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum
    μ k h_order_integrable]
  exact expectedSampleTopKEndpointLoss_eq_expectedReflectedBottomKSum
    M μ k h_top_integrable

/--
Bottom-indexed expected order-statistic mean induced by a family of finite
sample laws, one law for each sample size.
-/
def expectedOrderStatisticMeanSeq
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (rank sampleSize : ℕ) : ℝ :=
  expectedSampleOrderStatisticMean (sampleMeasure sampleSize) rank sampleSize

/--
Varying-sample-size version of
`expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum`.
-/
theorem expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (k a : ℕ)
    (h_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i))
          (sampleMeasure a)) :
    orderStatisticTopKSumFromMean
        (expectedOrderStatisticMeanSeq sampleMeasure) k a =
      expectedSampleTopKSum (sampleMeasure a) k := by
  simpa [expectedOrderStatisticMeanSeq] using
    expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum
      (sampleMeasure a) k h_integrable

/--
Varying-sample-size bounded reflection bridge in the global
`μ rank sampleSize` interface.
-/
theorem expectedOrderStatisticMeanSeq_topKEndpointLoss_eq_expectedReflectedBottomKSum
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
        (fun sample => sampleTopKSum sample k)
        (sampleMeasure a)) :
    (min k a : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k a =
      expectedReflectedBottomKSum M (sampleMeasure a) k := by
  simpa [expectedOrderStatisticMeanSeq] using
    expectedSampleOrderStatisticTopKEndpointLoss_eq_expectedReflectedBottomKSum
      M (sampleMeasure a) k h_order_integrable h_top_integrable

/--
Oracle for the expected value of the best `k` consumed items among `q` sampled
items of a type/category.
-/
structure TopKExpectationOracle (τ : Type*) where
  expectedTopSum : ℕ → τ → ℕ → ℝ

namespace TopKExpectationOracle

variable {τ : Type*}

/-- Marginal expected top-`k` value from adding one more sampled item. -/
def marginalTopK (O : TopKExpectationOracle τ)
    (k : ℕ) (t : τ) (q : ℕ) : ℝ :=
  O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q

/-- Diminishing marginal expected top-`k` values. -/
def HasDiminishingReturnsAt (O : TopKExpectationOracle τ) (k : ℕ) : Prop :=
  ∀ t q, O.marginalTopK k t (q + 1) ≤ O.marginalTopK k t q

/-- Nonnegative marginal expected top-`k` values. -/
def HasNonnegativeMarginalsAt (O : TopKExpectationOracle τ) (k : ℕ) : Prop :=
  ∀ t q, 0 ≤ O.marginalTopK k t q

@[simp] theorem marginalTopK_apply (O : TopKExpectationOracle τ)
    (k : ℕ) (t : τ) (q : ℕ) :
    O.marginalTopK k t q =
      O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q := rfl

/--
Certificate that all finite type-specific top-`k` marginals share a common
asymptotic scale, up to a positive type weight:

`marginal(k,t,q) / (scale q * weight t) -> 1`.

This is the probability-facing object that bounded, exponential, Pareto, or
finite-discrete order-statistic calculations should produce before the
optimization layer consumes marginal comparisons.
-/
structure ScaledMarginalLimitCertificate [Fintype τ]
    (O : TopKExpectationOracle τ) (k : ℕ)
    (scale : ℕ → ℝ) (weight : τ → ℝ) where
  scale_pos_eventually : ∀ᶠ q in atTop, 0 < scale q
  weight_pos : ∀ t, 0 < weight t
  marginal_ratio_tendsto :
    ∀ t,
      Tendsto
        (fun q => O.marginalTopK k t q / (scale q * weight t))
        atTop (nhds 1)

namespace ScaledMarginalLimitCertificate

variable [Fintype τ]
variable {O : TopKExpectationOracle τ} {k : ℕ}
variable {scale : ℕ → ℝ} {weight : τ → ℝ}

theorem eventually_uniform_ratio_abs_sub_lt
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop,
      ∀ t : τ,
        |O.marginalTopK k t q / (scale q * weight t) - 1| < ε := by
  classical
  refine eventually_all.2 ?_
  intro t
  have ht :=
    (C.marginal_ratio_tendsto t).eventually
      (Metric.ball_mem_nhds 1 hε)
  filter_upwards [ht] with q hq
  simpa [Metric.mem_ball, Real.dist_eq] using hq

theorem eventually_uniform_ratio_mem_Icc
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop,
      ∀ t : τ,
        (1 - ε ≤ O.marginalTopK k t q / (scale q * weight t)) ∧
          (O.marginalTopK k t q / (scale q * weight t) ≤ 1 + ε) := by
  filter_upwards [C.eventually_uniform_ratio_abs_sub_lt hε] with q hq t
  have habs := hq t
  rw [abs_lt] at habs
  constructor <;> linarith

theorem eventually_uniform_ratio_pos
    (C : ScaledMarginalLimitCertificate O k scale weight) :
    ∀ᶠ q in atTop,
      ∀ t : τ,
        0 < O.marginalTopK k t q / (scale q * weight t) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  filter_upwards [C.eventually_uniform_ratio_mem_Icc hhalf] with q hq t
  linarith [(hq t).1]

theorem marginalTopK_eq_ratio_mul
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {q : ℕ} {t : τ} (hscale : scale q ≠ 0) :
    O.marginalTopK k t q =
      (O.marginalTopK k t q / (scale q * weight t)) *
        (scale q * weight t) := by
  have hweight : weight t ≠ 0 := ne_of_gt (C.weight_pos t)
  field_simp [hscale, hweight]

/--
Uniform finite-type asymptotic ratio control gives an eventual multiplicative
sandwich for every type's marginal top-`k` value.
-/
theorem eventually_marginal_sandwich
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop,
      ∀ t : τ,
        (1 - ε) * (scale q * weight t) ≤ O.marginalTopK k t q ∧
          O.marginalTopK k t q ≤
            (1 + ε) * (scale q * weight t) := by
  filter_upwards
    [C.eventually_uniform_ratio_mem_Icc hε, C.scale_pos_eventually]
    with q hratio hscale t
  have hden_pos : 0 < scale q * weight t :=
    mul_pos hscale (C.weight_pos t)
  have hden_nonneg : 0 ≤ scale q * weight t := hden_pos.le
  have heq :=
    C.marginalTopK_eq_ratio_mul
      (q := q) (t := t) (ne_of_gt hscale)
  constructor
  · calc
      (1 - ε) * (scale q * weight t)
          ≤ (O.marginalTopK k t q / (scale q * weight t)) *
              (scale q * weight t) :=
            mul_le_mul_of_nonneg_right (hratio t).1 hden_nonneg
      _ = O.marginalTopK k t q := by rw [← heq]
  · calc
      O.marginalTopK k t q
          = (O.marginalTopK k t q / (scale q * weight t)) *
              (scale q * weight t) := heq
      _ ≤ (1 + ε) * (scale q * weight t) :=
            mul_le_mul_of_nonneg_right (hratio t).2 hden_nonneg

/-- A one-index marginal sandwich at a fixed count. -/
def MarginalSandwichAt
    (C : ScaledMarginalLimitCertificate O k scale weight)
    (ε : ℝ) (q : ℕ) : Prop :=
  ∀ t : τ,
    (1 - ε) * (scale q * weight t) ≤ O.marginalTopK k t q ∧
      O.marginalTopK k t q ≤ (1 + ε) * (scale q * weight t)

theorem eventually_marginalSandwichAt
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop, C.MarginalSandwichAt ε q :=
  C.eventually_marginal_sandwich hε

/--
If the upper scaled approximation for one marginal lies below the lower scaled
approximation for another, then the actual marginals are strictly ordered.
-/
theorem marginal_lt_of_scaled_gap
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} {qsrc qdst : ℕ} {src dst : τ}
    (hsrc : C.MarginalSandwichAt ε qsrc)
    (hdst : C.MarginalSandwichAt ε qdst)
    (hgap :
      (1 + ε) * (scale qsrc * weight src) <
        (1 - ε) * (scale qdst * weight dst)) :
    O.marginalTopK k src qsrc < O.marginalTopK k dst qdst :=
  lt_of_le_of_lt (hsrc src).2 (hgap.trans_le (hdst dst).1)

/--
Same-count specialization: a strict gap between scaled type weights eventually
implies the same strict ordering of top-`k` marginals.
-/
theorem eventually_same_count_marginal_lt_of_weight_gap
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) {src dst : τ}
    (hgap : (1 + ε) * weight src < (1 - ε) * weight dst) :
    ∀ᶠ q in atTop,
      O.marginalTopK k src q < O.marginalTopK k dst q := by
  filter_upwards [C.eventually_marginalSandwichAt hε, C.scale_pos_eventually]
    with q hq hscale
  apply C.marginal_lt_of_scaled_gap (qsrc := q) (qdst := q)
    (src := src) (dst := dst) hq hq
  have hscaled :
      scale q * ((1 + ε) * weight src) <
        scale q * ((1 - ε) * weight dst) :=
    mul_lt_mul_of_pos_left hgap hscale
  calc
    (1 + ε) * (scale q * weight src)
        = scale q * ((1 + ε) * weight src) := by ring
    _ < scale q * ((1 - ε) * weight dst) := hscaled
    _ = (1 - ε) * (scale q * weight dst) := by ring

end ScaledMarginalLimitCertificate

end TopKExpectationOracle

end

end Probability
end EconCSLib
