import PRPKG24AccuracyDiversity.ProofInterface

/-!
# Paper Assumptions: PRPKG24 Accuracy-Diversity

This file records source theorem-domain conditions and documented partial
boundaries used by the paper-facing review surface. The main remaining partial
boundary is Proposition 4's continuous sphere/Laplace analytic layer.
-/

namespace PRPKG24AccuracyDiversity

/-- Example 1 uses a calibrated two-type exponential mixture with positive parameters. -/
-- audit-premise: hp1 : 0 < p1
-- audit-premise: hp2 : 0 < p2
-- audit-premise: hlambda : 0 < lambda
-- audit-premise: hp_sum : p1 + p2 = 1
abbrev assumption_example1_positive_calibrated_exponential_parameters
    (p1 p2 lambda : ℝ) : Prop :=
  0 < p1 ∧ 0 < p2 ∧ 0 < lambda ∧ p1 + p2 = 1

/-- Theorem 1(i) finite-discrete endpoint separates a top value from lower values. -/
-- audit-premise: hk_pos : 0 < k
-- audit-premise: hxTop_pos : 0 < xTop
-- audit-premise: hxSecond_nonneg : 0 ≤ xSecond
-- audit-premise: hsecond_le_top : xSecond ≤ xTop
-- audit-premise: hsecond_lt_top : xSecond < xTop
-- audit-premise: hvalue_le : ∀ ω, value ω ≤ xTop
-- audit-premise: hvalue_split : ∀ ω, value ω = xTop ∨ value ω ≤ xSecond
abbrev assumption_finite_discrete_top_value_domain {Ω : Type*}
    (k : ℕ) (value : Ω → ℝ) (xTop xSecond : ℝ) : Prop :=
  0 < k ∧
    0 < xTop ∧
      0 ≤ xSecond ∧
        xSecond ≤ xTop ∧
          xSecond < xTop ∧
            (∀ ω, value ω ≤ xTop) ∧
              (∀ ω, value ω = xTop ∨ value ω ≤ xSecond)

/-- Type-likelihood weights in the optimization model are positive. -/
-- audit-premise: hlike_pos : ∀ t : ItemType T, 0 < likelihood t
-- audit-premise: hlike_pos : ∀ t, 0 < likelihood t
-- audit-premise: hlike_pos : ∀ t, 0 < B.likelihood t
abbrev assumption_positive_type_likelihoods {T : ℕ}
    (likelihood : ItemType T → ℝ) : Prop :=
  ∀ t : ItemType T, 0 < likelihood t

/-- Theorem 1(ii) and Lemma 1 use the bounded-support upper-endpoint density domain. -/
-- audit-premise: h_base_bounds : ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M
-- audit-premise: h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y
-- audit-premise: hM_pos : 0 < M
-- audit-premise: hbeta_pos : 0 < beta
-- audit-premise: hc_pos : 0 < c
-- audit-premise: hwidth_pos : 0 < M - L
abbrev assumption_bounded_upper_endpoint_density_domain
    (baseMeasure : MeasureTheory.Measure ℝ) (L M beta c : ℝ) : Prop :=
  (∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M) ∧
    (∀ᵐ y ∂baseMeasure, 0 ≤ y) ∧
      0 < M ∧ 0 < beta ∧ 0 < c ∧ 0 < M - L

/-- Theorem 1(iii)/Lemma D.3 use positive exponential rate and top-k size. -/
-- audit-premise: hlambda_pos : 0 < lambda
-- audit-premise: hk_pos : 0 < k
abbrev assumption_exponential_order_statistic_domain
    (lambda : ℝ) (k : ℕ) : Prop :=
  0 < lambda ∧ 0 < k

/-- Theorem 1(iv)/Lemma D.4 use the finite-mean Pareto domain. -/
-- audit-premise: halpha : 1 < alpha
-- audit-premise: hk : 0 < k
abbrev assumption_pareto_finite_mean_domain (alpha : ℝ) (k : ℕ) : Prop :=
  1 < alpha ∧ 0 < k

/-- Theorem 1(v) common-mean all-consumed endpoint uses an argmax condition. -/
-- audit-premise: hmean_nonneg : 0 ≤ mean
-- audit-premise: hbest : ∀ t, likelihood t ≤ likelihood best
abbrev assumption_common_mean_argmax_domain {T : ℕ}
    (likelihood : ItemType T → ℝ) (mean : ℝ) (best : ItemType T) : Prop :=
  0 ≤ mean ∧ ∀ t, likelihood t ≤ likelihood best

/-- Theorem 1(v) converse uses a positive mean and unique likelihood maximizer. -/
-- audit-premise: hmean_pos : 0 < mean
-- audit-premise: hbest_strict : ∀ t, t ≠ best → likelihood t < likelihood best
abbrev assumption_unique_common_mean_argmax_domain {T : ℕ}
    (likelihood : ItemType T → ℝ) (mean : ℝ) (best : ItemType T) : Prop :=
  0 < mean ∧ ∀ t, t ≠ best → likelihood t < likelihood best

/-- Corollary 1 ranges over nonnegative homogeneity exponents. -/
-- audit-premise: hgamma_nonneg : 0 ≤ gamma
abbrev assumption_nonnegative_homogeneity_exponent (gamma : ℝ) : Prop :=
  0 ≤ gamma

/-- Theorem 2 decaying Bernoulli statements use source parameter domains. -/
-- audit-premise: halpha_nonneg : 0 ≤ alpha
-- audit-premise: halpha_lt_one : alpha < 1
-- audit-premise: halpha_gt_one : 1 < alpha
-- audit-premise: halpha : 0 < alpha
-- audit-premise: hc : 0 < c
-- audit-premise: hc_pos : 0 < c
-- audit-premise: hc_nonneg : 0 ≤ c
-- audit-premise: hd : 0 ≤ d
-- audit-premise: hd_nonneg : 0 ≤ d
-- audit-premise: hfirst : decayingBernoulliSuccess c d alpha 0 < 1
-- audit-premise: hfirst : decayingBernoulliSuccess c d 1 0 < 1
abbrev assumption_decaying_bernoulli_parameter_domain
    (alpha c d : ℝ) : Prop :=
  ((0 ≤ alpha ∧ alpha < 1) ∨ alpha = 1 ∨ 1 < alpha ∨ 0 < alpha) ∧
    0 < c ∧
      0 ≤ c ∧
        0 ≤ d ∧
          decayingBernoulliSuccess c d alpha 0 < 1 ∧
            decayingBernoulliSuccess c d 1 0 < 1

/-- Theorem 3/Corollary 3 require Bernoulli probabilities in `(0,1)`. -/
-- audit-premise: hprob_pos : ∀ t, 0 < B.successProb t
-- audit-premise: hprob_lt_one : ∀ t, B.successProb t < 1
-- audit-premise: hprob_eq : ∀ i j : ItemType T, B.successProb i = B.successProb j
abbrev assumption_varying_bernoulli_probability_domain {T : ℕ}
    (B : BernoulliSatisfactionModel T) : Prop :=
  (∀ t, 0 < B.successProb t) ∧
    (∀ t, B.successProb t < 1) ∧
      (∀ i j : ItemType T, B.successProb i = B.successProb j)

/-- Proposition 2's corrected uniform route uses positive type likelihoods and top-k counts. -/
-- audit-premise: hkpos : ∀ N, 0 < N → 0 < kseq N
abbrev assumption_uniform_top_k_positive_count_domain (kseq : ℕ → ℕ) : Prop :=
  ∀ N, 0 < N → 0 < kseq N

/-- Proposition 4's full continuous-sphere theorem remains at the Laplace analytic boundary. -/
-- audit-premise: C : Proposition4ContinuousSphereCertificate Profile
abbrev assumption_proposition4_continuous_sphere_laplace_boundary : Prop := True

/-- Lemma D.2's finite split-integral endpoint remains at the analytic asymptotic boundary. -/
-- audit-premise: C : BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G
abbrev assumption_lemmaD2_split_integral_analytic_boundary : Prop := True

/-- Lemma D.5's finite rounding endpoint is stated for positive `N`. -/
-- audit-premise: hNpos : 0 < N
abbrev assumption_positive_rounding_population_size (N : ℕ) : Prop :=
  0 < N

end PRPKG24AccuracyDiversity
