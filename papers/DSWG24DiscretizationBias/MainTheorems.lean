import EconCSLib.Foundations.Optimization.Argmax

/-!
# Paper-Facing Theorems: Addressing Discretization-Induced Bias

This file is the public theorem interface for the current discretization-bias
formalization. The main wrappers below state source-facing expected-objective
results for Theorem 2(i)--(ii), using an abstract finite-linear expectation
operator to represent the paper's expectation over sampled datasets and the
Bayes tower-property step.
-/

namespace DSWG24DiscretizationBias

open scoped BigOperators

/--
Per-dataset objective from Equation (1)/(3).

For an observed dataset state `xs`, the decision vector `decision` is scored by
the posterior-score accuracy term and an arbitrary fidelity term encoding the
chosen reference distribution.
-/
noncomputable def paperONObjective
    {N K : ℕ} {σ : Type*}
    (γ : ℝ) (posterior : σ → Fin N → Fin K → ℝ)
    (fidelity : σ → (Fin N → Fin K) → ℝ)
    (xs : σ) (decision : Fin N → Fin K) : ℝ :=
  γ * EconCSLib.Decision.averageScore (posterior xs) decision +
    (1 - γ) * fidelity xs decision

/--
Paper objective `O_N^γ` from Equation (3), written in terms of expected true
0-1 accuracy and expected distributional fidelity.
-/
noncomputable def paperExpectedONObjective
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (expect : (ω → ℝ) → ℝ) (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (γ : ℝ) (fidelity : σ → (Fin N → Fin K) → ℝ)
    (rule : σ → Fin N → Fin K) : ℝ :=
  γ * EconCSLib.Decision.expectedDecisionAccuracy
      expect observedDataset trueLabels rule +
    (1 - γ) * EconCSLib.Decision.expectedObjective
      expect observedDataset fidelity rule

/--
Bayes-optimal posteriors convert the paper's expected true-accuracy objective
to the posterior-score objective optimized pointwise in Equation (1).
-/
theorem paperExpectedONObjective_eq_expected_paperONObjective
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (expect : (ω → ℝ) → ℝ)
    (hlin : EconCSLib.Decision.FiniteLinearExpectation expect)
    (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (γ : ℝ) (posterior : σ → Fin N → Fin K → ℝ)
    (fidelity : σ → (Fin N → Fin K) → ℝ)
    (hbayesRow : ∀ i (choose : σ → Fin K),
      expect (fun x =>
          if choose (observedDataset x) = trueLabels x i then (1 : ℝ) else 0) =
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x))))
    (rule : σ → Fin N → Fin K) :
    paperExpectedONObjective expect observedDataset trueLabels γ fidelity rule =
      EconCSLib.Decision.expectedObjective
        expect observedDataset (paperONObjective γ posterior fidelity) rule := by
  symm
  calc
    EconCSLib.Decision.expectedObjective
        expect observedDataset (paperONObjective γ posterior fidelity) rule =
      γ * EconCSLib.Decision.expectedDecisionScore
          expect observedDataset posterior rule +
        (1 - γ) * EconCSLib.Decision.expectedObjective
          expect observedDataset fidelity rule := by
        simpa [paperONObjective, EconCSLib.Decision.expectedDecisionScore] using
          EconCSLib.Decision.expectedObjective_linear_combination
            expect hlin observedDataset
            (fun xs decision =>
              EconCSLib.Decision.averageScore (posterior xs) decision)
            fidelity γ (1 - γ) rule
    _ = γ * EconCSLib.Decision.expectedDecisionAccuracy
          expect observedDataset trueLabels rule +
        (1 - γ) * EconCSLib.Decision.expectedObjective
          expect observedDataset fidelity rule := by
        rw [← EconCSLib.Decision.expectedDecisionAccuracy_eq_expectedDecisionScore_of_row_bayes
          expect hlin observedDataset trueLabels posterior hbayesRow rule]
    _ = paperExpectedONObjective expect observedDataset trueLabels γ fidelity rule := by
        rfl

/--
Source-facing Theorem 2(i), expected-objective form.

For every `γ` and reference-distribution fidelity term, there exists a joint
decision rule maximizing the paper objective `O_N^γ`.  The proof selects an
optimizer for the finite label assignment problem at each observed dataset and
then uses monotonicity of the outer expectation over datasets.
-/
theorem paper_theorem2i_joint_optimization_rule_exists
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hNK : K < N)
    (expect : (ω → ℝ) → ℝ)
    (hlin : EconCSLib.Decision.FiniteLinearExpectation expect)
    (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (γ : ℝ) (posterior : σ → Fin N → Fin K → ℝ)
    (fidelity : σ → (Fin N → Fin K) → ℝ)
    (hbayesRow : ∀ i (choose : σ → Fin K),
      expect (fun x =>
          if choose (observedDataset x) = trueLabels x i then (1 : ℝ) else 0) =
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) :
    ∃ optRule : σ → Fin N → Fin K,
      ∀ rule : σ → Fin N → Fin K,
        paperExpectedONObjective expect observedDataset trueLabels γ fidelity rule ≤
          paperExpectedONObjective expect observedDataset trueLabels γ fidelity optRule := by
  classical
  obtain ⟨optRule, hopt⟩ :=
    EconCSLib.Decision.exists_rule_maximizing_expectedObjective_of_pointwise_exists
      expect hlin.monotone observedDataset (paperONObjective γ posterior fidelity)
      (by
        intro xs
        exact EconCSLib.Decision.exists_maximizingDecisionRule
          (paperONObjective γ posterior fidelity xs))
  refine ⟨optRule, ?_⟩
  intro rule
  rw [paperExpectedONObjective_eq_expected_paperONObjective
    expect hlin observedDataset trueLabels γ posterior fidelity hbayesRow rule]
  rw [paperExpectedONObjective_eq_expected_paperONObjective
    expect hlin observedDataset trueLabels γ posterior fidelity hbayesRow optRule]
  exact hopt rule

/--
Auxiliary finite deterministic Bayes-score maximization.

For a finite dataset `ι`, label set `α`, and Bayes posterior score
`posterior i a`, any rule `argmaxRule` that pointwise maximizes this posterior
score also maximizes empirical Bayes-score accuracy among deterministic
decision rules.
-/
theorem paper_theorem2ii_argmax_accuracy_maximizing
    {ι α : Type*} [Fintype ι]
    (posterior : ι → α → ℝ) {decisionRule argmaxRule : ι → α}
    (hargmax : EconCSLib.Decision.IsPointwiseMax posterior argmaxRule) :
    EconCSLib.Decision.averageScore posterior decisionRule ≤
      EconCSLib.Decision.averageScore posterior argmaxRule := by
  exact EconCSLib.Decision.averageScore_le_of_isPointwiseMax posterior hargmax

/--
Source-facing Theorem 2(ii), expected-accuracy form.

For a Bayes-optimal posterior `q`, the paper's tower-property step says that
expected 0-1 accuracy equals expected posterior score for every decision rule.
The row-wise Bayes identities below imply that tower-property bridge, so the
argmax rule maximizes expected accuracy over all joint decision rules.
-/
theorem paper_theorem2ii_argmax_expected_accuracy_maximizing
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hNK : K < N)
    (expect : (ω → ℝ) → ℝ)
    (hlin : EconCSLib.Decision.FiniteLinearExpectation expect)
    (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (posterior : σ → Fin N → Fin K → ℝ)
    {decisionRule argmaxRule : σ → Fin N → Fin K}
    (hargmax :
      ∀ xs, EconCSLib.Decision.IsPointwiseMax (posterior xs) (argmaxRule xs))
    (hbayesRow : ∀ i (choose : σ → Fin K),
      expect (fun x =>
          if choose (observedDataset x) = trueLabels x i then (1 : ℝ) else 0) =
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) :
    EconCSLib.Decision.expectedDecisionAccuracy
        expect observedDataset trueLabels decisionRule ≤
      EconCSLib.Decision.expectedDecisionAccuracy
        expect observedDataset trueLabels argmaxRule := by
  have hbayes : ∀ rule : σ → Fin N → Fin K,
      EconCSLib.Decision.expectedDecisionAccuracy
          expect observedDataset trueLabels rule =
        EconCSLib.Decision.expectedDecisionScore
          expect observedDataset posterior rule :=
    EconCSLib.Decision.expectedDecisionAccuracy_eq_expectedDecisionScore_of_row_bayes
      expect hlin observedDataset trueLabels posterior hbayesRow
  exact EconCSLib.Decision.expectedDecisionAccuracy_le_of_bayesScore_pointwiseMax
    expect hlin.monotone observedDataset trueLabels posterior hargmax hbayes

end DSWG24DiscretizationBias
