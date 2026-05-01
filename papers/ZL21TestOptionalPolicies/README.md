# Test-optional Admissions and Informational Gaps

## Source Version

- Paper: *Test-optional Policies: Overcoming Strategic Behavior and Informational Gaps*
- Authors: Zhi Liu and Nikhil Garg
- Version formalized: arXiv:2107.08922 / EAAMO 2021 version
- Official URL: https://doi.org/10.1145/3465416.3483293
- arXiv URL: https://arxiv.org/abs/2107.08922
- PDF URL: https://arxiv.org/pdf/2107.08922
- Accessed: 2026-05-01

The paper is intentionally not committed to git (PDFs are kept local and ignored by
`.gitignore`). The current checkout does not include local cached PDF text, so this
README is maintained directly from the implemented paper-facing declarations in
`MainTheorems.lean`.

## Central Theorem File

- `ZL21TestOptionalPolicies/MainTheorems.lean`

## Dependency DAG

- `ZL21TestOptionalPolicies/DependencyDAG.tex`

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Model abstraction | `ZL21Model` | formalized | `MainTheorems.lean` | finite typeclass assumptions already in declaration |
| Base signal model wrapper | `zl21BaseModel` | formalized | `MainTheorems.lean` | none |
| Test signal model wrapper | `zl21TestModel` | formalized | `MainTheorems.lean` | none |
| Base mass/quality definitions | `zl21BaseMass`, `zl21BaseConditionalMass` | formalized | `MainTheorems.lean` | none |
| Test mass/quality definitions | `zl21TestMass`, `zl21TestConditionalMass` | formalized | `MainTheorems.lean` | none |
| Selection probability definitions | `zl21BaseSelectionProb`, `zl21TestSelectionProb` | formalized | `MainTheorems.lean` | none |
| Base universal acceptance mass | `zl21_base_universal_accept` | formalized | `MainTheorems.lean` | none |
| Base non-accepting mass | `zl21_base_no_accept` | formalized | `MainTheorems.lean` | none |
| Base complement mass identity | `zl21_base_mass_of_compl` | formalized | `MainTheorems.lean` | none |
| Base mass upper bound | `zl21_base_mass_le_total_of_quality_nonneg` | formalized | `MainTheorems.lean` | `∀ θ, 0 ≤ quality θ` |
| Base conditional on zero selection | `zl21_base_conditional_of_zero_selection` | formalized | `MainTheorems.lean` | `zl21BaseSelectionProb m p = 0` |
| Base mass on zero-selection event | `zl21_base_mass_of_zero_selection` | formalized | `MainTheorems.lean` | `zl21BaseSelectionProb m p = 0` |
| Base product decomposition | `zl21_base_mass_eq_selectionProb_mul_conditionalMass` | formalized | `MainTheorems.lean` | none |
| Base nonnegative selection mass | `zl21_base_mass_nonneg_of_quality_nonneg` | formalized | `MainTheorems.lean` | `∀ θ, 0 ≤ quality θ` |
| Base nonnegative conditional expectation | `zl21_base_conditional_nonneg_of_quality_nonneg` | formalized | `MainTheorems.lean` | `∀ θ, 0 ≤ quality θ` |
| Base monotonicity in selection predicate | `zl21_base_mass_le_of_pred_le` | formalized | `MainTheorems.lean` | `∀ θ, 0 ≤ quality θ` |
| Base universal conditional expectation | `zl21_base_conditional_universal_accept` | formalized | `MainTheorems.lean` | none |
| Base complement conditional formula | `zl21_base_conditional_of_compl` | formalized | `MainTheorems.lean` | division-formalized over selection probability |
| Base expectation decomposition | `zl21_base_exp_decompose` | formalized | `MainTheorems.lean` | none |
| Test universal acceptance mass | `zl21_test_universal_accept` | formalized | `MainTheorems.lean` | none |
| Test non-acceptance mass | `zl21_test_no_accept` | formalized | `MainTheorems.lean` | none |
| Test complement mass identity | `zl21_test_mass_of_compl` | formalized | `MainTheorems.lean` | none |
| Test mass upper bound | `zl21_test_mass_le_total_of_quality_nonneg` | formalized | `MainTheorems.lean` | `∀ θ, 0 ≤ quality θ` |
| Test conditional on zero selection | `zl21_test_conditional_of_zero_selection` | formalized | `MainTheorems.lean` | `zl21TestSelectionProb m p = 0` |
| Test mass on zero-selection event | `zl21_test_mass_of_zero_selection` | formalized | `MainTheorems.lean` | `zl21TestSelectionProb m p = 0` |
| Test product decomposition | `zl21_test_mass_eq_selectionProb_mul_conditionalMass` | formalized | `MainTheorems.lean` | none |
| Test nonnegative selection mass | `zl21_test_mass_nonneg_of_quality_nonneg` | formalized | `MainTheorems.lean` | `∀ θ, 0 ≤ quality θ` |
| Test nonnegative conditional expectation | `zl21_test_conditional_nonneg_of_quality_nonneg` | formalized | `MainTheorems.lean` | `∀ θ, 0 ≤ quality θ` |
| Test monotonicity in selection predicate | `zl21_test_mass_le_of_pred_le` | formalized | `MainTheorems.lean` | `∀ θ, 0 ≤ quality θ` |
| Test universal conditional expectation | `zl21_test_conditional_universal_accept` | formalized | `MainTheorems.lean` | none |
| Test complement conditional formula | `zl21_test_conditional_of_compl` | formalized | `MainTheorems.lean` | division-formalized over selection probability |
| Test expectation decomposition | `zl21_test_exp_decompose` | formalized | `MainTheorems.lean` | none |

## Source Notes

All paper-facing lemmas in `MainTheorems.lean` currently close the finite-type
decomposition identities and nonnegativity monotonicity identities for base/test
selection policies.
