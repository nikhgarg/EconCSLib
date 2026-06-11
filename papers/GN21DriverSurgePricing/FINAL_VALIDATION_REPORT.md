# Final Validation Report: Driver Surge Pricing

## 1. Human Verdict

- Lean formalization status: formalized
- Human dashboard review status: 0/24 rows reviewed; 0 stale; 0 mismatches.
- Main caveat: Named CTMC lemmas and Theorems 1--4 are exposed; zero-mass boundary behavior is audited separately.

The GN21 driver-surge paper is complete at the Lean proof level for the
paper-facing definitions and named results represented in
`PaperInterface.lean`.  The remaining non-Lean task is human signoff in the
review dashboard; the dashboard should currently show `0/24` rows reviewed
until a human reviewer saves those rows.

The formalization did not find a false main theorem.  It did find one important
domain issue that the paper leaves implicit: Appendix D reward rates divide by
accepted-trip mass/time quantities, so zero-mass policies need explicit
handling.  Lean proves the main Theorem 3 route on the source-relevant
defined-reward/feasible-current-bounds domain and records why a broader
zero-mass shortcut is not automatic for totalized real-valued division.

Lean footprint: the paper folder contains 143,056 lines of paper-local Lean
code across 12 `.lean` files.  The human-review surface is deliberately much
smaller: `PaperInterface.lean` is 184 lines and exposes 24 dashboard rows.

## 2. Source and Scope

Not separately recorded in the existing report.

## 3. What Has Been Proven

- The paper's single-state and dynamic incentive-compatibility definitions are
  represented as measurable trip-policy optimization statements, including the
  threshold-policy notation and the positive-denominator dynamic reward domain.

- Section 2.2's renewal-reward claim is proved through an explicit IID cycle
  model: lifetime hourly earnings equal expected cycle reward divided by
  expected cycle length under the stated stochastic assumptions.

- Theorem 1 and Proposition 3.1 are proved for the single-state model.  Lean
  verifies the threshold best-response theorem and the affine-pricing
  incentive-compatibility condition `0 <= a <= m / lambda`.

- Lemmas 1-3 and Remarks 1, 3, and 4 are proved for the CTMC/dynamic reward
  formulas: reward decomposition, switch probabilities, time fractions, the
  small-time switch-rate limit, and the nonnegativity/monotonicity facts used
  later in Appendix D.

- Lemmas 4-10 are proved as the response-shape chain used by the dynamic
  theorems.  This includes threshold uniqueness, the fixed-response policy
  form, the endpoint derivative formula, the quasi-convex/quasi-concave
  response facts, and the surge/non-surge derivative positivity lemmas used in
  Theorem 3.

- Theorem 2 is proved in two source-facing pieces: the structural
  multiplicative-policy shape result and an explicit instance with positive
  finite cutoff deviations in both states, proving that multiplicative pricing
  need not be incentive compatible.

- Theorem 4 is proved at the measure-theoretic structural surface: optimal
  policies have representatives of the source's stated threshold/interval forms,
  up to null feasible-trip sets.

- Theorem 3 is proved through the paper proof path: first choose the
  surge-state structured price via Lemma 9, transport the resulting current
  bounds, then choose the non-surge price via Lemma 10.  The final statement
  constructs prices of the form `m_i tau + z_i q_{i->j}(tau)`, proves
  measurable incentive compatibility, and proves accept-all uniqueness up to
  null sets on the feasible-current-bounds source-data assumptions.

## 4. Additional Assumptions Beyond Paper

None separately recorded in the existing report.

## 5. Proof-Strategy Deviations

### Did Lean Need a Different Qualitative Proof?

Mostly the proof follows the paper's qualitative path, especially for Theorem 3.
The differences are the places where the paper uses standard continuous-time or
measure-theoretic shorthand that Lean cannot leave implicit:

- Continuous trip policies are handled directly as measurable sets of positive
  real trip lengths, with almost-everywhere equality for structural policy
  forms.  The proof did not detour through a finite discretization.

- The renewal-reward bridge is proved with explicit IID cycles and strong-law
  wrappers rather than an informal limit argument.

- Theorem 1 handles atoms at threshold boundaries using one-sided
  dominated-convergence arguments instead of assuming away boundary mass.

- Theorem 3 separates defined-reward positive-mass reasoning from zero-mass
  totalization.  Lean also records obstruction lemmas showing that an overbroad
  zero-mass-dominance certificate would be false without extra hypotheses.

- Theorem 2's "not incentive compatible" clause is witnessed by a concrete
  measured atomic instance, so the existential counterexample is inspectable.

## 6. Proof Tricks Worth Reusing

- Work directly in the continuous/measure-theoretic model when the source proof
  is continuous.  The finite-support model was useful as support, but the paper
  closed only after the proof focused on measurable trip-length sets,
  integrals, and a.e. policy equality.

- State positive-denominator domains early.  The biggest avoidable delay was
  discovering that the paper's reward-rate notation assumes accepted-trip
  mass/time denominators are meaningful, while Lean's real division totalizes
  zero denominators.  This should have been surfaced earlier as a human-facing
  assumption decision: prove the intended positive-mass theorem now, document
  the domain assumption, and only then decide whether an all-feasible
  zero-mass strengthening is worth pursuing.

- Follow the paper's sequential Theorem 3 route.  The successful path first
  applies the surge Lemma 9 construction, then transports current bounds, then
  applies the non-surge Lemma 10 construction.  Symmetric all-at-once wrappers
  created stronger and sometimes false side obligations.

- Separate stochastic limit, algebraic reward-rate, and policy-shape work.
  Renewal-reward strong-law wrappers, CTMC scalar identities, and Lemma 5
  a.e. policy-form selectors each became tractable only after being isolated.

- For existential counterexamples, build a concrete measured atomic instance
  and reduce it to named aggregate primitives before doing strict inequalities.
  This avoided large symbolic expressions involving exponentials in the main
  proof path.

## 7. Library Lift Pass

The post-closeout lift moved the reusable pieces that passed the "second paper"
test without disturbing the paper-facing GN21 definitions.

Lifted now:

- `EconCSLib.Foundations.Probability.ContinuousReward`: positive-real
  accepted-set mass, time, reward, renewal-reward, average-reward, and the
  zero accepted-time to zero accepted-mass bridge used by continuous
  trip-policy papers.

- `EconCSLib.Foundations.Optimization.Endpoint`: one-dimensional endpoint
  calculus from derivative signs, first/last-zero stopping lemmas, and
  one-sided local improvement/decrease steps for cutoff and interval-endpoint
  proofs.

Kept paper-local for now:

- Two-state CTMC reward accounting: state reward rates, exit weights, time
  fractions, positive-mass reward-rate bridges, and structured-price switch
  kernels should become reusable CTMC/renewal-reward infrastructure rather than
  GN21-only declarations.

- Positive-denominator and partial-reward interfaces: papers with ratios should
  have a reusable defined-reward API so source semantics do not depend on
  Lean's totalized real division at zero.

- Atomic continuous-measure reductions: weighted Dirac and finite atomic
  set-integral simplification lemmas would make future continuous
  counterexample constructions much faster.

The GN21 paper-local definitions remain formula-explicit.  They are not opaque
aliases to generic library constants; instead the paper wrappers call the
library lemmas with `simpa` compatibility bridges.  This preserves the human
review surface and avoids destabilizing the long compiled proof.

## 8. DAG Audit

I rerendered and visually inspected `DependencyDAG.pdf` after this pass.  The
current DAG uses the shared preamble, has visible spacing between nodes, and no
arrow or label crosses through a node body.

The DAG was made more paper-facing: the disconnected finite-MDP implementation
support box was removed, the appendix Remarks 1, 3, and 4 are now explicit, and
Theorem 2 is represented by one combined paper-facing box instead of separate
shape and counterexample boxes.  The zero-mass reward issue is documented in
this report rather than shown in the DAG.  The remaining boxes correspond to the
paper-facing model, Section 2.2 renewal-reward bridge, named
lemmas/proposition/theorems, and the paper proof flow.

## 9. Conditional Results and Remaining Gaps

None separately recorded in the existing report.

## 10. Suspected Paper Errors or Inconsistencies

### Is Anything in the Paper Wrong?

No substantive theorem was rejected by Lean.

Two paper-facing issues were found and documented:

- Appendix D's reward-rate notation treats ratios as if their denominators are
  always meaningful.  The formalization makes this domain explicit.  This is a
  real edge-case ambiguity, not a counterexample to the paper's intended
  positive-mass/feasible proof route.

- In the printed Theorem 4 surge-state bullet list, the first two surge bullets
  say `sigma1` where the surrounding text and proof require `sigma2`.  Lean uses
  the intended surge-state policy variable.  This is a notational typo, not a
  mathematical failure.

The paper also reuses symbols such as `R1` and `R2` locally in Appendix lemmas.
The Lean development renames those local quantities where needed; this was a
disambiguation step, not a paper error.

## 11. Validation Checks

### Human Review Status

`SOURCE_AUDIT.md` records an agent source audit for all 24 paper-interface rows.
That audit checks that the Lean-facing rows correspond to paper-facing source
claims, but it is not human dashboard review.

After clearing the agent-generated local trace, the dashboard precheck reports
`0/24 reviewed`, `24 unreviewed`, `0 stale`, and `0 mismatch`.  This is the
expected state until a human reviewer validates the rows through the dashboard.

### Verification Summary

The paper-local root module and final audit surfaces build successfully:
`GN21DriverSurgePricing`, `GN21DriverSurgePricing.PaperInterface`, and
`GN21DriverSurgePricing.PostPaperAudit`.  The dependency DAG renders, and the
GN21 paper folder has no remaining `sorry`, `admit`, `axiom`, or `by omega`
placeholders in `.lean` files.

The detailed declaration ledger lives in `PostPaperAudit.lean`; the durable
source-to-Lean checklist lives in `SOURCE_AUDIT.md`; and the concise
human-review theorem surface lives in `PaperInterface.lean`.

### Statement Translation Audit

Audit date: 2026-06-06.
Scope: current dashboard rows from `PaperInterface.lean`; `lean_to_tex_llm.json` records context-free Lean-to-TeX drafts and `statement_match_llm.json` records the context-free paper-vs-translation judgment.

Summary: 24 rows; 24 match, 0 uncertain, 0 mismatch, 0 missing. Stale sidecar rows: none. Surface audit: not required (30 or fewer rows).

No flagged rows remain after the current statement check.

## 12. Final Verdict

### Final Status

Lean formalization: complete for the represented paper-facing definitions and
named results.

Human validation: pending.  The next step is dashboard review of the 24
`PaperInterface.lean` rows, not more Lean proof work.

- Completion status: formalized.
- Summary: Named CTMC lemmas and Theorems 1--4 are exposed; zero-mass boundary behavior is audited separately.

## 13. Paper Definitions Checked

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| def review_definition_single_state_ic | `review_definition_single_state_ic` | Matches the current paper-facing statement. |
| def review_definition_dynamic_ic | `review_definition_dynamic_ic` | Matches the current paper-facing statement. |
| def review_definition_threshold_policy | `review_definition_threshold_policy` | Matches the current paper-facing statement. |
| def review_definition_dynamic_defined_reward | `review_definition_dynamic_defined_reward` | Matches the current paper-facing statement. |
| abbrev review_section2_single_state_renewal_reward_iid_bridge | `review_section2_single_state_renewal_reward_iid_bridge` | - Section 2.2: IID renewal-reward bridge for the single-state formula. |
| abbrev review_proposition3_1_affine_single_state_ic | `review_proposition3_1_affine_single_state_ic` | - Proposition 3.1: affine single-state pricing is incentive compatible. |
| abbrev review_theorem1_single_state_threshold_best_response | `review_theorem1_single_state_threshold_best_response` | - Theorem 1: optimal single-state policies are threshold policies. |
| abbrev review_lemma4_single_state_threshold_uniqueness | `review_lemma4_single_state_threshold_uniqueness` | - Lemma 4: threshold optimizer uniqueness up to null sets. |
| abbrev review_lemma1_measured_dynamic_reward_decomposition | `review_lemma1_measured_dynamic_reward_decomposition` | - Lemma 1: dynamic reward decomposition. |
| abbrev review_lemma2_switch_probability_formula | `review_lemma2_switch_probability_formula` | - Lemma 2: CTMC switch-probability formula. |
| abbrev review_lemma3_measured_time_fraction_formula | `review_lemma3_measured_time_fraction_formula` | - Lemma 3: state time-fraction formula. |
| abbrev review_remark1_switch_probability_per_time_strictAntiOn | `review_remark1_switch_probability_per_time_strictAntiOn` | - Remark 1: switch probability per unit time is strictly decreasing. |
| abbrev review_remark3_switch_probability_per_time_tendsto_at_zero | `review_remark3_switch_probability_per_time_tendsto_at_zero` | - Remark 3: small-time switch probability per unit time tends to the switch rate. |
| abbrev review_remark4_switch_time_minus_switch_probability_nonneg | `review_remark4_switch_time_minus_switch_probability_nonneg` | - Remark 4: `lambda * t - q(t)` is nonnegative. |
| abbrev review_lemma5_fixed_response_policy_form | `review_lemma5_fixed_response_policy_form` | - Lemma 5: fixed-response feasible policy form almost everywhere. |
| abbrev review_lemma6_upper_endpoint_derivative_formula | `review_lemma6_upper_endpoint_derivative_formula` | - Lemma 6: upper-endpoint derivative formula. |
| abbrev review_lemma7_affine_positive_additive_response_quasi_convex | `review_lemma7_affine_positive_additive_response_quasi_convex` | - Lemma 7: positive-additive affine response is quasi-convex. |
| abbrev review_lemma8_affine_negative_additive_response_quasi_concave | `review_lemma8_affine_negative_additive_response_quasi_concave` | - Lemma 8: negative-additive affine response is quasi-concave. |
| abbrev review_lemma9_surge_derivative_positive_of_acceptAll_bounds | `review_lemma9_surge_derivative_positive_of_acceptAll_bounds` | - Lemma 9: surge-state derivative positivity under accept-all bounds. |
| abbrev review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds | `review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds` | - Lemma 10: non-surge-state derivative positivity under accept-all bounds. |
| abbrev review_theorem4_structural_policy_representatives | `review_theorem4_structural_policy_representatives` | - Theorem 4: structural representatives for optimal policies. |
<!-- lean-derived-definitions:end -->

## 14. Named Theorem Statements Checked

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem review_theorem2_multiplicative_policy_shape_ae | `review_theorem2_multiplicative_policy_shape_ae` | - Theorem 2: multiplicative-pricing optimal-policy shape handoff. Lean states the policy-shape clause separately from the explicit non-IC counterexample because the paper's theorem combines a structural statement with an existential exam... |
| theorem review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states | `review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states` | - Theorem 2: explicit multiplicative-pricing instance with positive finite cutoff deviations in both states, and hence measured dynamic non-IC. |
| theorem review_theorem3_feasible_sequential_current_bounds_source_data_statement | `review_theorem3_feasible_sequential_current_bounds_source_data_statement` | Matches the current paper-facing statement. |
<!-- lean-derived-statements:end -->

## 15. Paper-Facing Statement Validator Ledger

Generated from dashboard status export:

`python3 scripts/review_dashboard.py --paper GN21DriverSurgePricing --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| def review_definition_dynamic_defined_reward | `review_definition_dynamic_defined_reward` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): The draft states the paper-facing denominator-valid domain for the dynamic reward formulas: feasible measurable two-state policies with positive accepted-trip mass in each state. |
| def review_definition_dynamic_ic | `review_definition_dynamic_ic` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): The Lean statement expands dynamic incentive compatibility as accept-all weakly optimal among feasible measurable two-state policies, matching the dynamic part of the paper definition. |
| def review_definition_single_state_ic | `review_definition_single_state_ic` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): The Lean statement expands single-state incentive compatibility as accept-all weakly optimal among measurable feasible policies, matching the single-state part of the paper definition. |
| def review_definition_threshold_policy | `review_definition_threshold_policy` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): The draft states exactly the complete weak threshold-policy condition in the paper-facing row: positive trip lengths are accepted iff payment per time is at least the cutoff. |
| abbrev review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds | `review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation states derivative positivity under non-surge accept-all bounds and related assumptions. |
| abbrev review_lemma1_measured_dynamic_reward_decomposition | `review_lemma1_measured_dynamic_reward_decomposition` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation states the dynamic reward as a time-fraction weighted sum of state reward rates. |
| abbrev review_lemma2_switch_probability_formula | `review_lemma2_switch_probability_formula` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation gives the CTMC switch probability formula named in the paper statement. |
| abbrev review_lemma3_measured_time_fraction_formula | `review_lemma3_measured_time_fraction_formula` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation states the time-fraction expression equals the measured time-fraction formula, with nonzero denominator caveats. |
| abbrev review_lemma4_single_state_threshold_uniqueness | `review_lemma4_single_state_threshold_uniqueness` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation captures threshold optimizer existence and uniqueness up to null sets. |
| abbrev review_lemma5_fixed_response_policy_form | `review_lemma5_fixed_response_policy_form` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation captures that an optimal fixed-response feasible policy has the specified form almost everywhere. |
| abbrev review_lemma6_upper_endpoint_derivative_formula | `review_lemma6_upper_endpoint_derivative_formula` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation captures the derivative formula and sign correspondence, though it compresses the displayed derivative. |
| abbrev review_lemma7_affine_positive_additive_response_quasi_convex | `review_lemma7_affine_positive_additive_response_quasi_convex` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation states positive-additive affine response is strictly quasi-convex with explicit sign assumptions. |
| abbrev review_lemma8_affine_negative_additive_response_quasi_concave | `review_lemma8_affine_negative_additive_response_quasi_concave` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation states negative-additive affine response is strictly quasi-concave with explicit sign assumptions. |
| abbrev review_lemma9_surge_derivative_positive_of_acceptAll_bounds | `review_lemma9_surge_derivative_positive_of_acceptAll_bounds` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation states derivative positivity under surge accept-all bounds and related assumptions. |
| abbrev review_proposition3_1_affine_single_state_ic | `review_proposition3_1_affine_single_state_ic` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation states affine single-state renewal reward is incentive compatible under parameter bounds and assumptions. |
| abbrev review_remark1_switch_probability_per_time_strictAntiOn | `review_remark1_switch_probability_per_time_strictAntiOn` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation states strict decrease of switch probability per unit time on positive times. |
| abbrev review_remark3_switch_probability_per_time_tendsto_at_zero | `review_remark3_switch_probability_per_time_tendsto_at_zero` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation states the small-time per-unit switch probability limit equals the switch rate. |
| abbrev review_remark4_switch_time_minus_switch_probability_nonneg | `review_remark4_switch_time_minus_switch_probability_nonneg` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation states lambda*tau minus switch probability is nonnegative under nonnegative time/rate assumptions. |
| abbrev review_section2_single_state_renewal_reward_iid_bridge | `review_section2_single_state_renewal_reward_iid_bridge` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation states the IID renewal-reward convergence bridge to the single-state formula. |
| abbrev review_theorem1_single_state_threshold_best_response | `review_theorem1_single_state_threshold_best_response` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation captures existence of an optimal threshold policy, adding explicit measurability and positivity assumptions. |
| theorem review_theorem2_multiplicative_policy_shape_ae | `review_theorem2_multiplicative_policy_shape_ae` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation matches the stated structural handoff: optimal policies have the described almost-everywhere rejection shapes. |
| theorem review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states | `review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation captures the explicit multiplicative instance with profitable finite cutoff deviations in both states and non-IC. |
| theorem review_theorem3_feasible_sequential_current_bounds_source_data_statement | `review_theorem3_feasible_sequential_current_bounds_source_data_statement` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): The expanded draft exposes the source-data assumptions and the concrete Theorem 3 conclusion rather than only naming an opaque conclusion predicate. |
| abbrev review_theorem4_structural_policy_representatives | `review_theorem4_structural_policy_representatives` | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z) | gpt-5-codex (model; matches; 2026-06-11T03:55:30Z): Translation states existence of structural representatives for optimal policies and that every optimum admits them. |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.
