# Final Validation Report: Driver Surge Pricing

## 1. Human Verdict

- Lean formalization status: partially formalized
- Human dashboard review status: 0/24 rows reviewed; 0 stale; 0 mismatches.
- Main caveat: none for the named paper-facing results.  Theorem 3 is stated
  on the denominator-valid defined-reward domain used by the Appendix D
  reward-rate formulas; broader totalized real-division behavior at zero
  denominators is audit-only.

The GN21 driver-surge paper is complete at the Lean proof level for the
paper-facing definitions and named results represented in
`PaperInterface.lean`.  The remaining non-Lean task is human signoff in the
review dashboard; the dashboard should currently show `0/24` rows reviewed
until a human reviewer saves those rows.

The formalization did not find a false main theorem.  It did make one implicit
domain convention explicit: Appendix D reward rates divide by accepted-trip
mass/time quantities.  The compact paper-facing Theorem 3 row therefore uses
`DynamicDefinedReward.of_total`, so policies are compared exactly where the
paper's reward-rate expressions are defined.  Separate obstruction lemmas record
why a broader totalized real-valued division shortcut would need extra
hypotheses, but that shortcut is not part of the named Theorem 3 endpoint.

Lean footprint: the paper folder contains 142,478 lines of paper-local Lean
code across 13 `.lean` files.  The human-review surface is deliberately much
smaller: `PaperInterface.lean` is 379 lines and exposes 24 dashboard rows.

<!-- transitive-source-premise-audit:start -->
### Transitive Source-Premise Audit

The strengthened recursive source-premise audit does not yet pass for full-status provenance. It follows paper-local wrappers and reusable-library certificate APIs, and treats certificate/source-row/external-boundary premises as full-status blockers unless they are derived internally or routed through validated paper assumptions.

Current result: the compact endpoint still reaches boundary interval, a.e. policy-shape, optimizer-replacement, and sequential dynamic-reward certificates; the denominator-valid defined-reward theorem is formalized, but the full certificate provenance is not yet derived from primitives.
<!-- transitive-source-premise-audit:end -->

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
  bounds, then choose the non-surge price via Lemma 10.  The compact
  paper-facing statement constructs prices of the form
  `m_i tau + z_i q_{i->j}(tau)`, proves defined-reward dynamic incentive
  compatibility, and proves accept-all uniqueness up to null sets on the
  positive-denominator source domain used by the paper's reward-rate formulas.

## 4. Paper Definitions Checked

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| def review_definition_single_state_ic | `review_definition_single_state_ic` | uncertain. Paper-facing statement only names the definition; the translation is tautological and too compressed to verify contents. |
| def review_definition_dynamic_ic | `review_definition_dynamic_ic` | uncertain. Paper-facing statement only names the definition; the translation does not expose the dynamic IC condition. |
| def review_definition_threshold_policy | `review_definition_threshold_policy` | uncertain. Paper-facing statement only names threshold policies; the translation references a predicate without enough content to judge. |
| def review_definition_dynamic_defined_reward | `review_definition_dynamic_defined_reward` | uncertain. Paper-facing statement only names positive-mass denominators; the translation is a type-level description without details. |
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

## 5. Named Theorem Statements Checked

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem review_theorem2_multiplicative_policy_shape_ae | `review_theorem2_multiplicative_policy_shape_ae` | - Theorem 2: multiplicative-pricing optimal-policy shape handoff. Lean states the policy-shape clause separately from the explicit non-IC counterexample because the paper's theorem combines a structural statement with an existential exam... |
| theorem review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states | `review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states` | - Theorem 2: explicit multiplicative-pricing instance with positive finite cutoff deviations in both states, and hence measured dynamic non-IC. |
| theorem review_theorem3_defined_reward_source_statement | `review_theorem3_defined_reward_source_statement` | matches. The Lean row matches the fully incentive-compatible accept-all clause of Theorem 3 on the source-domain where Appendix D reward-rate denominators are defined. Lean states this as defined-reward dynamic IC and a.e. uniqueness rather than as totalized real division at zero denominators. |
<!-- lean-derived-statements:end -->

## 6. Paper-Facing Statement Validator Ledger

Generated from dashboard status export:

`python3 scripts/review_dashboard.py --paper GN21DriverSurgePricing --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| def review_definition_dynamic_defined_reward | `review_definition_dynamic_defined_reward` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:34Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:34Z): Paper-facing statement only names positive-mass denominators; the translation is a type-level description without details. |
| def review_definition_dynamic_ic | `review_definition_dynamic_ic` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:34Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:34Z): Paper-facing statement only names the definition; the translation does not expose the dynamic IC condition. |
| def review_definition_single_state_ic | `review_definition_single_state_ic` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:34Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:34Z): Paper-facing statement only names the definition; the translation is tautological and too compressed to verify contents. |
| def review_definition_threshold_policy | `review_definition_threshold_policy` | gpt-5-codex (model; uncertain; 2026-06-06T20:39:34Z) | gpt-5-codex (model; uncertain; 2026-06-06T20:39:34Z): Paper-facing statement only names threshold policies; the translation references a predicate without enough content to judge. |
| abbrev review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds | `review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation states derivative positivity under non-surge accept-all bounds and related assumptions. |
| abbrev review_lemma1_measured_dynamic_reward_decomposition | `review_lemma1_measured_dynamic_reward_decomposition` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation states the dynamic reward as a time-fraction weighted sum of state reward rates. |
| abbrev review_lemma2_switch_probability_formula | `review_lemma2_switch_probability_formula` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation gives the CTMC switch probability formula named in the paper statement. |
| abbrev review_lemma3_measured_time_fraction_formula | `review_lemma3_measured_time_fraction_formula` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation states the time-fraction expression equals the measured time-fraction formula, with nonzero denominator caveats. |
| abbrev review_lemma4_single_state_threshold_uniqueness | `review_lemma4_single_state_threshold_uniqueness` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation captures threshold optimizer existence and uniqueness up to null sets. |
| abbrev review_lemma5_fixed_response_policy_form | `review_lemma5_fixed_response_policy_form` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation captures that an optimal fixed-response feasible policy has the specified form almost everywhere. |
| abbrev review_lemma6_upper_endpoint_derivative_formula | `review_lemma6_upper_endpoint_derivative_formula` | gpt-5-codex (model; matches; 2026-06-12T18:05:00Z) | gpt-5-codex (model; matches; 2026-06-12T18:05:00Z): Translation captures the derivative formula and the conditional strict sign correspondence: the derivative identity itself does not assume positive endpoint density, while strict sign transfer is conditional on positive endpoint density. |
| abbrev review_lemma7_affine_positive_additive_response_quasi_convex | `review_lemma7_affine_positive_additive_response_quasi_convex` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation states positive-additive affine response is strictly quasi-convex with explicit sign assumptions. |
| abbrev review_lemma8_affine_negative_additive_response_quasi_concave | `review_lemma8_affine_negative_additive_response_quasi_concave` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation states negative-additive affine response is strictly quasi-concave with explicit sign assumptions. |
| abbrev review_lemma9_surge_derivative_positive_of_acceptAll_bounds | `review_lemma9_surge_derivative_positive_of_acceptAll_bounds` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation states derivative positivity under surge accept-all bounds and related assumptions. |
| abbrev review_proposition3_1_affine_single_state_ic | `review_proposition3_1_affine_single_state_ic` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation states affine single-state renewal reward is incentive compatible under parameter bounds and assumptions. |
| abbrev review_remark1_switch_probability_per_time_strictAntiOn | `review_remark1_switch_probability_per_time_strictAntiOn` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation states strict decrease of switch probability per unit time on positive times. |
| abbrev review_remark3_switch_probability_per_time_tendsto_at_zero | `review_remark3_switch_probability_per_time_tendsto_at_zero` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation states the small-time per-unit switch probability limit equals the switch rate. |
| abbrev review_remark4_switch_time_minus_switch_probability_nonneg | `review_remark4_switch_time_minus_switch_probability_nonneg` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation states lambda*tau minus switch probability is nonnegative under nonnegative time/rate assumptions. |
| abbrev review_section2_single_state_renewal_reward_iid_bridge | `review_section2_single_state_renewal_reward_iid_bridge` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation states the IID renewal-reward convergence bridge to the single-state formula. |
| abbrev review_theorem1_single_state_threshold_best_response | `review_theorem1_single_state_threshold_best_response` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation captures existence of an optimal threshold policy, adding explicit measurability and positivity assumptions. |
| theorem review_theorem2_multiplicative_policy_shape_ae | `review_theorem2_multiplicative_policy_shape_ae` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation matches the stated structural handoff: optimal policies have the described almost-everywhere rejection shapes. |
| theorem review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states | `review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation captures the explicit multiplicative instance with profitable finite cutoff deviations in both states and non-IC. |
| theorem review_theorem3_defined_reward_source_statement | `review_theorem3_defined_reward_source_statement` | gpt-5-codex (model; matches; 2026-06-12T18:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T18:00:00Z): The Lean row matches the fully incentive-compatible accept-all clause of Theorem 3 on the source-domain where Appendix D reward-rate denominators are defined. Lean states this as defined-reward dynamic IC and a.e. uniqueness rather than as totalized real division at zero denominators. |
| abbrev review_theorem4_structural_policy_representatives | `review_theorem4_structural_policy_representatives` | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:34Z): Translation states existence of structural representatives for optimal policies and that every optimum admits them. |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.

## 7. Paper Assumption Provenance

> Strict premise-source audit update (2026-06-12): `assumption_match_llm.json`
> now records per-premise judgments for this paper's `Assumptions.lean` ledger.
> Current result: every explicit premise is judged source text, source primitives,
> direct source-derived conditions, or explicit paper/local-calculus
> conditions. The Lemma 6 upper-endpoint row now proves the exact derivative
> identity without assuming positive endpoint density; positive density is only
> the conditional premise for strict sign transfer. The Theorem 1/Lemma 4
> positive accept-all payment premise is now
> derived from the source proof branch with nonnegative on-trip rates and
> positive mass on positive payouts.
> This note supersedes any older group-level wording in this section.

Every paper-facing premise is routed through
`GN21DriverSurgePricing/Assumptions.lean` and checked by
`assumption_match_llm.json`. The assumption ledger separates source-domain
theorem conditions from remaining proof-route boundaries; the latter are not
counted as paper assumptions.

| Lean assumption/condition | Judgment | Source role |
| --- | --- | --- |
| `assumption_affine_single_state_parameter_domain` | paper condition | Proposition 3.1 affine single-state parameter domain. |
| `assumption_single_state_defined_reward_domain` | paper condition | Theorem 1/Lemma 4 single-state domain: nonnegative on-trip rates are stated in the Appendix C.2 proof table, finite accept-all mass is source-derived from the probability-measure domain, and the positive-payout-mass branch matches the source proof's nonzero-payout case. Lean derives positive accept-all expected payment from these premises. |
| `assumption_dynamic_time_fraction_denominators` | paper condition | Lemma 3 dynamic time-fraction denominators. |
| `assumption_switch_rate_domain` | paper condition | CTMC switch-rate positivity/nonzero total intensity. |
| `assumption_fixed_response_policy_form_conditions` | paper condition | Lemma 5 measurable optimal fixed-response policy condition. |
| `assumption_upper_endpoint_derivative_domain` | paper condition | Lemma 6 upper-endpoint derivative formula domain; the exact derivative identity no longer assumes positive endpoint density, and strict sign transfer is conditional on positive density inside the theorem conclusion. |
| `assumption_affine_response_shape_domains` | paper condition | Lemmas 7--8 affine response sign domains. |
| `assumption_surge_derivative_source_bounds` | paper condition | Lemma 9 surge-state source formulas and current bounds over the derivative certificate fields; no certificate-field renaming premise remains exposed. |
| `assumption_nonsurge_derivative_source_bounds` | paper condition | Lemma 10 non-surge source formulas and current bounds over the derivative certificate fields; no certificate-field renaming premise remains exposed. |
| `assumption_theorem3_source_data_domain` | paper condition | Theorem 3 positive values, arrivals, switches, and accept-all masses. |

Additional assumptions beyond the paper: none affecting the named paper
results. Lemma 6 no longer exposes pointwise endpoint-density positivity as a
premise of the derivative formula; Lean proves the exact derivative identity
first and only derives strict sign transfer conditionally when density is
positive.  Theorem 3's positive-denominator condition is the source domain of
the Appendix D reward-rate formulas, and is exposed in the defined-reward
statement rather than hidden as a certificate.

## 8. Proof-Strategy Deviations

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

- Theorem 3 separates defined-reward positive-mass reasoning from optional
  totalized zero-mass extensions.  The compact paper-facing theorem uses the
  defined-reward source domain; Lean also records obstruction lemmas showing
  that an overbroad zero-mass-dominance certificate would be false without
  extra hypotheses.

- Theorem 2's "not incentive compatible" clause is witnessed by a concrete
  measured atomic instance, so the existential counterexample is inspectable.

## 9. Proof Tricks Worth Reusing

- Work directly in the continuous/measure-theoretic model when the source proof
  is continuous.  The finite-support model was useful as support, but the paper
  closed only after the proof focused on measurable trip-length sets,
  integrals, and a.e. policy equality.

- State positive-denominator domains early.  The biggest avoidable delay was
  discovering that the paper's reward-rate notation assumes accepted-trip
  mass/time denominators are meaningful, while Lean's real division totalizes
  zero denominators.  This should have been surfaced earlier as a human-facing
  source-domain decision: prove the intended defined-reward theorem now,
  expose the denominator-valid domain, and only then decide whether an
  all-feasible zero-mass totalization strengthening is worth pursuing.

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

## 10. Library Lift Pass

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

- Positive-denominator defined-reward interfaces: papers with ratios should
  have a reusable API so source semantics do not depend on Lean's totalized
  real division at zero.

- Atomic continuous-measure reductions: weighted Dirac and finite atomic
  set-integral simplification lemmas would make future continuous
  counterexample constructions much faster.

The GN21 paper-local definitions remain formula-explicit.  They are not opaque
aliases to generic library constants; instead the paper wrappers call the
library lemmas with `simpa` compatibility bridges.  This preserves the human
review surface and avoids destabilizing the long compiled proof.

## 11. DAG Audit

I rerendered and visually inspected `DependencyDAG.pdf` after this pass.  The
current DAG uses the shared preamble, has visible spacing between nodes, and no
arrow or label crosses through a node body.

The DAG was made more paper-facing: the disconnected finite-MDP implementation
support box was removed, the appendix Remarks 1, 3, and 4 are now explicit, and
Theorem 2 is represented by one combined paper-facing box instead of separate
shape and counterexample boxes.  Optional zero-mass totalization is documented
in this report rather than shown as a named paper result in the DAG.  The
remaining boxes correspond to the paper-facing model, Section 2.2 renewal-reward bridge, named
lemmas/proposition/theorems, and the paper proof flow.

## 12. Conditional Results and Remaining Gaps

None separately recorded in the existing report.

## 13. Suspected Paper Errors or Inconsistencies

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

## 14. Validation Checks

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

Audit date: 2026-06-12.
Scope: current dashboard rows from `PaperInterface.lean`; `lean_to_tex_llm.json` records context-free Lean-to-TeX drafts and `statement_match_llm.json` records the context-free paper-vs-translation judgment.

Summary: 34 rows; 34 match, 0 uncertain, 0 mismatch, 0 missing. Stale sidecar
rows: none. The 34 rows consist of 24 paper-interface rows plus 10 typed
assumption-provenance rows. The row-local statement match lane is clean, but it
does not certify theorem-premise provenance; that is handled by the strict
assumption audit above.

## 15. Final Verdict

### Final Status

Lean formalization: formalized. The represented paper-facing definitions and
named results compile, and every explicit proof premise is source-matched,
source-derived, or listed as an explicit paper/local-calculus condition in the
assumption ledger. The Lemma 6 derivative formula has been strengthened so
endpoint-density positivity is no longer a theorem premise; it appears only as
the conditional hypothesis for strict sign transfer.

Human validation: pending.  The next step is dashboard review of the 24
`PaperInterface.lean` rows, not more Lean proof work.

- Completion status: formalized.
- Summary: Named CTMC lemmas and Theorems 1--4 are exposed, with all
  explicit premises source-matched, source-derived, or recorded as explicit
  paper/local-calculus conditions.
