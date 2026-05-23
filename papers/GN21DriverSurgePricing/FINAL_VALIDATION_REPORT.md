# Final Validation Report: Driver Surge Pricing

## Human Verdict

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

## What Has Been Proven

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

## Is Anything in the Paper Wrong?

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

## Did Lean Need a Different Qualitative Proof?

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

## Proof Tricks Worth Reusing

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

## Library Lift Pass

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

## DAG Audit

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

## Human Review Status

`SOURCE_AUDIT.md` records an agent source audit for all 24 paper-interface rows.
That audit checks that the Lean-facing rows correspond to paper-facing source
claims, but it is not human dashboard review.

After clearing the agent-generated local trace, the dashboard precheck reports
`0/24 reviewed`, `24 unreviewed`, `0 stale`, and `0 mismatch`.  This is the
expected state until a human reviewer validates the rows through the dashboard.

## Verification Summary

The paper-local root module and final audit surfaces build successfully:
`GN21DriverSurgePricing`, `GN21DriverSurgePricing.PaperInterface`, and
`GN21DriverSurgePricing.PostPaperAudit`.  The dependency DAG renders, and the
GN21 paper folder has no remaining `sorry`, `admit`, `axiom`, or `by omega`
placeholders in `.lean` files.

The detailed declaration ledger lives in `PostPaperAudit.lean`; the durable
source-to-Lean checklist lives in `SOURCE_AUDIT.md`; and the concise
human-review theorem surface lives in `PaperInterface.lean`.

## Final Status

Lean formalization: complete for the represented paper-facing definitions and
named results.

Human validation: pending.  The next step is dashboard review of the 24
`PaperInterface.lean` rows, not more Lean proof work.
