# LG21 Pickup Note

Last updated: 2026-05-17.

## Current Clean Boundary

- Latest proof commits:
  - `6d87aeb Add LG21 Theorem 3.2 source-witness iff routes`
  - `59b22da Expose LG21 source-witness no-relevance iff routes`
  - `dc9c7f2 Record LG21 Theorem 3.2 raw-surface scope counterexample`
  - `c86c733 Add LG21 raw law-surface scope counterexample`
- Latest local proof bridge:
  full-support/not-all-acting Theorem 3.1 Section 3 PMF and continuous-law
  endpoints now live in `MainTheorems.lean` and the public wrappers delegate to
  them.
- Worktree used for the latest LG21 work:
  `/home/nkgarg/src_wsl/EconCSLean`.
- Expected local dirt in this shared worktree can include unrelated non-LG21
  files from other paper campaigns. Check `git status --short --branch --
  papers/LG21TestOptionalPolicies` before staging.
- Do not use broad staging or index-repair workflows. Stage explicit owned LG21
  paths only.

The latest LG21 commits extended the non-certificate Theorem 3.2
source-witness route. The route now has direct Section 3 wrappers:

- `paper_interface_theorem3_2_section3_fairness_impossibility_of_mixture_and_source_evidence`
- `paper_interface_theorem3_2_section3_no_test_relevance_of_mixture_and_source_evidence`
- `paper_interface_theorem3_2_section3_law_fairness_impossibility_of_observable_implication_and_source_evidence`
- `paper_interface_theorem3_2_section3_law_no_test_relevance_of_observable_implication_and_source_evidence`

It also constructs compact certificate/iff wrappers directly from that
source-witness layer:

- `paper_interface_theorem3_2_fairness_impossibility_certificate_of_mixture_and_source_evidence`
- `paper_interface_theorem3_2_fairness_iff_test_blank_of_mixture_and_source_evidence_observable_identities`
- `paper_interface_theorem3_2_fairness_iff_no_test_relevance_of_mixture_and_source_evidence_observable_identities`
- `paper_interface_theorem3_2_law_fairness_impossibility_certificate_of_observable_implication_and_source_evidence`
- `paper_interface_theorem3_2_law_fairness_iff_test_blank_of_observable_implication_and_source_evidence_observable_identities`
- `paper_interface_theorem3_2_law_fairness_iff_no_test_relevance_of_observable_implication_and_source_evidence_observable_identities`

The matching audit aliases are in `PostPaperAudit.lean`.

The raw-surface scope check
`paper_interface_theorem3_2_raw_surface_scope_counterexample` proves that an
unconstrained `LG21SourcePolicySurface` can be latent-skill fair and observably
fair while not test-blank; `paper_interface_theorem3_2_raw_law_surface_scope_counterexample`
proves the same point for raw continuous-law surfaces. Do not try to prove
Theorem 3.2 over the raw surface alone; the source-witness/strategic-stability
assumptions are necessary for the current model.

The latest Theorem 3.1 bridge moves the full-support/not-all conversion out of
interface-only proof glue:

- `paper_theorem3_1_section3_optional_reporting_law_strategic_withholding_for_every_equilibrium_of_full_support_not_all_and_base_mixed_gaussian_posterior_surface`
- `paper_theorem3_1_section3_report_required_law_strategic_withholding_for_every_equilibrium_of_full_support_not_all_and_base_mixed_affine_skill_posterior_surface`
- `paper_theorem3_1_section3_optional_reporting_strategic_withholding_for_every_equilibrium_of_full_support_not_all_event_share_no_report_mixture`
- `paper_theorem3_1_section3_report_required_strategic_withholding_for_every_equilibrium_of_full_support_not_all_event_share_no_take_mixture`

These derive the positive-mass no-reporter/no-taker complement from full
support of a finite cohort law and an ordinary not-all-acting witness, then feed
the existing finite-event-share Section 3 PMF or continuous-law route.

## Validated Commands

Run from `/home/nkgarg/src_wsl/EconCSLean`:

```bash
lake build LG21TestOptionalPolicies.PostPaperAudit
lake build LG21TestOptionalPolicies
git diff --check -- papers/LG21TestOptionalPolicies/MainTheorems.lean papers/LG21TestOptionalPolicies/PaperInterface.lean papers/LG21TestOptionalPolicies/PostPaperAudit.lean papers/LG21TestOptionalPolicies/README.md papers/LG21TestOptionalPolicies/FINAL_VALIDATION_REPORT.md papers/LG21TestOptionalPolicies/FORMALIZATION_PLAN.md papers/LG21TestOptionalPolicies/START_HERE_NEXT_AGENT.md
```

`lake build LG21TestOptionalPolicies.PostPaperAudit` passed after the PMF
full-support/not-all theorem-layer bridge. Run `lake build
LG21TestOptionalPolicies` again before declaring a final paper closeout.

`HumanStartHere.lean` is not a good LG21 validation target right now: it imports

## Best Next Proof Seam

Do not spend the next pass adding more Theorem 3.2 source-witness aliases unless
an audit file is missing an existing endpoint. The higher-value work is
reducing the remaining conditional status:

1. For Theorem 3.2, decide whether the paper-facing final statement should be
   the current concrete/event-share source-surface theorem or a stricter
   conditional-kernel theorem closer to arbitrary estimation policies. If the
   latter, build the missing conditional-kernel/source-policy bridge explicitly.
2. For Theorem 3.1, the remaining gap is not cutoff algebra. The current route
   has Gaussian/affine threshold and event-share wrappers; the open question is
   whether to make a fully concrete finite PMF surface or keep the continuous
   law certificate as the paper-facing surface.
3. Keep optional full support over all real scores out of the formalization.
   The finite-test full-support route is the correct support statement for
   optional-reporting mapped actors.

## First Commands Next Session

```bash
git status --short --branch -- papers/LG21TestOptionalPolicies
sed -n '1,120p' papers/LG21TestOptionalPolicies/START_HERE_NEXT_AGENT.md
rg -n "Remaining Assumptions|Theorem 3\\.1|Theorem 3\\.2" papers/LG21TestOptionalPolicies/FINAL_VALIDATION_REPORT.md
```
