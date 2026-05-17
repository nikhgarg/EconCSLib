# LG21 Pickup Note

Last updated: 2026-05-17.

## Current Clean Boundary

- Latest proof commit: `64010e7 Add LG21 source-witness Section 3 routes`.
- Worktree used for the latest LG21 work: `/tmp/econcslean-lg21-next`.
- Expected local dirt after checkout/worktree use: untracked `.lake` cache only.
- Do not use broad staging or index-repair workflows. Stage explicit owned LG21
  paths only.

The latest commit added direct Section 3 wrappers for the non-certificate
Theorem 3.2 source-witness routes:

- `paper_interface_theorem3_2_section3_fairness_impossibility_of_mixture_and_source_evidence`
- `paper_interface_theorem3_2_section3_no_test_relevance_of_mixture_and_source_evidence`
- `paper_interface_theorem3_2_section3_law_fairness_impossibility_of_observable_implication_and_source_evidence`
- `paper_interface_theorem3_2_section3_law_no_test_relevance_of_observable_implication_and_source_evidence`

The matching audit aliases are in `PostPaperAudit.lean`.

## Validated Commands

Run from `/tmp/econcslean-lg21-next`:

```bash
lake build LG21TestOptionalPolicies.PostPaperAudit
lake build LG21TestOptionalPolicies
git diff --check -- papers/LG21TestOptionalPolicies/MainTheorems.lean papers/LG21TestOptionalPolicies/PaperInterface.lean papers/LG21TestOptionalPolicies/PostPaperAudit.lean papers/LG21TestOptionalPolicies/README.md papers/LG21TestOptionalPolicies/FINAL_VALIDATION_REPORT.md papers/LG21TestOptionalPolicies/FORMALIZATION_PLAN.md
```

All three passed before commit `64010e7`.

`HumanStartHere.lean` is not a good LG21 validation target right now: it imports

## Best Next Proof Seam

Do not spend the next pass adding more Theorem 3.2 aliases unless an audit file
is missing an existing endpoint. The higher-value work is reducing the
remaining conditional status:

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
git -C /tmp/econcslean-lg21-next status --short
sed -n '1,120p' papers/LG21TestOptionalPolicies/START_HERE_NEXT_AGENT.md
rg -n "Remaining Assumptions|Theorem 3\\.1|Theorem 3\\.2" papers/LG21TestOptionalPolicies/FINAL_VALIDATION_REPORT.md
```
