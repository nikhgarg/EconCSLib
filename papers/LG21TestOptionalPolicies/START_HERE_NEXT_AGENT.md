# LG21 Pickup Note

Last updated: 2026-05-17.

## Current Clean Boundary

- Latest proof commits:
  - `6d87aeb Add LG21 Theorem 3.2 source-witness iff routes`
  - `59b22da Expose LG21 source-witness no-relevance iff routes`
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

## Validated Commands

Run from `/home/nkgarg/src_wsl/EconCSLean`:

```bash
lake build LG21TestOptionalPolicies.PostPaperAudit
lake build LG21TestOptionalPolicies
git diff --check -- papers/LG21TestOptionalPolicies/MainTheorems.lean papers/LG21TestOptionalPolicies/PaperInterface.lean papers/LG21TestOptionalPolicies/PostPaperAudit.lean papers/LG21TestOptionalPolicies/README.md papers/LG21TestOptionalPolicies/FINAL_VALIDATION_REPORT.md papers/LG21TestOptionalPolicies/FORMALIZATION_PLAN.md
```

`lake build LG21TestOptionalPolicies.PostPaperAudit` and the LG21-scoped
`git diff --check` passed before commits `6d87aeb` and `59b22da`.
Run `lake build LG21TestOptionalPolicies` again before declaring a final paper
closeout.

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
