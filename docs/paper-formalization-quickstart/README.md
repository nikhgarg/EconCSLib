# Paper Formalization Quickstart

This is the short human-facing guide for starting or steering an EconCSLib
paper formalization. Detailed agent rules live in
[`../AGENT_FORMALIZATION_WORKFLOW.md`](../AGENT_FORMALIZATION_WORKFLOW.md) and
[`../../skills/econcs-formalizer/SKILL.md`](../../skills/econcs-formalizer/SKILL.md).

## Executive Summary

Start with a precise source and a precise goal. Give the agent both the
arXiv/open version and the official/published source when both exist, then ask
for source intake and target setting before proof work.

Starter prompt:

```text
Get context on this repo and use the econcs-formalizer skill. Start formalizing
<paper title>.

Sources:
- arXiv/open version: <url>
- official/published version: <url, if available>

Goal: <fully formalize / formalize to closeout / make a public partial
formalization with only <specific boundary> left>.

First do the intake pass: identify the exact source version, cache the
source/PDF/TeX locally if needed, list every paper definition and named
theorem-like result, sanity-check formulas and dependencies, check reusable
Mathlib/CSLib/Optlib/EconCSLib APIs, and write FORMALIZATION_PLAN.md before
deep Lean proof work.
```

For long jobs, set a durable goal:

```text
/goal fully formalize <PaperFolder> to closeout, including README,
PaperInterface, DependencyDAG, status.json, and FINAL_VALIDATION_REPORT.
```

Useful steering rules:

- Source first: official URL, arXiv/open URL, local cache, and source-version
  mismatches should be explicit.
- Target first: make a compact `PaperInterface.lean` skeleton and run
  statement/premise checks before expensive proof loops.
- Prove from source primitives. If a boundary remains, make it the smallest
  named theorem, certificate, or library lemma needed.
- Use `partially formalized` in public docs when a boundary remains; name the
  boundary in one plain sentence.
- Keep human docs current at milestones. DAGs and reports should use paper
  concepts, not Lean function names.
- Final reports should put the human verdict, paper issues/errors, additional
  assumptions or boundaries, proof deviations, reusable tricks, and closeout
  status before Lean checklist details.
- Run full closeout only when the paper is actually done or intentionally
  public-partial; otherwise use targeted builds and audits.

See [`DETAILS.md`](DETAILS.md) for prompt variants and the closeout checklist.
