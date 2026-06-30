# Paper Formalization Details

## Prompt Variants

New paper intake:

```text
Do new paper intake for <paper title>, and your goal is to fully formalize it.
Use <arXiv URL>. The official source is <official URL> for documentation.
Start with source/version inventory, named-result ledger, formula sanity pass,
shared-library reuse checkpoint, and FORMALIZATION_PLAN.md.
```

Resume a paper:

```text
Resume <PaperFolder>. First read the skill, the paper README,
FINAL_VALIDATION_REPORT.md, PaperInterface.lean, FORMALIZATION_PLAN.md, and the
current status.json. Tell me the exact remaining proof boundary, then keep
going until the paper is formalized or the boundary is reduced to one named
library theorem/certificate.
```

Public partial target:

```text
Clean this up as a public partial formalization. Derive everything possible
from source-model primitives. The only remaining work should be the smallest
explicit boundary: <one sentence>. Make the README, DAG, status, and final
report human-facing.
```

## Intake Checklist

- Record `Paper`, `Authors`, `Version formalized`, `Official URL`, and
  `Public PDF` in the paper README.
- Prefer source TeX for formulas, theorem labels, equation numbers, appendix
  proof steps, and version disputes. Use PDF text mainly for orientation.
- Fill the initial `FORMALIZATION_PLAN.md` before deep proof work: source
  inventory, named-result ledger, formula/dependency sanity pass, reusable API
  checkpoint, formal target map, and fallback boundaries.
- Build a small paper-facing interface first. A broad package row or
  source-looking certificate is not a substitute for matching each visible
  theorem/formula target.

## During Proof Work

- Search Mathlib, CSLib, Optlib, and existing `EconCSLib` APIs before creating
  a local wrapper around a standard concept.
- Keep `PaperInterface.lean` readable: definitions and named source results
  belong there; implementation helpers belong in `MainTheorems.lean`,
  `ProofInterface.lean`, or local proof files.
- A paper result is fully formalized only when non-derived premises are either
  proved from source primitives or listed as validated paper-source
  assumptions. Hidden certificate, replay, process, bridge, or source-record
  fields should be audited recursively.
- Subagents are allowed for scouting, independent proof regions, audit cleanup,
  CI, and release tasks. Ask them for exact files, declarations, and next
  lemmas, not broad summaries.
- Do not run the full closeout workflow just because an unfinished paper
  changed. Use targeted `lake build` commands and row-scoped checks until a
  real closeout or handoff point.

## Human-Facing Standards

- Put current status first. Avoid history markers like "no longer done" in
  human-facing docs.
- Write one-sentence status summaries when possible, for example: "Full
  formalization requires a homogeneous Poisson process and stopping-time
  derivation."
- DAGs should be paper-facing and visually readable. Avoid Lean declaration
  names, oversized boxes, and overlapping arrows.
- Reports should start with what a paper author or researcher needs: verdict,
  paper issues or none found, additional assumptions or proof boundaries,
  proof-strategy deviations, and reusable proof ideas.
- Do not call a source assumption a caveat. Use kind, precise caveat language
  only for real source discrepancy, ambiguity, or proof-boundary issues.
- For public tables, avoid separate `conditional` terminology; use
  `partially formalized` and name the exact remaining boundary.

## Closeout Checklist

At real completion or public-partial handoff, update:

- `README.md`
- `PaperInterface.lean`
- `DependencyDAG.tex` and rendered DAG if tracked
- `status.json`
- `FINAL_VALIDATION_REPORT.md`
- reusable-library notes or extracted APIs, when applicable

Then run the relevant checks from the repository root:

```bash
lake build <paper target>
python3 scripts/sync_paper_status.py --check
python3 scripts/audit_repository.py --paper <paper> --paper-closeout --include-active --info-limit 0
git diff --check
```

Before claiming a public-ready branch, run the broader public-release checks
listed in [`../AGENT_FORMALIZATION_WORKFLOW.md`](../AGENT_FORMALIZATION_WORKFLOW.md).
