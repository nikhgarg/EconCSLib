# LG21 Pickup Note

Last updated: 2026-05-23.

## Current Boundary

The LG21 paper-facing Lean route is closed under the source models used by the
paper.

- `lake build LG21TestOptionalPolicies` passes.
- `PaperInterface.lean` is intentionally compact: 16 human-review rows covering
  Definitions 1--6, Theorems 3.1--3.2 in optional-reporting/report-required
  forms, Lemma 4.1, Propositions 4.2--4.3, and Theorem 4.4.
- `PostPaperAudit.lean` remains the broad importable audit ledger. It exposes
  the proof-route variants, PMF/law specializations, a.e. repairs, and raw
  arbitrary-policy scope diagnostics.
- `DependencyDAG.tex` is source-facing and follows the shared template styles:
  definitions/model layers use `dag_model`, supporting lemmas use `dag_lemma`,
  and paper results use `dag_result`. The current PDF has had a spacing pass;
  it should not be expanded with theorem-route variants.
- `SOURCE_AUDIT.md` is the standalone agent source-surface audit. It maps the
  16 compact interface rows to local source-cache line numbers and audit
  endpoints.
- Human dashboard review remains external: `review-dashboard.sh --check`
  reports `0/16 reviewed`, with no stale or mismatch entries.
- Library pass status: the a.e. positive-failure-mass contradiction and
  positive-measure subset lemmas were lifted to
  `EconCSLib.Foundations.Probability.MeasureInequalities`; LG21 keeps thin
  wrappers around those generic lemmas.

## What Not To Reopen

- Do not treat the raw arbitrary-policy counterexamples as paper-theorem
  caveats. They show that an overbroad abstraction is false; the source-model
  paper route is closed.
- Do not re-expand `PaperInterface.lean` with every `PostPaperAudit` alias.
  The compact interface is the human review surface; proof-route details belong
  in `PostPaperAudit.lean`, `ProofInterface.lean`, or theorem route files.
- Do not use `git restore`, `git reset`, broad staging, or index-repair
  workflows in this shared worktree.

## Validation Commands

Run from `/home/nkgarg/src_wsl/EconCSLean`:

```bash
lake build LG21TestOptionalPolicies
rg -n "\bsorry\b|\badmit\b|\baxiom\b|\bunsafe\b" papers/LG21TestOptionalPolicies --glob '*.lean'
git diff --check -- papers/LG21TestOptionalPolicies docs/ECONCSLEAN_CURRENT_STATUS.md scripts/audit_repository.py skills/econcs-formalizer
papers/LG21TestOptionalPolicies/review-dashboard.sh --check
```

Expected dashboard status until a human saves reviews:

```text
Review status for LG21TestOptionalPolicies: 0/16 reviewed, 16 need attention (0 stale, 16 unreviewed, 0 mismatch).
```

`python3 scripts/audit_repository.py --include-active` currently has no
in the repository.

## Remaining Work

For this paper, only external human review and normal publication-style cleanup
remain. If a future proof agent continues anyway, the highest-value tasks are:

1. Inspect the 16 `PaperInterface.lean` rows against local source caches.
2. If a row is too opaque for human comparison, improve that single row without
   adding proof-route aliases.
3. Keep README, `FINAL_VALIDATION_REPORT.md`, and `DependencyDAG.tex` aligned
   with the compact interface and the all-green source-model status.
4. If another generic proof utility appears, lift only a small targeted lemma
   with a clear `EconCSLib` destination and build-verify it.
