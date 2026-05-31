# MSVV07AdWords Validation Handoff

## Current Status

MSVV07AdWords has a compiling paper-facing Lean surface for the core finite
AdWords model, Theorem 8 finite and limiting endpoints, Section 6/8 extensions,
the source-shaped Section 6 page-level top-`n_q` multiple-slot rule, Theorem 9
lower-bound endpoints, and the post-paper audit ledger.

The former Section 6 caveat has been closed by
`section6_page_top_balance_theorem8_finite_explicit_error`, which uses the
page-level model in `AdWordsBatch.lean`.

## Validation Commands

Run these before changing the status ledger:

```bash
lake build MSVV07AdWords
lake build
python3 scripts/check_smoke.py --include-papers
python3 scripts/review_dashboard.py --paper MSVV07AdWords --refresh-cache
python3 scripts/review_dashboard.py --paper MSVV07AdWords --precheck
python3 -c "import scripts.audit_repository as a; fs=[f for f in a.run(False, False) if 'MSVV07AdWords' in str(f.path)]; [print(f.format()) for f in fs]; raise SystemExit(1 if fs else 0)"
rg -n '\b(sorry|admit|axiom)\b' papers/MSVV07AdWords.lean papers/MSVV07AdWords --glob '*.lean'
git diff --check
```

The full repository audit may still report unrelated non-MSVV paper-folder
issues. The local `DependencyDAG.pdf` artifact has been regenerated with
`latexmk` and is present for inspection.
