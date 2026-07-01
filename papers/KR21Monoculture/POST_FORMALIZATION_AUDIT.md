# Post-Formalization Audit: KR21 Monoculture

## Scope
This audit records the closeout state for *Algorithmic Monoculture and Social Welfare* by Jon Kleinberg and Manish Raghavan. The source version is arXiv:2101.05853 / PNAS 2021, with local source cache under `papers/KR21Monoculture/sources/`.

Current status: formalized. Theorem 1, Theorem 2, Theorem 3, Theorem 4, Appendix A scaled-noise consequences, Appendix C Gaussian/Laplace routes, and the concrete Mallows family route are exposed through `PaperInterface.lean` and summarized in `FINAL_VALIDATION_REPORT.md`.

## Source Note
Appendix C Lemma 1 states global strict Laplacian well-ordering. Lean proves the globally valid weak Laplacian form, and also proves strict overlap/local forms where strictness is available. The downstream Laplace route is proved from the weak comparison plus the later strict support/monotonicity ingredients.

No named theorem or main-text result is affected. This note is not an additional assumption, not a paper-level caveat, and not an external theorem boundary.

The focused math note `LAPLACIAN_LEMMA1_SOURCE_NOTE.md` records the paper statement, the Lean-proved statement, and the all-positive concrete counterexample `a = 11, b = 10, c = 2, d = 1` for the global strict Laplacian claim.

## Review Surface
`PaperInterface.lean` has 65 exported declarations:

- 49 reviewed paper-facing rows in `status.json`;
- 16 auxiliary proof-route rows for explicit boundary helpers, certificates, packages, and intermediate wrappers.

The reviewed rows cover the paper-facing definitions, Appendix A/RUM route, Appendix C Gaussian/Laplace route, Theorems 1--4, and Theorem 9. Auxiliary rows are not counted as final theorem boundaries.

## DAG Audit
Closeout artifacts:

- `FINAL_VALIDATION_REPORT.md`
- `DependencyDAG.tex`
- `DependencyDAG.pdf`

`DependencyDAG.tex` uses the shared TikZ preamble. The rendered `DependencyDAG.pdf` was produced from the paper folder and visually inspected via PNG conversion for overlap, stale open-boundary labels, and Lean-code-facing node text. The diagram is paper-facing and records the paper-facing result flow as formalized; the Laplacian Lemma 1 strict-vs-weak distinction is documented in this audit note rather than as a theorem-status caveat.

## Library Extraction Review
Reusable support has been lifted into shared ranking, Mallows, finite-expectation, finite-sum, monotone-continuity, conditional-probability, measure-inequality, and random-utility modules where the proof work created reusable infrastructure. KR21 keeps paper-shaped wrappers for theorem numbering, source-note handling, and review surface clarity.

## Commands
Build command:

```bash
lake build KR21Monoculture.PaperInterface
```

Targeted closeout audit:

```bash
python3 scripts/audit_repository.py --paper KR21Monoculture --paper-closeout --include-active --info-limit 0
```

The closeout command is rerun after KR21 report, status, source-record sidecar, or DAG edits until it reports no KR21-specific errors or warnings.
