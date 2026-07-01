# Final Validation Report: PRPKG24 Accuracy-Diversity

## 1. Human Verdict
Formalized. The paper-facing surface covers the main examples, definitions,
theorems, corollaries, propositions, and appendix lemmas listed below.
Source-quality notes remain for Proposition 2's printed finite constant and
Lemma D.1(i)'s sign convention; Proposition 4 is treated as validated for the
concrete sphere endpoint rather than as a caveat. No human dashboard sign-off
has been recorded. The automated statement judge marks Proposition 2 as a
mismatch because Lean uses the corrected finite constant.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: The accuracy-diversity paper surface is checked, with
  source-quality notes recorded separately from proof boundaries.

## 3. Source and Scope
- Paper: *Reconciling the Accuracy-Diversity Trade-off in Recommendations*.
- Authors: Kenny Peng, Manish Raghavan, Emma Pierson, Jon Kleinberg, and Nikhil Garg.
- Source version: The ACM Web Conference, 2024 metadata plus local arXiv:2307.15142v1 text cache.
- Local source text: `papers/PRPKG24AccuracyDiversity/PRPKG24AccuracyDiversity.txt`.
- Lean folder: `papers/PRPKG24AccuracyDiversity`.
- Human-facing theorem file: `papers/PRPKG24AccuracyDiversity/PaperInterface.lean`.
- Detailed audit notes: `papers/PRPKG24AccuracyDiversity/POST_FORMALIZATION_AUDIT.md`.
- DAG artifacts: `papers/PRPKG24AccuracyDiversity/DependencyDAG.tex` and `papers/PRPKG24AccuracyDiversity/DependencyDAG.pdf`.

## 4. Researcher Summary of Checked Results
- The paper-facing surface covers the main examples, definitions, theorems, corollaries, propositions, and appendix lemmas.
- Proposition 2 is closed for the asymptotic homogeneity conclusion via the corrected finite constant.
- Proposition 4 is validated for the concrete sphere endpoint, with source-quality notes recorded separately from proof boundaries.

## 5. Remaining Boundaries and Gaps
None for the checked theorem conclusions; source-quality notes are recorded below.

## 6. Additional Assumptions Beyond Paper
- None. Proposition 2's corrected finite constant is a source-quality note, not
  an added model assumption.

## 7. Proof-Strategy Deviations
- None

## 8. Proof Tricks Worth Reusing
- None

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
- Proposition 2: the printed finite constant appears to miss a factor of 2. Lean proves the corrected finite `(2m+1)/N` bound, which is sufficient for the paper's asymptotic conclusion. The automated statement judge records this as a mismatch.
- Lemma D.1(i): the literal printed sign convention combines `B > 0` with `sigma < 0`, while the proof route and downstream exponential-decay application use the source-consistent positive-rate/decay convention. Lean closes the optimizer-limit content and downstream routes under that convention.

## 10. Paper Issues or Caveats
No paper-level formalization caveat is claimed from the source-quality notes above. Proposition 2's corrected finite constant is sufficient for the paper's asymptotic conclusion, and the Lemma D.1 optimizer-limit content used downstream is closed under the source-consistent convention.

## 11. Detailed Formalization Evidence
The current paper interface exposes source-shaped statements rather than proof-internal certificates. In particular:

- Definitions 1-3 and Example 1 are exposed at the paper-facing equation/interface level.
- Theorem 1 covers the finite-discrete, bounded, exponential, Pareto, and all-consumed/common-mean branches, with Corollary 1's model-witness split.
- Theorem 2 covers the decaying-Bernoulli top-one regimes and the all-consumed alpha-zero argmax interpretation.
- Theorem 3 proves the varying-success log-share limit and all-consumed argmax endpoint from primitive Bernoulli probability assumptions.
- Proposition 2 proves the homogeneity conclusion from the corrected finite `(2m+1)/N` bound.
- Proposition 4 proves the concrete continuous-sphere endpoint using the unit sphere, normalized Haar-sphere uniform measure, linear-isometry transitivity, radial log-kernel symmetry, Fubini/integrability facts, compact maximizer, and positive-Laplace-defined objective route.
- Proposition 5, Lemma 1, and Lemmas D.1-D.5 are exposed through source-shaped paper rows.

## 12. Assumption And Validation Notes
All visible paper assumptions are routed through `Assumptions.lean` and the current `assumption_match_llm.json` sidecar. There are 15 assumption/provenance rows; all are judged current, with 56 premise-level judgments and no unresolved or partial-boundary premises.

The Proposition 4 row `assumption_proposition4_continuous_sphere_laplace_boundary` is a validation-note row, not an external proof boundary. It records:

- `hp : Continuous q`, the regularity used by the formal Laplace route;
- positivity of the radial function on `[0,2]`, aligned with the paper's `(0,1]` codomain;
- the reading of the paper's displayed `Gamma` limit as the Laplace-defined compact-supremum objective used by the Lean endpoint.

## 13. Statement Validator Ledger
The current validator sidecars are:

- `lean_to_tex_llm.json`
- `statement_match_llm.json`
- `assumption_match_llm.json`
- `review_surface_llm.json`

Current dashboard checks:

- Statement lane: 27 paper-result rows, 41 Lean-to-TeX drafts, 41 statement-judge rows, no missing or stale items. Proposition 2 is recorded as a conditional-boundary mismatch with human override because the corrected finite constant differs from the printed finite bound while preserving the asymptotic conclusion.
- Assumption lane: 15 assumption declarations, no missing/stale/flagged items.
- Review surface lane: 42 rows, current `review_surface_llm.json`, no stale surface audit.
- Combined dashboard precheck: no stale checks; the only remaining attention items are the 42 absent manual dashboard review entries.

The current full validator table can be regenerated with:

```bash
python3 scripts/review_dashboard.py --paper PRPKG24AccuracyDiversity --export-format validators-md
```

## 14. DAG Audit
`DependencyDAG.tex` was audited against the workflow. Definition 1 is green and now covers both equation (5) for finite real `gamma` and the `gamma = infinity` likelihood-argmax profile, Proposition 4 appears once as a formalized result node, the header records the ACM Web Conference 2024 venue while pointing to the arXiv source cache, and the rendered layout has no node/text overlap. `pdflatex` wrote `DependencyDAG.pdf`, but the local MiKTeX wrapper still exits with code 134 after trying to write user config/log files under read-only `~/.miktex`; `mutool draw` was used for PNG rendering and visual inspection.

## 15. Library Lift Pass
Reusable infrastructure used by this proof already lives in shared recommender, finite-rounding, asymptotics, order-statistics, exponential, Pareto, real-distribution, large-deviation, and symmetry modules. No additional library extraction was made in this closeout pass.

The library-only premise audit was clean:

```bash
python3 scripts/audit_repository.py --library-only --library-premise-audit --info-limit 0
```

Result: 0 errors, 0 warnings.

## 16. Validation Commands
Passed:

```bash
lake build PRPKG24AccuracyDiversity
python3 scripts/review_dashboard.py --paper PRPKG24AccuracyDiversity --statement-check
python3 scripts/review_dashboard.py --paper PRPKG24AccuracyDiversity --assumption-check
python3 scripts/review_dashboard.py --paper PRPKG24AccuracyDiversity --precheck
python3 scripts/sync_paper_status.py --check
python3 scripts/audit_repository.py --paper PRPKG24AccuracyDiversity --paper-closeout --include-active --info-limit 0
python3 scripts/audit_repository.py --library-only --library-premise-audit --info-limit 0
git diff --check
```

The targeted paper-closeout repository audit:

```bash
python3 scripts/audit_repository.py --paper PRPKG24AccuracyDiversity --paper-closeout --include-active --info-limit 0
```

passes with no PRPKG-specific errors or warnings. The broader unfiltered
repository audit still has unrelated maintenance findings, including a
pre-existing tracked source-PDF artifact in
`papers/GLM20DroppingStandardizedTesting`.

The proof-hole scan found no Lean proof holes in PRPKG files; matches were historical documentation lines mentioning `sorry`/`admit` commands or notes.
