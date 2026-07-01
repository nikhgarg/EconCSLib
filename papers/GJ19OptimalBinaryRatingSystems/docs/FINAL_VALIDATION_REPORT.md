# Final Validation Report: GJ19 Optimal Binary Rating Systems

## 1. Human Verdict
The binary-rating theory from the AISTATS/PMLR paper and supplement is
formalized in Lean. The checked surface covers the finite large-deviation
layer, Theorem 3.1, Theorem 3.2 certificate statements, Appendix B convergence
and learning lemmas, and the Kendall/Spearman example branches. No source
discrepancy is identified for this theorem surface.

## 2. Closeout Status
Status: formalized.

The curated dashboard surface contains 25 source-level rows. Those rows are
intended for human translation review of the main definitions, theorem blocks,
algorithm certificate, examples, and Appendix B convergence/learning results.
The much larger helper surface remains proof-facing infrastructure.

## 3. Source and Scope
- Paper: *Designing Optimal Binary Rating Systems*.
- Authors: Nikhil Garg and Ramesh Johari.
- Publication venue: AISTATS / PMLR 89, 2019.
- Source version: PMLR 89 paper PDF plus PMLR supplement PDF.
- Lean folder: `papers/GJ19OptimalBinaryRatingSystems`.
- Human-facing theorem file: `papers/GJ19OptimalBinaryRatingSystems/PaperInterface.lean`.
- Detailed audit: `papers/GJ19OptimalBinaryRatingSystems/POST_FORMALIZATION_AUDIT.md`.
- DAG artifacts: `papers/GJ19OptimalBinaryRatingSystems/DependencyDAG.tex`, `papers/GJ19OptimalBinaryRatingSystems/DependencyDAG.pdf`.

The source PDF, supplement, TeX, and extracted text caches are local
source-audit artifacts. They are not part of the committed theorem surface.
Empirical simulations, figures, and visualization material are outside the
Lean theorem scope.

## 4. Researcher Summary of Checked Results
The formalization verifies the paper's mathematical theory for optimal binary
rating systems. The checked development includes Bernoulli KL formulas,
adjacent-rate formulas, finite equalized-rate optimization, finite and
continuum objective aggregation, the large-deviation rate characterization, the
algorithmic certificate layer, Appendix B convergence and learning statements,
and the Kendall/Spearman examples.

## 5. Remaining Boundaries and Gaps
No remaining theorem boundary is recorded for the formalized mathematical
surface. Empirical simulations, plots, and visualization material remain
outside the Lean theorem scope.

## 6. Additional Assumptions Beyond Paper
None identified. The Lean development exposes model-regularity,
measurability, boundedness, positivity, and convergence hypotheses explicitly
where the source proof uses them in prose.

## 7. Proof-Strategy Deviations
None requiring a public qualification. The Lean proof factors several source
arguments through reusable large-deviation, finite-optimization, and
convergence interfaces, but the paper-facing conclusions are the source
results.

## 8. Proof Tricks Worth Reusing
- Keep displayed formulas as small review rows before exposing broad theorem
  wrappers.
- Separate source-level theorem rows from helper rows so the dashboard remains
  reviewable.
- Package reusable regularity reductions in a paper-local assumptions/proof
  interface rather than turning them into public caveats.

## 9. Paper Issues or Caveats
None recorded for the formalized theorem surface.

## 10. Detailed Formalization Evidence
The formalized surface includes:

- Bernoulli KL and support-safe Bernoulli KL formulas.
- Theorem 3.1 adjacent binary-rate formula and two-stage value/rate optimality
  logic.
- Lemma 3.1 closed adjacent-rate formula and finite equalized-rate optimizer.
- Theorem C.1 weighted large-deviation/Laplace skeleton.
- Lemma C.3 finite decomposition, adjacent dominance, and partition-integral
  aggregation.
- Lemma C.4 positive-rate characterization and reverse obstruction.
- Theorem 3.2 finite calculated-grid approximation/runtime certificate
  statements.
- Lemmas C.10-C.12, the Kendall/Spearman examples, Theorem B.1, Corollary C.4,
  and Appendix B.2/B.3 learning wrappers.

## 11. DAG Audit
The dependency DAG was rerendered as `DependencyDAG.pdf` on 2026-06-28.
Visual inspection after rerendering checked for stale open-box notation,
overlap, and missing theorem labels. The DAG shows the GJ19 theorem surface as
formalized and distinguishes theorem nodes from reusable proof-interface nodes.

## 12. Validation Checks
Validation commands run on 2026-06-28:

```bash
lake build GJ19OptimalBinaryRatingSystems
python3 scripts/sync_paper_status.py --check
python3 scripts/review_dashboard.py --paper GJ19OptimalBinaryRatingSystems --precheck
python3 scripts/audit_repository.py --paper GJ19OptimalBinaryRatingSystems --paper-closeout --include-active --info-limit 0
```

The build, status sync, and dashboard precheck passed. The closeout audit is
used as the repository-level style/provenance check.
