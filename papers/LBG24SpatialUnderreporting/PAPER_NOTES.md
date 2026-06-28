# Quantifying Spatial Under-reporting Disparities in Resident Crowdsourcing Formalization Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `LBG24SpatialUnderreporting`
- Official URL: https://www.nature.com/articles/s43588-023-00572-6
- Source PDF: `source.pdf`
- Local source text cache, if generated: `source.txt` (ignored by Git in public workspaces)

## Formalization checklist

- [ ] Full named-result inventory copied to the README theorem table.
- [ ] DAG graph includes all required paper-stage nodes and dependencies.
- [ ] README status and remaining-assumption notes match proof artifacts.
- [ ] Post-formalization library elevation pass completed: reusable proof
      results, techniques, and primitives were moved into `EconCSLib` when
      local/low-risk, or recorded with destination modules in the final report.
- [ ] Recursive provenance audit completed with
      `python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0 --write-report docs/RECURSIVE_PROVENANCE_AUDIT_<date>.md`;
      all findings for this paper are resolved or explicitly recorded as
      partial/conditional boundaries.
- [ ] Final status review completed before publishing.

## Notes

- Date reviewed: 2026-06-27 status checkpoint before the next reusable-library
  proof campaign.
- Last theorem row formalized: the current `PaperInterface.lean` surface has
  48 paper-facing declarations and 49 review rows, ending with
  `equation7_zero_inflated_likelihood_nonnegative`; the Theorem 1 / Appendix
  Theorem 2 rows route through
  `assumption_theorem2_poisson_process_and_conditions`.
- Outstanding assumptions / caveats: the paper is partially formalized. The
  remaining headline proof obligation is to derive the source-assumption bundle
  from primitive homogeneous Poisson stopping-window semantics and the paper's
  Conditions 1/2. The Appendix B.2 `M > 1` residual reciprocal issue is
  recorded as a source proof-formula correction note. Lemma 1's optional
  stronger stochastic-model route would derive IID/integrability and one-period
  mean premises from a Poisson thinning/steady-state model.
- Reusable library elevation candidates: sample-path/counting-process
  interface for homogeneous Poisson processes, stationary independent
  increments, ordered interarrival density kernels, no-arrival survival over
  stopping windows, first-jump/memoryless splitting, and IID/steady-state
  thinning support for OR/queueing papers.
