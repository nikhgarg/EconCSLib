# Designing Informative Rating Systems: Evidence from an Online Labor Market Formalization Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `GJ18InformativeRatingSystems`
- Official URL: https://doi.org/10.1287/msom.2020.0921
- Publisher page: https://pubsonline.informs.org/doi/10.1287/msom.2020.0921
- Public preprint and TeX cache source: https://arxiv.org/abs/1810.13028
- Source PDF: `source.pdf`
- Local source text cache, if generated: `source.txt` (ignored by Git in public workspaces)

## Formalization checklist

- [x] Full named-result inventory copied to the README theorem table.
- [x] DAG graph includes all required paper-stage nodes and dependencies.
- [x] README status and remaining-assumption notes match proof artifacts.
- [x] Final status review completed before publishing.

## Notes

- Date reviewed: 2026-06-05
- Last theorem row formalized:
  `theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_rating_tail_dominance_and_full_support`
- The source-facing finite ordinal endpoint is closed. Lean derives the
  pairwise common-dual witnesses and support-safe LDP certificates from
  positive match rates, ordinal upper-tail dominance, monotone scores, and full
  finite ordinal rating support.
- The older all-real real-rate route is retained only as a compatibility
  wrapper for users who supply stronger domain conventions; it is not the
  canonical public status boundary for this paper.
