# Combatting Gerrymandering with Ranked Choice Voting: an Experimental Analysis of Multi-member Districts in the United States Formalization Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `GGRS26CombattingGerrymanderingRCV`
- Official URL: https://pubsonline.informs.org/doi/abs/10.1287/opre.2024.1167
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

- Date reviewed: 2026-06-29 stopping point.
- Last theorem row formalized:
  `paper_proposition1_from_solid_coalition_primitive_trace_and_pav_min_argmax`.
- Outstanding assumptions / caveats: the primitive candidate-level STV trace
  facts still need to be derived from the paper's executable STV source model
  and transfer rule; generated LLM sidecars are stale relative to the current
  21-row review surface.
- Reusable library elevation candidates: executable STV transition/transfer
  constructors that instantiate primitive trace laws from raw ballots.
