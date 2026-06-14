# A No Free Lunch Theorem for Human-AI Collaboration Formalization Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `PKG25NoFreeLunch`
- Official URL: https://ojs.aaai.org/index.php/AAAI/article/view/33574
- Source PDF: `source.pdf`
- Local source text cache, if generated: `source.txt` (ignored by Git in public workspaces)

## Formalization checklist

- [x] Full named-result inventory copied to the README theorem table.
- [x] DAG graph includes all required paper-stage nodes and dependencies.
- [x] README status and remaining-assumption notes match proof artifacts.
- [x] Post-formalization library elevation pass completed: reusable proof
      results, techniques, and primitives were moved into `EconCSLib` when
      local/low-risk, or recorded with destination modules in the final report.
- [ ] Final status review completed before publishing.

## Notes

- Date reviewed: 2026-06-13
- Last theorem row formalized: `theorem_main_no_free_lunch`
- Outstanding assumptions / caveats: no proof caveats; source-implicit nonempty agent set and deterministic strategy domain are exposed in the interface/report.
- Reusable library elevation candidates: finite calibrated setting mixtures, finite event-mass scaling lemmas, and finite accuracy range lemmas; kept paper-local until a second paper needs the API.
