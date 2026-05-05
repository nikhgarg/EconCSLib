# Driver Surge Pricing Verification Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `GN21DriverSurgePricing`
- Official URL: https://pubsonline.informs.org/doi/10.1287/mnsc.2021.4058
- Source PDF: `source.pdf`
- Source text cache: `source.txt`

## Verification checklist

- [x] Full named-result inventory copied to the README theorem table.
- [x] DAG graph includes all required paper-stage nodes and dependencies.
- [x] README status and remaining-assumption notes match proof artifacts.
- [x] Final status review completed before publishing.

## Notes

- Date reviewed: 2026-05-04
- Last theorem row verified: Theorem 1 measured marginal add/remove steps,
  Proposition 3.1 measured affine reward step, Lemma 2 CTMC closed form,
  Lemma 1/Lemma 3 measured algebra support, Appendix D derivative-kernel
  algebra and conditional Lemma 4-10/Theorem 4 endpoints, Theorem 3 CTMC
  structured price form, and auxiliary finite dynamic policy support.
- Outstanding assumptions / caveats: source theorems remain conditional on the
  global Theorem 1 threshold-existence compactness/continuity argument, the
  continuous renewal-reward cycle construction, CTMC stochastic-process bridge,
  and derivative-shape certificates listed in `README.md`.
