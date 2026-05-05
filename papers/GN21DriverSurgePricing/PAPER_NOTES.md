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

- Date reviewed: 2026-05-05
- Last theorem row verified: Theorem 1 measured marginal add/remove steps,
  Proposition 3.1 measured affine reward step, Lemma 2 CTMC closed form,
  Lemma 1/Lemma 3 measured algebra support, Appendix D derivative-kernel
  algebra, measured Lemma 9/10 accept-all-to-current tightening including
  positive-measure and primitive-equality variants, named-primitive Remark 4
  positivity wrappers, Lemma 9/10 endpoint bridges, Theorem 4 paper-ordered
  shape-derivation routes, raw statewise improvement adapters, shape-level
  with-density bridges for all four Theorem 4 shape cases, the accept-all-bound
  wrappers for all four shape cases, the packaged source-facing
  statewise-improvement certificate for Theorem 4/Theorem 3, Theorem 3 CTMC
  structured price form, Theorem 4 shape-replacement to shape-derivation and
  statewise-improvement bridges, direct Lemma 9 primitive-feasibility bridge,
  ratio-to-IC endpoints, and accept-all-primitive statewise-certificate
  endpoint, accept-all-primitive positive-primitives strict-local and
  statewise-certificate endpoints, raw statewise-improvement positive-primitives
  route, replacement-data Theorem 3 positive-primitives route, all-optimal
  replacement-data Theorem 4/Theorem 3 routes, canonical Lemma 5 replacement
  constructors for all five shape cases, state-specific Theorem 4
  allowed-replacement constructors, source-facing all-optimal replacement case
  data, packaged allowed-replacement Theorem 4/Theorem 3 boundary routes, and
  auxiliary finite dynamic policy support.
- Outstanding assumptions / caveats: source theorems remain conditional on the
  global Theorem 1 threshold-existence compactness/continuity argument, the
  continuous renewal-reward cycle construction, CTMC stochastic-process bridge,
  and the remaining analytic selection/regularity hypotheses listed in
  `README.md`.
