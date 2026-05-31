# Final Validation Report: User-Item Fairness Tradeoffs in Recommendations

Date: 2026-05-01

## Verdict

The tracked paper-facing formalization for *User-item fairness tradeoffs in
recommendations* is formalized in Lean.

The paper-local status ledger marks no active target remaining, and the targeted
paper build completed successfully. A Lean-file placeholder scan found no real
`sorry`, `admit`, or `axiom` proof gaps in `papers/GCG24UserItemFairness`;
matches were only comment prose.

## Scope Checked

The validation source of truth was the paper folder, not older campaign-level
notes:

- `papers/GCG24UserItemFairness/README.md`
- `papers/GCG24UserItemFairness/DependencyDAG.tex`
- `papers/GCG24UserItemFairness/PaperInterface.lean`
- `papers/GCG24UserItemFairness/MainTheorems.lean`
- the successful targeted Lean build

`PaperInterface.lean` exposes the human-facing definitions and main theorem
statements. `MainTheorems.lean` exposes the full paper-facing wrappers.
Detailed proof work is split across the paper-local LP reduction,
optimization, symmetry, opposing-types, and misestimation files.

## Results Covered

The formalization covers the paper's tracked named model definitions, supporting
propositions, supporting appendix lemmas, and main paper-facing results,
including:

- recommendation-model user/item fairness definitions and optimization
  predicates;
- Example 1's two-item diverse-preferences toy instance and homogeneous
  tradeoff algebra;
- Proposition 1's symmetric LP-reduction instantiation used downstream;
- Proposition 2's symmetric optimum and sparse-support bridge;
- Appendix C Lemmas 1--2 and Appendix D Lemmas 3--11;
- Theorem 3 price-of-fairness monotonicity through canonical reduction-witness
  wrappers on both halves of the alpha interval;
- Appendix E Lemmas 12--17 and the Problem 11 construction;
- Theorem 4 misestimation/no-fairness and with-fairness source wrappers for both
  possible true cold-start rows.

## Additional Assumptions

No additional unverified assumptions remain for the final source Theorem 3 and
Theorem 4 wrappers tracked by the paper README/DAG.

Some declarations expose ordinary mathematical hypotheses that are part of the
formal statement or its intended model, for example finite type representatives,
positive row normalizers, nonnegative or strictly positive utilities, and
compatibility assumptions identifying estimated known rows with the true rows.
These are not proof gaps; they are explicit hypotheses in the formalized model.

The main modeling caveat is that the paper's general "finding reduces to an LP"
claim is encoded through paper-local equality-form LP and certificate interfaces
rather than a generic solver-level LP syntax. The final paper-facing wrappers
construct or discharge the needed certificates internally. Auxiliary
selected-BFS/certificate variants that still take explicit inputs are retained
as helper interfaces and are not the closed source theorem wrappers.

## Mistakes or Deviations Found

The main deviation from a literal paper proof is the LP boundary. Instead of
formalizing a general-purpose LP solver/simplex theorem, the proof uses
paper-local equality-form primal/dual certificates, closed-form witnesses,
finite pivot existence, and complementary-slackness-style uniqueness arguments.
This is a proof-method deviation, not an open assumption.

The center-pivot Lemma 15 formula required an explicit convention split: the
source displayed center formula is formalized under a half-LP center-item
convention, while the executable full Problem 11 proof uses the mirrored-policy
identity. The distinction is documented in the README and represented by
separate paper-facing declarations.

Older author-wide status notes were stale for this paper. The paper-local README
and DAG correctly indicate that the final wrappers are closed.

## Paper-Proof Fidelity

The Lean development follows the paper's named proof architecture closely:
symmetry reduction, sparse support and opposing-types reductions, canonical
pivot/closed-form constructions for Problem 6, mirror symmetry for the second
half of Theorem 3, and the Appendix E Problem 11/cold-start construction for
Theorem 4.

Where the Lean proof differs, the difference is mainly organizational: LP
arguments are factored through auditable certificate structures, and parity,
center, and mirror cases are made explicit as separate lemmas before being
recombined by the final source wrappers.

## Residual Risk

The residual risk is statement-audit risk, not Lean proof risk: a human should
still compare the paper-facing declarations in `MainTheorems.lean` against the
source PDF to confirm that the intended modeling conventions are exactly the
ones desired. The compiled Lean proof itself has no remaining placeholders for
the tracked paper-facing results.
