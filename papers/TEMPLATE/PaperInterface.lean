import TEMPLATE.MainTheorems
import TEMPLATE.Assumptions

/-!
# Human-Facing Paper Interface: [Paper Title]

This is the compact Lean file a human should read after formalization to check
whether the paper's definitions and named theorem statements were represented
correctly.

Rules for completing this file:

- Keep the paper's definitions/formatted objects first, in source order.
- Expose the actual paper formulas here; do not only point to generic library
  definitions or implementation witnesses.
- If a named theorem needs a hypothesis that is not derived from earlier Lean
  declarations, declare that hypothesis in `Assumptions.lean` and list it in
  `status.json` `review_surface.assumption_names`.
- Then state the named results directly, with assumptions visible in each
  theorem signature by referencing named paper assumptions imported from
  `Assumptions.lean`.
- Use short proofs that call into `MainTheorems.lean` or lower proof files.
- Keep exhaustive endpoint aliases and proof-seam checks in `PostPaperAudit.lean`,
  not here.

## Paper Definitions

- `paperDefinition1_formula`: placeholder for the first exact source formula.

## Named Results

- `paper_theorem_1_statement`: placeholder for the first exact source theorem.
-/

namespace TEMPLATE

/--
Definition 1 / first source object.

Replace this placeholder with the raw formula from the paper. A reviewer should
not need to open imported files to know what this object means.
-/
abbrev paperDefinition1_formula : Prop := True

/--
Theorem 1 / first named result.

Replace this placeholder with the exact source theorem statement, using the
visible paper-facing definitions and named paper assumptions imported from
`Assumptions.lean`.
-/
theorem paper_theorem_1_statement
    (_h_source : assumption_source_model_conditions) :
    paperDefinition1_formula := by
  trivial

end TEMPLATE
