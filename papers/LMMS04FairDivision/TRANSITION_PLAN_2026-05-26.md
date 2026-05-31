# LMMS04 Transition Plan

Date: 2026-05-26.

## Stopping Point

The Lean development is at a clean compile boundary. Section 2, Theorem 3.1,
Theorem 3.2's Graham-citation wrapper, Claim 3.4's finite exact-allocation
source wrapper, Lemma 3.5 arithmetic transfer, the large Theorem 3.3
finite-search/IP/source-output surface, and Section 4 compile.

The paper is not fully formalized because Theorem 3.3 still lacks a concrete
Lenstra/fixed-dimension IP runtime theorem or equivalent machine-model proof.
The current code exposes that as an abstract
`EconCSLib.Complexity.ExternalSolverConsequence`, not as a proved PTAS/FPTAS
runtime statement.

## Plan Decision

The forward plan is to fully formalize the LMMS04-specific mathematics and
certificate plumbing, while treating fixed-dimension integer-program runtime as
a named external complexity boundary.

Concretely:

- Fully formalize and review the paper-local finite allocation, rounding,
  Claim 3.4, finite search, concrete IP-certificate, source-output, and ratio
  transfer layers.
- Keep Theorem 3.3's final PTAS/FPTAS runtime conclusion conditional on
  `EconCSLib.Complexity.ExternalSolverConsequence` until a concrete
  fixed-dimension IP runtime theorem is available.
- Do not formalize Lenstra/Kannan-style fixed-dimension integer programming
  inside this paper folder. That belongs in a reusable complexity/optimization
  layer, or in an imported upstream library theorem.
- Human-facing status must remain "partially formalized" or "conditional" for
  Theorem 3.3 until this boundary is discharged. The boundary is not a hidden
  LMMS combinatorial assumption; it is the standard external algorithmic
  runtime theorem used to turn the finite IP search into a PTAS/FPTAS.

## CSLib / optlib Path

No public CSLib or optlib theorem currently appears to provide the needed
Lenstra/fixed-dimension IP runtime result directly. Keep LMMS04 insulated from
future library churn by routing through a small adapter theorem:

1. Preserve the current LMMS theorem shape in terms of
   `ExternalSolverConsequence`.
2. If CSLib supplies a suitable machine-model or cost-semantics theorem, use it
   to justify the polynomial/FPTAS runtime part of the adapter.
3. If optlib supplies a suitable integer-program feasibility/optimization
   theorem, use it to justify the IP solver specification part of the adapter.
4. If both libraries mature in complementary directions, combine them in an
   `EconCSLib.Algorithms.Complexity.FixedDimensionIP` adapter rather than
   changing the LMMS paper-facing declarations.

## Strongest Current Boundary

Use the public aliases in `PaperInterface.lean`:

- `theorem3_3_external_solver_selected_pair_full_summary_source_output_package`
- `theorem3_3_external_solver_selected_pair_full_summary_source_output_payload`
- `theorem3_3_external_solver_selected_pair_full_summary_source_output_consequence`
- `theorem3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_no_top_of_margin`
- `theorem3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_forward_additive_no_top_of_margin`

These package the selected search witness, full comparison/search IP summaries,
source-output allocation payload, and an externally supplied solver
consequence. They are the intended entry point for the final runtime proof.

## Do Not Redo

- Do not reopen the Claim 3.4 finite descent unless a compile error points
  there. The all-goods exact source wrapper is already present.
- Do not force the rounded combined supply back to the original average `L`.
  The verified Theorem 3.3 route is two-scale: the value grid uses the original
  average and the rounded search/window uses the generated rounded average
  `LR`.
- Do not replace the external solver seam with an optimistic PTAS/FPTAS theorem
  unless the statement explicitly treats PTAS/FPTAS as an external `Prop` or a
  real machine-model theorem has been added.
- Do not populate review-dashboard entries as an agent. The dashboard currently
  has zero human-reviewed rows.

## Next Proof Work

1. Continue closing and reviewing any remaining LMMS04-specific finite
   mathematics around the existing compact external package; do not spend paper
   effort on an internal Lenstra proof.
2. On the library track, add or import a concrete fixed-dimension
   integer-program solver/runtime theorem for the LMMS search/IP shape, or
   formalize a reusable machine-model theorem that can instantiate
   `ExternalSolverConsequence`.
3. Instantiate the compact external package above using the Claim-3.4
   source-average scalar or additive endpoint once the library theorem exists.
4. State the final paper-facing PTAS/FPTAS complexity theorem only after the
   runtime theorem is real, then update `README.md`, `DependencyDAG.tex`, and
   `docs/ECONCSLEAN_CURRENT_STATUS.md`.
5. Run the human review workflow by slices. `review_slices.json` partitions the
   791 `PaperInterface.lean` rows into 16 slices with max size 70.

## Validation Snapshot

Passed:

```bash
lake env lean -t 0 papers/LMMS04FairDivision/MainTheorems.lean
lake build LMMS04FairDivision
rg -n '\b(sorry|admit|axiom|opaque|placeholder|TODO|FIXME)\b' papers/LMMS04FairDivision --glob '*.lean'
comm -23 <(rg -o 'paper_lmms_theorem_3_3_[A-Za-z0-9_]+' papers/LMMS04FairDivision/MainTheorems.lean | sort -u) <(rg -o 'paper_lmms_theorem_3_3_[A-Za-z0-9_]+' papers/LMMS04FairDivision/PaperInterface.lean | sort -u)
python3 /home/nkgarg/.codex/skills/.system/skill-creator/scripts/quick_validate.py skills/econcs-formalizer
```

Expected nonzero checks:

- `./review-dashboard.sh --check`: reports `0/791` reviewed, `0` stale,
  `0` mismatch.
- `python3 scripts/audit_repository.py --include-active`: repo-wide failures
  remain. LMMS04-specific output is the missing cached source PDF plus an info
  line that `review_slices.json` exposes 791 rows across 16 slices.
