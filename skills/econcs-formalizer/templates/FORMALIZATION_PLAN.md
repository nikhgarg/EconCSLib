# Formalization Plan: {{TITLE}}

This is the paper-local outside-Lean scratchpad. Keep it short enough to guide
proof work, but complete enough that another agent can see the theorem target,
source risks, and reusable-library choices before opening Lean files.

- Namespace: `{{NAMESPACE}}`

## Initial Outside-Lean Paper Audit

- Source version / local files inspected:
  - Official source:
  - Open/source-of-truth version:
  - Local PDF/TeX/text caches:
  - Extraction notes:
- Source/version mismatch notes:
  - Publication/source-version differences:
  - Theorem-level differences found:
- Complete named-result ledger status:
  - Source files searched:
  - Named definitions/results extracted:
  - Empirical/descriptive material excluded from theorem scope:
- Formula sanity check:
  - Signs/constants/domains:
  - Density vs mass / likelihood-kernel representation issues:
  - Dependency map between named source results:
  - Formula-bearing displayed claims that need derivation, not source-row
    assumptions:
- Named result sanity check:
  - Results that look correct as stated:
  - Suspected bugs, missing assumptions, or ambiguous wording:
- Shared-library reuse checkpoint:
  - Mathlib declarations/modules inspected:
  - Cslib declarations/modules inspected:
  - Optlib declarations/modules inspected:
  - Existing `EconCSLib` declarations/modules inspected:
  - API chosen and near-misses:
- Proof strategy consequences:
  - Source proof route to follow:
  - Cleaner Lean route or reusable library route:
  - Major issues already reported to the user:

## Source Inventory

- Definitions / formatted paper objects:
- Named lemmas / propositions / theorems / corollaries:
- Theorem-like displayed claims that are used later:
- Algorithms, tables, empirical procedures, or examples that affect theorem
  interpretation:

## Initial Proof Strategy

- Main theorem chain:
- Likely reusable `EconCSLib` seams:
- Paper steps that look underspecified or analytically hard:
- Formal target map:
  - Rows to fully prove now:
  - Empirical/descriptive rows out of formal theorem scope:
  - Explicit assumption/certificate boundaries, if any:
- Planned fallback route if the source proof is too informal:

## Reusable-Library TODO

- Library APIs to use directly:
- Small reusable lemmas to add now:
- Larger reusable components to defer:
- Library-audit risks:

## Execution Checklist

- [ ] Download/cache source PDFs and text extracts, with redistribution notes.
- [ ] Complete named-result and formula-bearing displayed-claim inventory.
- [ ] Fill the formal target map and declare any intended boundary/certificate.
- [ ] Build or select reusable library APIs before adding paper-local wrappers.
- [ ] Replace paper scaffold with source-facing Lean definitions and rows.
- [ ] Prove all rows marked in-scope, or downgrade them with an explicit
      boundary note.
- [ ] Update README, status, DAG, and validation report from the same row list.
- [ ] Run build, audits, placeholder/provenance checks, and DAG validation.
- [ ] Record any unresolved source bug, assumption, or library debt.

## Active Scratchpad

- Current Lean endpoint:
- Exact current mathematical gap:
- Next bridge lemmas to try:
- Informal proof sketch / recurrence / construction:

## Deviations And Assumptions

- Source imprecision or proof deviation to report later:
- Genuine paper assumptions to declare in `Assumptions.lean`:
- Temporary certificate fields to discharge:
- Validation/audit checks that must inspect these assumptions:
