# Formalization Plan: Combatting Gerrymandering with Ranked Choice Voting: an Experimental Analysis of Multi-member Districts in the United States

This is a working scratchpad for outside-Lean proof thinking. Keep it short and
useful; it is not the final validation report.

- Namespace: `GGRS26CombattingGerrymanderingRCV`

## Initial Outside-Lean Paper Audit

- Source version / local files inspected: arXiv:2107.07083 and local
  `source.pdf` / `source.txt`; official OPRE DOI page recorded in the README.
- Source/version mismatch notes: final validation must compare the OPRE title
  and statement text against the arXiv cache used here.
- Complete named-result ledger status: first-pass source-text inventory
  completed.
- Formula sanity check:
  - Signs, constants, normalizations, quantifiers, domains: not fully checked.
    The main formulas are `n_R(y_R, STV)` / `n_R(y_R, lambda_PAV)` in
    Proposition 1, the rounding set `{floor (y_R M), ceil (y_R M)}`, and Lemma
    C.1's harmonic/PAV marginal inequalities.
  - Density vs mass / likelihood-kernel representation issues: not applicable;
    finite voters, seats, candidates, party shares, and STV/PAV seat shares are
    the key objects.
  - Dependency map between named source results: Lemma C.1 proves the PAV
    rounding component; Proposition 1 combines known STV solid-coalition facts
    with Lemma C.1 to justify the seat-share formula used by the map
    optimization.
  - Formula-bearing displayed claims that need derivation, not source-row
    assumptions: Lemma C.1 inequalities, Droop-quota bounds, and the floor/ceil
    seat-share bridge.
- Named result sanity check:
  - Results that look correct as stated: no contradiction found in the initial
    scan. Proposition 1 is a compact, useful partial formalization target.
  - Suspected bugs, missing assumptions, or ambiguous wording: the first part of
    Proposition 1 cites known STV theory; if not formalized, expose it as an
    external theorem boundary rather than assuming the final conclusion.
- Shared-library reuse checkpoint:
  - Mathlib declarations/modules inspected: finite lists/finsets and natural
    arithmetic through the new `Voting` skeleton.
  - Cslib declarations/modules inspected: none yet.
  - Optlib declarations/modules inspected: none present in this checkout.
  - Existing `EconCSLib` declarations/modules inspected:
    `EconCSLib.SocialChoice.Voting.Thiele` and
    `EconCSLib.SocialChoice.Voting.STV`.
  - API chosen and near-misses: use `Voting.Thiele` for PAV/committee score
    vocabulary and `Voting.STV` for the STV side; do not encode district-map
    generation before the seat-share theorem is source-shaped.
- Proof strategy consequences:
  - Source proof route to follow: Lemma C.1 PAV rounding first; then Proposition
    1 as a conditional STV/PAV seat-share bridge under solid coalitions.
  - Cleaner Lean route or reusable library route: build paper-neutral Thiele
    and seat-share rounding lemmas only when they serve this proof.
  - Major issues already reported to the user: roadmap author metadata was
    stale and has been corrected.

## Source Inventory

- Definitions / formatted paper objects:
  - Multi-member districts, party vote share `y_R`, STV seat count
    `n_R(y_R, STV)`, PAV/Thiele seat count `n_R(y_R, lambda_PAV)`,
    solid-coalition assumption, and tie-breaking in party D's favor.
- Named lemmas / propositions / theorems / corollaries:
  - Proposition 1 (Seat shares under STV) and Lemma C.1.
- Theorem-like displayed claims that are used later:
  - Droop quota bounds, PAV marginal inequalities, floor/ceil rounding bridge,
    and simulation/data-pipeline claims used in the empirical sections.

## Initial Proof Strategy

- Main theorem chain: Lemma C.1 -> PAV seat-share rounding -> STV
  solid-coalition bridge -> Proposition 1 -> redistricting/simulation boundary.
- Likely reusable `EconCSLib` seams: Thiele/PAV scoring, seat-share rounding,
  floor/ceil arithmetic, and STV solid-coalition seat conservation.
- Paper steps that look underspecified or analytically hard: the cited STV
  solid-coalition theorem, full ranking/no exhaustion assumptions, and the
  data/simulation pipeline.
- Formal target map:
  - Rows to fully prove now: natural-valued Thiele score wrappers and later
    Lemma C.1's finite rounding statement.
  - Empirical/descriptive rows out of formal theorem scope: map optimization,
    simulations, computational runtime, district plans, and empirical figures.
  - Explicit assumption/certificate boundaries, if any: cited STV
    solid-coalition theorem and data/code pipeline.
- Planned fallback route if the source proof is too informal: formalize the PAV
  rounding lemma fully and state Proposition 1 conditional on a named STV
  solid-coalition theorem boundary.

## Reusable-Library TODO

- Library APIs to use directly:
  `EconCSLib.SocialChoice.Voting.roundedSeatShare`,
  `EconCSLib.SocialChoice.Voting.pavSeatInterval`, and
  `EconCSLib.SocialChoice.Voting.pavSeatInterval_roundedSeatShare`,
  `EconCSLib.SocialChoice.Voting.pavSeatInterval_of_isMinArgmaxOn`, and
  `EconCSLib.SocialChoice.Voting.roundedSeatShare_of_isMinArgmaxOn`.
- Small reusable lemmas added now: the interval-to-floor/ceil rounding theorem
  for the Lemma C.1 seat-count interval, the two-party PAV harmonic score,
  leftmost argmax predicate, adjacent marginal-weight bridge,
  min-argmax-to-rounded-seat bridge, quota-witness-to-lower-bound arithmetic,
  canonical quota residual certificates, terminal same-party quota-process
  constructors, solid-coalition party isolation, and primitive trace-to-party
  preservation constructors. The STV quota-capacity step
  `twoParty_floor_votes_div_STVQuota_sum_le_seats` is in
  `EconCSLib.SocialChoice.Voting.STV.Quota`. The current paper-facing GGRS
  route uses `paper_stv_solid_coalition_primitive_trace_bounds` and
  `paper_proposition1_from_solid_coalition_primitive_trace_and_pav_min_argmax`.
- Larger reusable components to defer: a concrete executable fractional STV
  transfer implementation that produces the primitive per-step transfer-law,
  terminal-below-quota, and final-seat-inclusion facts currently passed to the
  primitive trace theorem.
- Library-audit risks: the old process/replay boundary is no longer exposed by
  the GGRS `PaperInterface.lean` review surface. The remaining boundary is
  narrower and source-shaped: deriving the primitive trace facts from a
  concrete source algorithm and transfer rule.

## Execution Checklist

- [ ] Download/cache source PDFs and text extracts, with redistribution notes.
- [ ] Complete named-result and formula-bearing displayed-claim inventory.
- [ ] Fill the formal target map and declare any intended boundary/certificate.
- [x] Build or select reusable library APIs before adding paper-local wrappers.
- [x] Replace initial paper scaffold with source-facing Lean definitions and
      the first bridge row.
- [ ] Prove all rows marked in-scope, or downgrade them with an explicit
      boundary note.
- [ ] Update README, status, DAG, and validation report from the same row list.
- [ ] Run build, audits, placeholder/provenance checks, and DAG validation.
- [ ] Record any unresolved source bug, assumption, or library debt.

## Active Scratchpad

- Current Lean endpoints:
  `paper_pav_min_argmax_seat_interval`,
  `paper_pav_min_argmax_seat_share_rounded`,
  `paper_stv_solid_coalition_ballots_party_trace_isolation`,
  `paper_stv_solid_coalition_primitive_trace_bounds`,
  `paper_stv_solid_coalition_primitive_trace_quota_witness_bounds`,
  `paper_stv_quota_floors_fit`, and
  `paper_proposition1_from_solid_coalition_primitive_trace_and_pav_min_argmax`
  in `PaperInterface.lean`.
- Exact current mathematical gap: derive the primitive candidate-level trace
  facts from a concrete STV source algorithm and transfer rule. The paper-facing
  theorem no longer stops at an opaque process/replay input, but the primitive
  per-step transfer law, terminal below-quota condition, and final-seat
  inclusion are still theorem premises.
- Next bridge lemmas to try if strengthening the model: an executable
  fractional-STV transition function plus a theorem that each generated step
  satisfies the primitive transfer-preservation law used by the current GGRS
  primitive trace endpoint.
- Informal proof sketch / recurrence / construction: split the PAV marginal
  optimality conditions into the two paper inequalities, rewrite harmonic
  weights as reciprocals, and derive
  `y_R (M + 1) - 1 <= n_R < y_R (M + 1)`.

## Deviations And Assumptions

- Source imprecision or proof deviation to report later:
- Genuine paper assumptions to declare in `Assumptions.lean`:
- Temporary certificate fields to discharge:
  primitive STV trace generation and transfer-law facts from the source
  algorithm.
- Validation/audit checks that must inspect these assumptions:
