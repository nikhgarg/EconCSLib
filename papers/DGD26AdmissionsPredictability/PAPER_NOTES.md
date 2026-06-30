# Capacity Constraints Make Admissions Processes Less Predictable Formalization Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `DGD26AdmissionsPredictability`
- Official URL: https://ojs.aaai.org/index.php/AAAI/article/view/41179
- Open TeX/PDF source: https://arxiv.org/abs/2601.11513
- Source PDF: `source.pdf`
- Local source text cache, if generated: `source.txt` (ignored by Git in public workspaces)

## Formalization checklist

- [x] Full named-result inventory copied to the README theorem table.
- [x] DAG graph includes all required paper-stage nodes and dependencies.
- [x] README status and remaining-assumption notes match proof artifacts.
- [x] Post-formalization library elevation pass completed: reusable proof
      results, techniques, and primitives were moved into `EconCSLib` when
      local/low-risk, or recorded with destination modules in the final report.
- [x] Targeted recursive provenance/source-record audit completed; all findings
      for this paper are resolved or explicitly recorded as source-facing
      theorem conditions.
- [x] Final status review completed before publishing.

## Notes

- Date reviewed: 2026-06-30
- Last theorem row formalized:
  `paper_even_instability_inconsistency_converse_statement`;
  the paper target builds with 101 source-facing review rows and 5 auxiliary
  proof-support bridge rows.
- Conditions and source notes:
  - Main no-zero-instability theorem exposes the standard nontrivial capacity
    domain: positive capacity and an applicant pool larger than capacity.
  - Appendix removable-set lemma has a typo:
    `V_C(X_1) = V_C(X_1)` should read `V_C(X_1) = V_C(X_2)`.
  - The q-representative converse is now proved via a revealed-preference
    asymmetry/minimal-descent argument. The paper-facing characterization says
    that under feasibility, q-representativeness is equivalent to
    q-acceptance, 1-instability, and variability at most one.
  - Exact variability one is formalized with an explicit displacement witness
    to rule out degenerate no-displacement cases; this is a theorem condition,
    not an unresolved caveat.
  - q-representative forward variability is formalized for both the main
    borderline definition and the appendix general borderline/waitlisted
    definition. A q-representative/full-capacity changing-insert version of the
    Ranking-m bridge is also proved, and the same bridge is exposed directly
    under the q-acceptant, 1-instability, and variability-at-most-one
    characterization hypotheses. The appendix general-variability bound and
    exact-one form under those one-variable hypotheses now follow directly from
    the all-`m` append/remove equivalence, with exact one requiring a real
    displacement witness.
  - Append/remove exact-exchange helpers are proved: a waitlisted witness
    exactly replaces the removed chosen applicant, and a borderline witness
    exactly replaces the displaced chosen applicant by the fresh applicant.
    The finite-family matching bridge is also proved, yielding the all-`m`
    threshold and exact equivalence between appendix general variability and
    main-text borderline variability for feasible q-acceptant 1-unstable rules.
  - The main sequential q-representative queue variability upper bound is
    proved, along with feasibility, summed-capacity q-acceptance, and
    1-instability for feasible q-representative queue compositions. The
    appendix additive theorem is also proved for feasible q-acceptant
    1-unstable stages with supplied per-stage variability bounds.
  - LAP ordering is proved in both source-facing directions from primitive
    assignment optimality and rejected-applicant replacement feasibility.
    Global objective optimality with capacity filling is proved to imply the
    local no-profitable-one-slot-swap condition used by the ordering lemma.
    Feasible capacity-filling unique global-optimum assignment selectors now
    induce feasible q-acceptant 1-unstable choice rules. The formerly missing
    single-addition exchange step is proved in `LAP.lean` by a directed
    alternating-splice argument. The distinct-ordering variability theorem is
    now proved by a proper-suffix exchange: if an inserted applicant displaces
    `y`, no surviving old slot occupant can be strictly below `y` in that
    occupant's old slot order, so each slot-order class contributes at most one
    borderline applicant.
  - The tight-instability construction family is closed: padded even and odd
    trigger-switch constructions prove feasible q-acceptant rules that are
    tightly `d`-unstable for every `1 ≤ d ≤ 2q`. The earlier maximal even/odd
    constructions and tight 1-, 2-, 3-, 4-, and 5-instability examples remain
    as simpler sanity-check witnesses, alongside the general `2q` upper bound.
  - Positive even instability is fully formalized in both directions:
    a fresh rejected applicant with positive distance implies inconsistency,
    inconsistent feasible q-acceptant rules have a positive even fresh-addition
    witness, and consistent q-acceptant rules cannot be tightly positive-even
    unstable.
- Reusable library elevation candidates:
  - Finite choice functions with feasibility, q-acceptance, substitutability,
    monotonicity, consistency, independence, instability, variability, and
    sequential composition.
  - Paper-local finite assignment/no-profitable-one-slot-swap model may become
    reusable if future OR/assignment papers need the same exchange API.
