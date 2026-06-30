# Formalization Plan: Capacity Constraints Make Admissions Processes Less Predictable

This is a working scratchpad for outside-Lean proof thinking. Keep it short and
useful; it is not the final validation report.

- Namespace: `DGD26AdmissionsPredictability`

## Initial Outside-Lean Paper Audit

- Source version / local files inspected:
  - Canonical publication page:
    <https://ojs.aaai.org/index.php/AAAI/article/view/41179>.
  - Published venue metadata: AAAI-26 Special Track on AI for Social Impact I,
    Proceedings of the AAAI Conference on Artificial Intelligence 40(45),
    38385-38394, DOI <https://doi.org/10.1609/aaai.v40i45.41179>,
    published 2026-03-14.
  - Open TeX/PDF source: arXiv:2601.11513v1,
    <https://arxiv.org/abs/2601.11513>, submitted 2026-01-16.
  - Local caches:
    `papers/DGD26AdmissionsPredictability/source.pdf`,
    `papers/DGD26AdmissionsPredictability/source.txt`,
    `papers/DGD26AdmissionsPredictability/source_tex/main.tex`, and
    `papers/DGD26AdmissionsPredictability/source_tex/appendix.tex`.
- Source/version mismatch notes:
  - The AAAI abstract uses "stability" where the arXiv TeX source uses
    "instability"; the theorem body and definitions use instability.
  - The TeX source is treated as the exact formula source. The AAAI page is
    the canonical publication/source documentation link.
- Complete named-result ledger status:
  - Initial TeX scan complete. Main text has four core definitions, one
    proposition, two main theorems, sequential composition, and the empirical
    queue-count proposition. The appendix adds auxiliary definitions and
    lemmas for monotonicity, consistency, q-representativeness, zero
    instability, independence, distance terms, triangle inequality,
    substitutability equivalence, consistency, instability constructions,
    variability equivalence, sequential composition, and linear assignment.
- Formula sanity check:
  - Signs, constants, normalizations, quantifiers, domains:
    - The main "no 0-instability under q-acceptance" statement needs the
      appendix's nontrivial-universe hypothesis, e.g. `|X| > q >= 1`; otherwise
      a universe with at most `q` applicants is q-acceptant and zero-unstable by
      accepting everyone.
    - The appendix proof sketch for monotonicity/q-acceptance uses two disjoint
      q-sets, which would require `|X| >= 2q`; the theorem itself can be proved
      under the stated weaker `|X| > q >= 1` by comparing two q-subsets inside
      a shared `(q+1)`-set.
    - Choice functions must explicitly include feasibility `C(X) subset X`;
      the prose definition states this before q-acceptance and all capacity
      proofs rely on it.
    - The paper writes variability as an exact maximum. In Lean, start with
      pointwise/upper-bound forms and derive exact finite maxima after the
      finite-universe API is stable.
    - Sequential composition order differs slightly between main text and
      appendix notation; formalize one source-facing recursive order and prove
      equivalence aliases if needed.
  - Density vs mass / likelihood-kernel representation issues:
    - None. This paper's formal core is finite choice theory, not probability
      densities.
  - Dependency map between named source results:
    - Choice-distance term lemmas imply zero-distance iff substitutable and
      monotonic.
    - Independence iff substitutable and monotonic implies only independent
      rules are zero-unstable; with the nontrivial-universe condition,
      q-acceptance rules are not zero-unstable.
    - Non-substitutability reduction plus q-acceptance proves
      substitutability iff 1-instability.
    - q-representativeness iff q-acceptance plus 1-instability plus
      1-variability feeds ML representation and the single-queue case of the
      variability theorem.
    - Sequential composition preserves substitutability and has additive
      variability, giving the main n-queue variability bound.
    - Linear assignment results are appendix extensions; they likely need a
      compact matching/assignment certificate API.
  - Formula-bearing displayed claims that need derivation, not source-row assumptions:
    - Choice distance.
    - Instability and variability definitions.
    - Borderline and waitlisted sets.
    - Append/remove equality of maxima.
    - Sequential-composition union/recurrence.
    - Additive variability bound.
    - LAP slot-ordering and variability bound.
- Named result sanity check:
  - Results that look correct as stated:
    - Choice-distance term characterizations, zero-distance equivalence,
      independence equivalence, substitutability/1-instability under
      q-acceptance, consistency from q-acceptance plus substitutability,
      sequential composition preservation of substitutability, and additive
      variability.
  - Suspected bugs, missing assumptions, or ambiguous wording:
    - Appendix Lemma "Consistency of Removable Sets" states
      `V_C(X_1) = V_C(X_1)`. The intended statement is
      `V_C(X_1) = V_C(X_2)` when `C(X_1) = C(X_2)`.
    - The main Theorem 1 first item omits the nontrivial-universe condition
      that is stated in the appendix incompatibility lemma.
    - Theorem 2's wording "`m=1` iff characterized by a single total order,
      `n=1`" needs a minimal/distinct-queue interpretation. Literal `n=1` is
      false for nonminimal decompositions, for example repeated identical queue
      orderings can be represented with more than one stage while still
      inducing one total order.
    - The theorem "can be tightly d-unstable for every 1 <= d <= 2q" is
      constructive but informally stated; Lean should expose the concrete
      construction family rather than leave an existence claim opaque.
    - The additive variability proof sketch needs the first-stage remainder
      input to change by at most one element after inserting one applicant. Lean
      proves this from feasibility, q-acceptance, and substitutability; the
      paper's 1-instability hypothesis supplies substitutability under
      q-acceptance. The appendix additive theorem is therefore formalized for
      feasible q-acceptant 1-unstable stages with supplied per-stage
      variability bounds.
    - The LAP ordering lemma needs primitive optimality. A paper-local finite
      assignment model now proves the one-slot ordering lemma from no-profitable
      one-slot swaps, and unique global-optimum assignment selectors now imply
      1-instability by a directed alternating-splice exchange proof.
- Shared-library reuse checkpoint:
  - Mathlib declarations/modules inspected:
    - `Finset`, `Fintype`, finite card lemmas, strict orders, finite sorting,
      and existing finite assignment/matching-adjacent APIs by concept search.
  - Cslib declarations/modules inspected:
    - No local Cslib checkout/module appears in the Lake surface for this
      finite-choice seam.
  - Optlib declarations/modules inspected:
    - No Optlib-specific dependency is needed for this paper; assignment
      optimality will use finite optimization/certificate APIs if needed.
  - Existing `EconCSLib` declarations/modules inspected:
    - `EconCSLib.Foundations.Probability.Admissions` is admissions/probability
      oriented and not a choice-function API.
    - `EconCSLib.Foundations.Math.FiniteRanking` has finite ranking helpers.
    - `EconCSLib.SocialChoice.Ranking.Basic` has ranking primitives for voting,
      but not finite-set choice functions with capacities.
    - Matching and auction modules have local monotonicity notions but no
      reusable choice-function theory with q-acceptance/instability.
  - API chosen and near-misses:
    - Add a reusable finite choice-function module under
      `EconCSLib.Foundations.Math.FiniteChoice`. Keep paper-specific theorem
      labels and source corrections in the paper folder.
- Proof strategy consequences:
  - Source proof route to follow:
    - Mirror the appendix dependency order: definitions, distance term lemmas,
      zero/independence, q-acceptance instability, variability, sequential
      composition, ML representation, empirical queue-count proposition.
  - Cleaner Lean route or reusable library route:
    - Prove generic finite-set lemmas once in `FiniteChoice.lean`, then expose
      source-facing wrappers in `MainTheorems.lean` and `PaperInterface.lean`.
  - Major issues already reported to the user:
    - Nontrivial capacity domain for no zero-instability.
    - Typo in the removable-set lemma.

## Source Inventory

- Definitions / formatted paper objects:
  - q-acceptance.
  - Total order / q-representativeness / queue.
  - Choice distance.
  - d-instability and tight d-instability.
  - Variability and general variability via borderline/waitlisted sets.
  - Substitutability.
  - Sequential composition.
  - Monotonicity.
  - Consistency.
  - Independence.
  - Linear assignment slot ordering/equivalence of slot orderings.
- Named lemmas / propositions / theorems / corollaries:
  - Proposition: ML representation.
  - Theorem: q-acceptant choice-function instability.
  - Theorem: sequential-queue variability.
  - Proposition: empirical program variability.
  - Lemma: incompatibility of monotonicity and q-acceptance.
  - Lemma: non-substitutability single-add reduction.
  - Lemmas: substitutability and monotonicity distance terms.
  - Theorem: triangle inequality for choice distance.
  - Definition/corollary: zero instability and zero distance.
  - Theorem/corollary: independence equivalence and only independent rules are
    zero-unstable.
  - Theorem: substitutability iff 1-instability under capacity.
  - Theorem: q-acceptant substitutable choice functions are consistent.
  - Lemma: calculating instability.
  - Theorem/corollary: even instability and inconsistency.
  - Theorem: append/remove variability maxima equality.
  - Lemma: corrected consistency of removable sets.
  - Lemma: ranking m.
  - Theorem: q-representativeness iff q-acceptance, 1-instability, and
    1-variability.
  - Theorem: sequential composition preserves substitutability.
  - Theorem: additive variability bound.
  - Lemma/theorems: LAP ordering, LAP instability, LAP variability.
- Theorem-like displayed claims that are used later:
  - ML-independent classifier formula.
  - ML rank/threshold classifier formula.
  - Choice-distance formula.
  - Variability, borderline, and waitlisted set formulas.
  - Sequential-composition recurrence.

## Initial Proof Strategy

- Main theorem chain:
  - Build finite choice rules over `Finset α`, with feasibility, q-acceptance,
    substitutability, monotonicity, consistency, independence, choice distance,
    instability, and variability.
  - Prove the distance-term and zero-instability equivalences first.
  - Prove q-acceptance consequences from explicit nontrivial universe/witness
    conditions.
  - Prove sequential composition and ranking results after the base
    substitution/instability lemmas are stable.
  - Formalize ML representation as choice-rule expressiveness: independent
    pointwise rules are zero-unstable; rank/threshold rules correspond to
    q-representative rules.
- Likely reusable `EconCSLib` seams:
  - Finite choice functions with capacity constraints.
  - Choice-distance/cardinality lemmas.
  - Sequential composition of choice rules.
  - Finite top-q/ranking choice rules.
  - Optional finite assignment-choice certificates.
- Paper steps that look underspecified or analytically hard:
  - Constructing tight d-instability examples for all d up to 2q.
  - Proving the full q-representativeness converse from variability 1.
  - LAP variability without importing or building a heavier matching/assignment
    library.
- Formal target map:
  - Rows to fully prove now:
    - All definitions and theorems in the theoretical section and appendix,
      with explicit source-correction notes where needed.
  - Empirical/descriptive rows out of formal theorem scope:
    - Data extraction, XGBoost/logistic methods, NYC empirical performance
      plots, and non-releasable data claims.
  - Explicit assumption/certificate boundaries, if any:
    - None intended at intake. If LAP requires a finite-assignment certificate,
      that certificate must be either constructed in Lean from a concrete
      assignment model or marked as an appendix-only partial boundary.
- Planned fallback route if the source proof is too informal:
  - State and prove stronger/cleaner finite-choice lemmas that imply the source
    results. Do not encode the paper's informal construction as an opaque
    record field.

## Reusable-Library TODO

- Library APIs to use directly:
  - `Finset` cardinality, subset, image/biUnion, and strict order APIs.
  - Existing finite ranking helpers where they reduce top-q proof work.
- Small reusable lemmas to add now:
  - `FiniteChoice` definitions and cardinal lemmas for zero distance,
    substitutability, monotonicity, independence, and q-acceptance
    incompatibility.
  - q-representative forward lemmas: feasibility plus one total-order
    representation implies substitutability, 1-instability, and variability at
    most one; exact variability one additionally needs a displacement witness.
  - sequential composition preserves feasibility and substitutability for
    feasible substitutable stages.
  - sequential composition of feasible q-acceptant 1-unstable stages has
    variability bounded by the sum of supplied per-stage variability bounds.
  - sequential composition of feasible q-representative queues has variability
    at most the number of queues.
  - the paper's instability-calculation lemma, with feasibility explicit.
- Larger reusable components to defer:
  - A reusable finite linear-assignment/matching certificate API beyond the
    current paper-local no-profitable-one-slot-swap model.
- Library-audit risks:
  - Avoid putting paper assumptions or source-provenance language in reusable
    library files.
  - Avoid hiding source formulas in record fields; paper-facing wrappers must
    display the choice-distance/variability formulas.

## Execution Checklist

- [x] Download/cache source PDFs and text extracts, with redistribution notes.
- [x] Complete named-result and formula-bearing displayed-claim inventory.
- [x] Fill the formal target map and declare any intended boundary/certificate.
- [x] Build or select reusable library APIs before adding paper-local wrappers.
- [x] Replace paper scaffold with source-facing Lean definitions and rows.
- [x] Prove all rows marked in-scope, or downgrade them with an explicit
      boundary note.
- [x] Update README, status, DAG, and validation report from the same row list.
- [x] Run build, audits, placeholder/provenance checks, and DAG validation.
- [x] Record any unresolved source bug, assumption, or library debt.

## Active Scratchpad

- Current Lean endpoint:
  - `lake build DGD26AdmissionsPredictability` succeeds with 101
    source-facing review rows and 5 auxiliary proof-support bridge rows.
  - Shared `EconCSLib.Foundations.Math.FiniteChoice` now contains the finite
    choice-rule API, zero/independence lemmas, full
    substitutability iff 1-instability, the full q-representative
    characterization via a revealed-preference minimal-descent proof,
    q-representative forward lemmas,
    q-representative borderline/waitlisted/general variability forward lemmas,
    a full-capacity q-representative insert/remove equality between the
    previous borderline set and new waitlisted set,
    sequential-composition preservation, sequential q-acceptance capacity
    accounting, the appendix additive variability theorem for feasible
    q-acceptant 1-unstable stages with supplied per-stage variability bounds,
    the sequential q-representative variability/property package, the
    instability-calculation lemma, the `2q` instability ceiling for
    q-acceptant rules, a generic maximal-even tight `2q` construction, a
    generic complementary-group tight `2q - 1` construction over a consistent
    q-acceptant fallback, a reusable fresh-chosen-or-no-change lemma for
    `2q - 1` instability, exact waitlisted/borderline one-for-one exchange
    helpers for append/remove variability, the finite-family append/remove
    matching bridge, threshold and exact equivalence between appendix general
    variability and main-text variability for feasible q-acceptant 1-unstable
    rules, a reusable consistency/fresh-not-chosen helper, the positive-even
    instability collapse for consistent rules, and the converse that
    inconsistency in a feasible q-acceptant rule yields a positive even
    fresh-addition distance witness.
  - Paper-local `DGD26AdmissionsPredictability.LAP` contains a primitive
    finite assignment/no-profitable-one-slot-swap model, proves replacement
    feasibility for rejected applicants, proves both source-facing LAP ordering
    directions from objective improvement, defines explicit capacity filling
    and global objective optimality, proves global objective optimality plus
    capacity filling implies the local no-profitable-one-slot-swap condition,
    proves the assignment-induced choice rule is feasible, q-acceptant, and
    1-unstable for feasible capacity-filling unique global-optimum selectors,
    and proves assignment-induced borderline variability is bounded both by
    the number of slots and by the number of distinct slot-induced applicant
    orderings under slotwise no-ties.
- Exact current mathematical gap:
  - No Lean proof gap is currently known for the formalized theorem surface.
    Empirical NYC performance plots and private-data program instantiations are
    descriptive/source-instantiation material outside the Lean theorem target.
  - The q-representative converse is now closed: `QRepresentativeConverseWork`
    proves revealed asymmetry by a finite minimal-descent argument over
    opposite canonical witnesses and extends the revealed relation to a strict
    total order.
  - The all-`d` tight d-instability construction family is closed in Lean:
    padded even and odd trigger-switch constructions give feasible
    q-acceptant rules that are tightly `d`-unstable for every
    `1 ≤ d ≤ 2q`. The generic maximal even/odd constructions and concrete
    tightly 1-, 2-, 3-, 4-, and 5-unstable q-acceptant examples remain as
    simpler witnesses, alongside the `2q` upper bound and the
    instability-calculation lemma.
  - The append/remove variability equivalence is closed in Lean in threshold
    and exact forms. Under feasibility, q-acceptance, and 1-instability, the
    appendix general variability upper bound is equivalent to the main-text
    borderline-only upper bound, and exact appendix general variability is
    equivalent to exact main-text variability. The proof constructs the
    waitlisted-to-borderline finite-family matching bridge from the paper's
    waitlisted-set witnesses.
  - LAP 1-instability and distinct-ordering variability are closed:
    `LAP.lean` derives the single-addition exchange-repair certificate for
    unique global-optimum finite assignment selectors using a directed
    alternating-splice argument, then proves the sharper variability bound by
    the number of distinct slot-induced preference orderings using a
    proper-suffix exchange.
  - The even-instability/inconsistency theorem is now closed in both
    directions: the previously missing converse is exposed by
    `paper_even_instability_inconsistency_converse_statement`.
- Next bridge lemmas to try:
  - If a future report wants the theorem in literal `max_{X ⊆ 𝓧}` syntax,
    package the current threshold/exact append-remove equivalence into a
    finite-maximum statement; the mathematical append/remove bridge itself is
    already proved.
- Informal proof sketch / recurrence / construction:
  - Continue using explicit source formulas in `PaperInterface.lean`. Do not
    encode source proof obligations as hidden record fields; if a bridge model
    is used, prove its paper-facing consequences from primitive fields.

## Deviations And Assumptions

- Source imprecision or proof deviation to report later:
  - Nontrivial capacity domain for no zero-instability.
  - Corrected statement of removable-set lemma.
  - Exact variability one exposes a displacement/nondegeneracy witness; the
    formalized q-representative result proves at-most-one unconditionally and
    exact-one with that source-level witness.
  - The main sequential-queue bound and appendix additive variability theorem
    are proved for feasible q-acceptant 1-unstable stages, with the
    q-representative queue theorem as a corollary/special case.
- Genuine paper assumptions to declare in `Assumptions.lean`:
  - None intended at intake.
- Temporary certificate fields to discharge:
  - None intended.
- Validation/audit checks that must inspect these assumptions:
  - Source-coverage audit must see the theorem-condition correction and lemma
    typo correction as source issues, not hidden Lean hypotheses.
