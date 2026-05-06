# Validation Report: Roth 1982 Matching

## 1. Source and Scope
- Paper: *The Economics of Matching: Stability and Incentives* (Roth 1982)
- Source version: Mathematics of Operations Research, Vol. 7, No. 4 (Nov., 1982)
- Lean folder: `papers/Roth82StableMatching/`
- Human-facing theorem file: `papers/Roth82StableMatching/PaperInterface.lean`
- Post-paper audit ledger: `papers/Roth82StableMatching/PostPaperAudit.lean`,
  imported by `papers/Roth82StableMatching.lean`
- DAG artifacts: `papers/Roth82StableMatching/DependencyDAG.tex`,
  `papers/Roth82StableMatching/DependencyDAG.pdf`

## 1.1 Post-Paper Audit Checklist
- Cached-text named-result inventory:
  Theorem 1 (line 227), Theorem 2 (line 258), Theorem 3 (line 356),
  Theorem 4 (line 438), Theorem 5 (line 468), Corollary 5.1 (line 477),
  Lemma 1 (line 537), Lemma 2 (line 564), Theorem 6 (line 678), and
  Theorem 7 (line 713) in `Roth82StableMatching.txt`. No numbered source
  propositions or definitions were found by the named-result search.
- README check: every named result has a controlled-status row in
  `papers/Roth82StableMatching/README.md`; all source endpoints are marked
  `formalized`.
- DAG check: `DependencyDAG.tex` marks all named source results as closed and
  renders to `DependencyDAG.pdf`; the Theorem 3 to Theorem 7 edge is solid
  because the arbitrary-`k` padded proof now uses the formal Theorem 3 route.
- Lean audit check: `PostPaperAudit.lean` exposes one source-numbered audit
  endpoint per final paper result, and the paper root imports it.
- Verification checks covered the paper Lean build, placeholder scan over the
  Roth and matching Lean files, stale-status scan over Roth docs, whitespace
  diff check, and DAG rendering from the paper folder.

## 2. Theorem-by-Theorem Validation
| Paper item | Lean declaration | Status | Statement match | Notes |
|---|---|---|---|---|
| Theorem 1 (stable outcomes are nonempty) | `paper_roth82_theorem1_stable_outcome_exists`, `paper_roth82_theorem1_stable_complete_outcome_exists_on_strict_marriage_domain` | formalized | exact wrapper plus source-domain complete-outcome endpoint | DA step-invariant preservation, finite-fold termination, and the terminated-invariant stability proof are closed in `EconCSLib`. On Roth's equal-size strict marriage domain, Lean also proves the DA output is complete. |
| Theorem 2 (men- and women-optimal stable outcomes exist) | `paper_da_is_men_optimal_on_strict_marriage_domain`, `paper_da_is_women_optimal_on_strict_marriage_domain`, `paper_roth82_theorem2_optimal_stable_outcomes_on_strict_marriage_domain`, plus generic certificate wrappers | formalized | source strict marriage domain | The theorem is proved from a reusable DA rejected-pair invariant and role reversal. Roth explicitly assumes complete/transitive strict preferences and excludes indifference; the positive strict-utility encoding represents that source domain with no outside option. Arbitrary-utility wrappers remain compatibility APIs. |
| Theorem 3 (no stable procedure is strategyproof for all agents) | `theorem3_stable_base_eq_x_or_y`, `theorem3_stable_woman_prime_eq_y`, `theorem3_stable_man_double_prime_eq_x`, `paper_roth82_theorem3_no_stable_truthful_procedure` | formalized | source counterexample route | The 3-by-3 profiles, stable-set enumerations `C(P) = {x,y}`, `C(P') = {y}`, `C(P'') = {x}`, stable-procedure behavior, and manipulation contradiction are formalized. |
| Theorem 4 (efficient strategyproof procedures exist) | `paper_serial_dictatorship_mechanism`, `paper_roth82_theorem4_serial_dictatorship_constructed`, `paper_roth82_theorem4_serial_dictatorship_route`, `paper_roth82_theorem4_efficient_strategyproof_procedure_exists` | formalized | constructed serial dictatorship on the indexed strict finite marriage domain | Lean constructs the serial-dictatorship mechanism and proves efficiency, men-truthfulness, and women-truthfulness on Roth's canonical indexed finite marriage domain `Fin n`. The older fully generic existence wrapper remains a certificate API. |
| Theorem 5 (one-sided truthfulness of optimal stable procedure) | `paper_da_no_profitable_strict_simple_report_on_strict_domain_of_card_eq`, `paper_da_truthful_for_men_on_strict_domain_of_card_eq`, `paper_da_truthful_for_women_on_strict_domain_of_card_eq`, `paper_roth82_theorem5_men_truthful_on_strict_domain_of_card_eq`, `paper_roth82_theorem5_women_truthful_on_strict_domain_of_card_eq`, `paper_roth82_theorem5_optimal_side_truthful_on_strict_domain_of_card_eq`, plus reduction and trace helpers including `paper_strict_top_report` and `paper_da_top_rejected_proposer_later_match_time` | formalized | source equal-size strict marriage domain | Lean formalizes Roth's reduction from arbitrary reports to strict simple reports, uses the closed Lemma 2 no-harm theorem, proves the no-new-low-proposal and unique-truthful-proposer base bridges, discharges the top-rejected-proposer later-match-time induction, and obtains the women-proposing side by role reversal. The older generic/certificate wrappers remain compatibility APIs outside the source-domain endpoint. |
| Corollary 5.1 | `paper_da_no_need_to_misrepresent_first_choice_for_women_on_strict_domain`, `paper_roth82_corollary5_1_no_need_to_misrepresent_first_choice_on_strict_domain`, `paper_da_raise_first_choice_trace_eq_or_holds_top`, `paper_da_raise_first_choice_report_weakly_dominates`, `paper_exists_strict_top_choice_for_woman`, `paper_raise_first_choice_report_preserves_woman_first_choice`, `paper_da_true_first_choice_proposal_implies_final_true_first_choice`, `paper_da_true_first_choice_proposal_no_profitable_woman_report`, `paper_da_profitable_woman_report_implies_true_first_choice_not_proposed`, plus older compatibility wrappers | formalized | source-faithful strict-domain endpoint | Closed for nonempty finite strict marriage markets. Lean exposes the source-faithful reading as "every report is weakly matched by some report preserving the true first choice", proves first-choice existence, raises that man above an arbitrary report, proves the bad and raised DA traces are equal until the raised trace holds the true first choice, and then uses top-choice persistence to prove weak dominance. The older no-profitable-false-top certificate wrapper is stronger than the source reading and is retained only as a caveated compatibility API. |
| Lemma 1 | `paper_simple_report_preserves_stability_of_partner`, `paper_roth82_lemma1_strict_simple_misrepresentation_same_partner`, plus generic wrapper `paper_roth82_lemma1_simple_misrepresentation_same_partner` | formalized | strict simple-report route from Theorem 2 | Closed for Roth's source strict marriage domain, where the outcome gives the manipulator a concrete partner and the replacement report strictly ranks that partner first. The older fully generic wrapper remains a certificate API. |
| Lemma 2 | `paper_da_simple_report_no_nonmanipulator_truthful_partner_crossing`, `paper_da_strict_simple_report_no_men_harmed_on_strict_domain`, `paper_roth82_lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain`, plus trace bridges including `paper_da_simple_report_first_crossing_proposer_ne_manipulator`, `paper_da_removed_truthful_partner_before_active_step_yields_earlier_crossing`, and the compatibility wrapper `paper_roth82_lemma2_simple_misrepresentation_no_men_harmed` | formalized | source strict simple-report route on equal-size strict marriage domains | Lean now proves Roth's minimal first-rejection induction. A worse non-manipulator gives a first crossing at his truthful DA partner; the crossing proposer is not the manipulator under the simple-report top-partner condition; the proposer has already proposed to his own truthful partner at an earlier step; and DA rejection invariants produce an even earlier crossing, contradicting minimality. The older generic certificate wrapper remains for compatibility outside the source-domain statement. |
| Theorem 6 | `daStateAfterSteps`, `Assignment.m_complete_of_w_complete_of_card_eq`, `deferredAcceptance_complete_of_card_eq_all_pairs_acceptable`, `paper_da_last_active_step_at_time_of_complete`, `paper_da_last_active_step_at_time_implies_final_unmatched_woman_step_at_time`, `paper_da_last_unique_proposal_implies_weak_pareto_for_men`, `paper_da_complete_on_strict_marriage_domain_of_card_eq`, `paper_roth82_theorem6_on_strict_marriage_domain`, plus generic wrapper `paper_roth82_theorem6_no_feasible_outcome_strictly_better_for_all_men` | formalized | source strict equal-size marriage domain | Closed for Roth's nonempty equal-size strict marriage domain. Lean proves DA completeness from equal cardinality and all-pairs acceptability, derives the last active proposal step, proves Roth's final unique-proposal observation, and derives weak Pareto. |
| Theorem 7 | `paper_rank_of_choice`, `paper_report_misrepresents_kth_choice`, `paper_stable_procedure_has_profitable_kth_choice_misreport`, `paper_no_stable_procedure_avoids_kth_choice_manipulation_on`, `PaperTheorem7ArbitraryKFamilyCertificate`, `Theorem7RankManipulationCounterexample`, `theorem7Padded_counterexample_has_profitable_rank_misreport`, `paper_roth82_theorem7_arbitrary_k_family_statement`, `paper_roth82_theorem7_arbitrary_k`, `paper_roth82_theorem7_second_choice_counterexample`, `paper_roth82_theorem7_third_choice_counterexample`, `paper_roth82_theorem7_second_or_third_choice_counterexample`, `paper_roth82_theorem7_second_or_third_choice_source_statement`, `paper_roth82_theorem7_second_or_third_choice_family_statement`, `paper_roth82_theorem7_arbitrary_k_of_family_certificate` | formalized | arbitrary `k > 1` padded Theorem 3 family | Lean defines the general rank-based `k`th-choice misreport predicate and proves the source-facing "no stable procedure avoids `k`th-choice manipulation" property for every `k > 1`. The proof pads Roth's Theorem 3 profile with forced dummy pairs, proves the padded manipulated reports alter rank `r + 2`, restricts padded stable outcomes back to the Theorem 3 core, and derives a profitable woman-side or man-side manipulation for any stable procedure. |

## 3. Additional Assumptions Beyond Paper
- Source-domain note: Roth Section 2 explicitly assumes complete/transitive
  strict preference relations and then says only strict preferences will be
  considered. Strict preferences are therefore not an additional Lean caveat for
  Theorems 2, 4, 5, 6, Corollary 5.1, or Lemma 1.
- Generic DA truthfulness and simple-misreport certificate APIs remain in the
  file for compatibility with arbitrary utility profiles, but the source-domain
  Lemma 2, Theorem 5, and Corollary 5.1 wrappers no longer assume those
  certificates.
- `DaNoNeedToMisrepresentFirstChoiceForWomenCertificate`: an older
  compatibility certificate API for Corollary 5.1. The source strict-domain
  endpoint is now closed by
  `paper_da_no_need_to_misrepresent_first_choice_for_women_on_strict_domain`.
- `DaNoProfitableFirstChoiceMisreportForWomenCertificate`: an older broad
  no-profitable-false-top wrapper retained as a compatibility/caveat API; it is
  stronger than Roth's proof-language reading.

## 4. Proof-Strategy Deviations
- Theorem 2's men side is proved by carrying a reusable DA
  rejected-pair-impossibility invariant through the finite fold; this formalizes
  Roth's "possible woman" induction. The women side is then proved by the
  generic matching-side swap lemma (`EconCSLib.Matching.isStable_swap_iff`) and
  role-reversed deferred acceptance.
- The DA stability proof is factored through
  `foldl_daStep_preserves_invariants` and
  `stable_of_invariants_and_terminated`, closed generic theorems in
  `EconCSLib.Markets.Matching.DeferredAcceptance`.
- Theorem 1 has both a generic optional-partner stability wrapper and a
  source-domain stable-complete endpoint for equal-size strict marriage markets.
- Theorem 3 is split into explicit finite stable-set enumeration lemmas and the
  manipulation contradiction. The final paper-facing wrapper derives the
  contradiction from `paper_stable_matching_procedure` on the three-by-three
  counterexample domain.
- Theorem 4 is closed by an explicit indexed finite-marriage serial-dictatorship
  construction over `Fin n`. The older generic certificate wrapper is retained
  as an API for arbitrary finite types, but the source-facing proof follows
  Roth's strict-preference domain.
- Lemma 1 is proved by formalizing Roth's Theorem 2 route: the arbitrary-report
  DA outcome remains stable under the strict simple report, and men-optimality
  of the simple-profile DA outcome forces the manipulating man to keep the same
  partner.
- Theorem 5 is decomposed further on both proposing sides: Lean constructs a
  canonical positive strict top report for any reported partner, proves that
  arbitrary profitable reports reduce to strict simple profitable reports on the
  strict marriage domain, applies Lemma 2's no-harm theorem, proves the
  source proof's no-new-low-proposal and unique-truthful-proposer base bridges,
  and discharges the top-rejected-proposer later-match-time induction. The
  women side is obtained by role reversal.
- Lemma 2 is now closed on the equal-size strict marriage domain for Roth's
  strict simple-report route. Lean proves the proposal-removal and woman-side
  monotonicity bridges, packages the first crossing at a worse man's truthful
  partner, rules out the crossing proposer being the manipulator by using the
  simple report's unique top final partner and a no-rematch invariant, and then
  derives an earlier crossing for the proposer's truthful partner. Choosing the
  minimal crossing time gives the formal contradiction.
- Theorem 6 is decomposed through the final active proposal step over
  `daStateAfterSteps`. Lean proves DA completeness from equal cardinality and
  all-pairs acceptability, derives a final active step, proves that this step is
  a final unmatched-woman trace fact, proves Roth's final unique-proposal
  observation, and then derives weak Pareto optimality.
- Corollary 5.1 is represented by a source-faithful "no need to misrepresent
  first choice" interface instead of only the older broad false-top-report
  predicate. Lean closes the strict-domain endpoint by raising the true first
  choice above any arbitrary report, proving a DA trace split showing equality
  until the raised trace holds that first choice, proving top-choice
  persistence after it is held, and deriving weak dominance. The earlier
  proof-line lemmas about true-first-choice proposals remain available.
- Theorem 7 has a general rank-based `k`th-choice misreport predicate and a
  source-facing arbitrary-family theorem. Lean follows Roth's Theorem 3 route
  by padding the counterexample with forced dummy pairs, proving the manipulated
  alternative has true rank `r + 2`, and reducing padded stable outcomes back to
  the Theorem 3 stable-set enumeration.

## 5. Conditional Results and Remaining Gaps
- No source-theorem gaps remain for the named results in the cached Roth 1982
  text. Older generic/certificate APIs remain as compatibility surfaces outside
  the source-domain endpoints.

## 5.1 Reusable Library Material
- Already extracted into `EconCSLib/Markets/Matching/Basic.lean`: assignment
  side-swap, assignment extensionality from man-side matches, completeness
  transfer across equal-cardinality sides, and stability invariance under side
  swap.
- Already extracted into `EconCSLib/Markets/Matching/DeferredAcceptance.lean`:
  DA run-prefix states, proposal-removal and proposal-monotonicity lemmas,
  finite-fold termination/stability closure, all-pairs-acceptable completeness,
  strict-preference profile predicates, the rejected-pair impossibility
  invariant, and the reusable DA men-optimality theorem.
- Remaining extraction candidates: generic direct-mechanism incentive
  predicates, Pareto/efficiency predicates for complete assignments, finite
  serial-dictatorship APIs, and rank-based report-misrepresentation predicates.
  They remain in the Roth paper namespace for this commit because their current
  names and statements are still paper-facing wrappers; moving them cleanly
  should be a separate API-design pass.

## 6. Suspected Paper Errors or Inconsistencies
- None

## 7. Final Verdict
- Completion status: all named source results in the cached Roth 1982 text are
  source-domain formalized
- Summary: The paper-facing definitions, Theorem 1 DA stable-complete existence,
  Theorem 2 source strict-domain men/women optimal stable outcomes, Theorem 3 finite
  counterexample impossibility, Theorem 4 indexed finite-domain serial-dictatorship
  construction, Theorem 5 equal-size strict-domain one-sided truthfulness, Lemma 1
  strict simple-report route, Lemma 2
  strict simple-report source route, Corollary 5.1 source-faithful strict-domain
  endpoint, Theorem 6 source-domain
  weak Pareto endpoint through DA completeness and the final-active-step route
  plus the generic conditional weak Pareto
  wrapper, Theorem 7 arbitrary `k > 1` padded counterexample family, DA step-invariant preservation,
  finite-fold termination, and the generic fold/invariant proof path to stability
  compile. The full Roth 1982 theorem sequence is verified on the documented
  source domains; generic DA truthfulness and Lemma 2 certificate wrappers are
  retained only as broader compatibility APIs.
