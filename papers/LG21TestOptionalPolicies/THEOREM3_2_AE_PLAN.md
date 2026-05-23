# Theorem 3.2 A.E. Repair Plan

## Source Reading

The paper's Theorem 3.2 proof is not trying to exhibit a literal upper-tail
source equilibrium. It argues by contradiction: if a positive fraction reports
and fairness equalizes the access/no-access estimate laws, then the reported
and unreported estimate laws coincide. For a point-estimate Gaussian policy,
that makes the no-report estimate use the mean of the reported-score
distribution. Since some reporting types lie weakly below that mean, those
types would prefer withholding, so the positive-reporting situation is not an
equilibrium unless the policy is test-blank or no one reports.

## Formal Repair

The old pointwise source-equilibrium encoding is too strong for continuous
type spaces and also points in the wrong direction when used as a fully
specified upper-tail equilibrium assumption. The faithful route is:

1. Add a generic `IsChoiceEquilibriumAE` predicate over a measure on
   information states.
2. Add `lg21SourceEquilibriumAE` as the LG21 source wrapper.
3. Prove a.e. optional-reporting best-response consequences, especially:
   among types that report, no-report payoff is not better than report payoff
   for almost every realized type.
4. Use the paper's fairness-to-law-equality and reported-score-mean bridge to
   create a positive-measure set of reporters below the relevant mean.
5. Contradict the a.e. best-response theorem on that positive-measure set.

The key new knowledge is that the paper's proof is not an equilibrium-existence
proof for a literal "report above the upper-tail mean" source game. It is an
instability proof: any positive reporting/taking mass plus fairness-generated
resampling equality gives a below-mean positive-measure set that wants to
deviate. Therefore the final paper-facing Theorem 3.2 route should not assume
`lg21FullySpecified...UpperTailSourceEquilibriumData` is a source equilibrium.
Those declarations are diagnostics or old staging artifacts. The closure route
should consume an a.e. equilibrium over the actual type law and a positive-mass
below-mean witness.

## Implementation Order

1. Done: add reusable `IsChoiceEquilibriumAE`.
2. Done: add `lg21SourceEquilibriumAE` plus optional/report-required a.e.
   best-response projections.
3. Done: add affine corollaries converting a.e. best response into
   `actorMean <= score` for reporters and `actorMean <= skill` for takers.
4. Done: add abstract positive-mass contradiction lemmas for both regimes:
   a.e. reporters/takers cannot all be above the imputed mean if the realized
   law gives positive mass to reporters/takers strictly below that mean.
5. Done: expose these a.e. endpoints through `ProofInterface`,
   `PostPaperAudit`, and `PaperInterface`, so the audited theorem surface uses
   the repaired route rather than the old pointwise upper-tail source
   equilibrium staging declarations.
6. Done: add cutoff-interval and base-local cutoff-interval a.e. instability
   certificates, plus optional-reporting/report-required Gaussian upper-tail
   interval versions. These consume positive mass on `[cutoff, upperTailMean)`
   and route it into the a.e. best-response contradiction.
7. Done: specialize the positive-below-mean witness to Gaussian threshold
   laws via `GaussianScaleLaw.toMeasure_Ico_pos`, fixed-base pushforward laws,
   paper `P_BO` threshold wrappers, and family-level a.e. marginal-law
   contradictions.
8. Done: add compact repaired a.e. certificates:
   `LG21OptionalReportingGaussianPosteriorPBOAECertificate.false_of_nonempty`
   and `LG21ReportRequiredAffineSkillPBOAECertificate.false_of_nonempty`.
9. Done: add source-law model wrappers for the repaired a.e. route:
   `LG21OptionalReportingGaussianPosteriorPBOAESourceLawModel` and
   `LG21ReportRequiredAffineSkillPBOAESourceLawModel`.  These bundle the
   source equilibrium, `P_BO` threshold rule, observable-law identities, and the
   Gaussian upper-tail marginal-law assumption only at nonblank relevance
   witnesses, then expose Section 3 fairness iff no test relevance.

## Distance to Paper Completion

This repair removes the major conceptual blocker for Theorem 3.2. Theorem 3.2
is now closed on the paper-facing source-law model route, with the abstract
a.e. equilibrium/instability seam compiled. Remaining diagnostic cleanup is
roughly:

- optional-reporting and report-required top-level paper wrappers now exist
  over the repaired nonblank-conditioned a.e. source-law model;
- decide how much of the older pointwise upper-tail source-equilibrium staging
  surface should stay visible as diagnostics.

Current distance estimate after the a.e. fix:

- Theorem 3.2: closed for the paper-facing source-law route; the Gaussian
  law/witness bridge, repaired a.e. certificate route, and
  nonblank-conditioned source-law model wrappers compile.
- Theorem 3.1: closed for the paper-facing source-equilibrium routes, including
  optional-reporting source equilibrium and report-required a.e. source
  equilibrium.
- Theorem 4.4/resampling: closed in the named paper interface; it is not a
  blocker for Section 3.

Overall, the main continuous-law Theorem 3.2 obstruction is closed for the
paper-facing source-law models. Future work should only revisit this if the
desired target is a deliberately broader abstraction than the paper model.
