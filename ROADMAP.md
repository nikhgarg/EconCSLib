# EconCSLib Roadmap

## Vision

EconCSLib aims to become a reusable Lean 4 library and audit trail for
Economics and Computation. The repository separates paper-independent EC
mathematics under `EconCSLib/` from source-faithful paper formalizations under
`papers/`.

## Phase 1: Public Release Hardening

- Keep `lake build EconCSLib` green on every public commit.
- Keep each public paper folder reviewable from `FINAL_VALIDATION_REPORT.md`,
  `PaperInterface.lean`, `DependencyDAG.tex`, and `README.md`.
- Keep the top-level README concise and route detailed paper status to
  `docs/PAPER_STATUS.md` and paper-local ledgers.
- Publish additional paper formalizations only once their paper-facing ledger
  and validation report are ready for public review.
- Publish a partial paper only when the remaining assumption is explicit and
  useful to expose publicly. LMMS04 and LOS02 are the current examples; both
  expose reusable complexity-library seams.

## Phase 2: Reusable EC Library Growth

Upstream reusable facts when they pass the second-paper test: a definition,
lemma, theorem interface, or proof pattern should move into `EconCSLib/` when
it is likely to support more than one paper.

Current high-value areas:

- finite sums, inequalities, and asymptotic helpers;
- finite and continuous probability primitives;
- matching markets and stability;
- mechanism-design interfaces for auctions and incentives;
- online algorithms and competitive-analysis certificates;
- fair-division primitives; and
- recommender-system and fairness models.
- complexity and runtime interfaces for externally supplied algorithmic
  certificates, starting with the LMMS04 fixed-dimension IP solver boundary and
  the LOS02 machine-level NP-hardness/`NP = ZPP` boundary.

### STV/RCV Social-Choice Cluster

The next new-paper cluster from the private backlog should be treated as a
shared library project before paper-local theorem work. The target cluster is:

- Deshpande--Garg--Jacobson, *Optimal Strategies in Ranked-Choice Voting*.
  This has the largest finite formal core: ballots, deterministic STV/RCV
  traces, quota/election/elimination rounds, transfers, tie-breaking, final
  social-choice orders, structure regions, and strategy reductions.
- Deshpande--Garg--Jacobson, *Simpler Than You Think: The Practical Dynamics of
  Ranked Choice Voting*. Treat this as a second application of the STV/RCV
  library; expect a partial formalization boundary around empirical and audit
  claims.
- Garg--Gurnee--Rothschild--Shmoys, *Combatting Gerrymandering with Ranked
  Choice Voting*. Treat this as the first post-library paper: it has the
  shortest mathematical target, combining a compact STV seat-share statement, a
  Thiele/PAV rounding lemma, and explicit redistricting/simulation boundaries.

Existing ranking modules cover useful permutation, Mallows, and score
primitives, but they do not provide an STV/RCV election semantics. Build the new
work under `EconCSLib/SocialChoice/Voting` rather than overloading the existing
ranking hierarchy.

Recommended shared modules:

- `EconCSLib/SocialChoice/Voting/Ballot`: finite candidates, partial rankings,
  active-candidate filtering, and next-active preference.
- `EconCSLib/SocialChoice/Voting/STV`: quotas, active sets, tallies, winner and
  elimination steps, transfer rules, tie-breaking, and deterministic traces.
- `EconCSLib/SocialChoice/Voting/STV/Structures`: final order / win-loss
  sequence structures, trace replay, and region-validity predicates.
- `EconCSLib/SocialChoice/Voting/Thiele`: approval ballots, Thiele scores, PAV,
  Thiele-squared, and committee-score comparisons.
- Later: ballot-addition/change strategy vectors, proportionality/seat-share
  metrics, and data/simulation boundary certificates.

Initial milestones:

1. Build the STV/RCV core library and prove deterministic trace/replay
   invariants on finite elections.
2. Start `GGRS26CombattingGerrymanderingRCV` as the first paper formalization
   after the library pass, closing the PAV/STV seat-share boundary before
   touching redistricting/simulation code.
3. Reuse the library in the two Deshpande--Garg--Jacobson RCV papers, marking
   empirical prediction, election-audit, and runtime claims as explicit
   data/code boundaries rather than Lean theorem targets.

Estimated scale: the core library plus the first gerrymandering seat-share
boundary should be the shortest route to a visible STV/RCV paper result. The
`OptimalStrategiesRCV` core likely takes several weeks because it requires full
structure/replay and strategy-reduction machinery. The practical-dynamics paper
should be planned as a partial/application formalization unless its empirical
pipeline is separately certified.

## Phase 3: Paper Contribution Pipeline

The public workflow should make it straightforward for contributors to develop
paper formalizations privately and submit them when complete. A public paper
contribution should include a compact `PaperInterface.lean`, a theorem-status
ledger, a dependency DAG, a validation report, and a reproducible build target.

Partially formalized papers may remain in private repositories until their
authors are ready to publish them. When a paper becomes public-ready, its
paper-local history can be imported with filtered history rather than exposing
unrelated unfinished work.

## Phase 4: Agent-Assisted Formalization

EconCSLib also serves as a testbed for AI-assisted formalization workflows.
The `skills/econcs-formalizer/` bundle records reusable instructions and proof
patterns for agents that ingest a source paper, build a theorem inventory,
identify reusable library seams, and produce Lean code plus human-review
artifacts.
