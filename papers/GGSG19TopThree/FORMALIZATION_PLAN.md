# Formalization Plan: Who is in Your Top Three?

This is a working scratchpad for outside-Lean proof thinking. The human-facing
post-formalization audit is `POST_FORMALIZATION_AUDIT.md`; do not turn this
file into the final audit report.

- Namespace: `GGSG19TopThree`
- Publication venue: HCOMP 2019
- Source target: arXiv 1906.08160 TeX/PDF, checked during intake.

## Source Inventory

- Definitions / formatted paper objects:
  - Asymptotic design invariance for `(M, F)` and goal `G`.
  - Large-deviation rate `r = -lim_N (1 / N) log A_N`.
  - Finite ranking laws, W-selection goals, scoring rules, K-approval rules,
    randomized rules, and Mallows ranking laws.
- Named lemmas / propositions / theorems / corollaries:
  - Proposition 1 / `thm:consistency`.
  - Proposition 2 / `thm:pairwiselearning`.
  - Proposition 3 / `lem:pairwiselearning_approval`.
  - Proposition 4 / `thm:goal_learning`.
  - Theorem 1 / `lem:randomizebetterscoring`.
  - Theorem 2 / `lem:randomizenotbetterapproval`.
  - Corollary / `lem:mallowsnorando`.
  - Theorem / `lem:randomizebetterapproval_Wselection`.
  - Theorem / `lem:mallowsnotWK`.
- Theorem-like displayed claims that are used later:
  - Pairwise score-gap log-MGF and Chernoff-rate formulas.
  - K-approval ternary rate formulas.
  - Finite relevant-pair aggregation formulas.
  - Mallows pivotal-pair probability formulas.

## Initial Proof Strategy

- Main theorem chain:
  - Pairwise finite-support log-MGF rates close Proposition 2.
  - K-approval ternary score-gap specialization closes Proposition 3.
  - Relevant-pair finite aggregation closes Proposition 4.
  - Finite ranking/tier consistency closes Proposition 1.
  - Randomized scoring, randomized K-approval, constructed W-selection, and
    Mallows endpoints consume the finite aggregation and Mallows probability
    layers.
- Likely reusable `EconCSLib` seams:
  - `EconCSLib.Foundations.Probability.FiniteSupportMGF`.
  - `EconCSLib.Foundations.Probability.LargeDeviations`.
  - `EconCSLib.SocialChoice.Ranking.Approval`.
  - `EconCSLib.SocialChoice.Ranking.MallowsRankFactorization`.
- Paper steps that look underspecified or analytically hard:
  - Finite-support one-sided and eventually-zero rate boundary cases.
  - The source's strict cross-tier condition in Proposition 1 versus same-tier
    ties in the outcome notion.
  - Empirical/numerical sections, which are reproducibility artifacts rather
    than Lean theorem targets.
- Planned fallback route if the source proof is too informal:
  - Use explicit `WithTop` rates and boundary branches.
  - Keep source-facing wrappers compact in `PaperInterface.lean`.
  - Keep detailed proof and certificate layers in `ProofInterface.lean`.

## Active Scratchpad

- Current Lean endpoint: `lake build GGSG19TopThree`.
- Exact current mathematical gap: none for the source-facing finite-candidate
  theorem surface.
- Next bridge lemmas to try:
  - None required for GGSG closeout.
  - If another Mallows/approval paper needs last-rank Mallows mass, consider
    lifting GGSG's one-loser last-rank formulas into the social-choice library.
- Informal proof sketch / recurrence / construction:
  - Pairwise finite-support rates feed K-approval specialization and finite
    aggregation.
  - Mallows endpoints reduce static K-approval comparisons to pivotal-pair and
    last-rank probability formulas.

## Deviations And Assumptions

- Source imprecision or proof deviation to report later:
  - Proposition 2-4 expose finite-support boundary branches explicitly.
  - Empirical/numerical sections are out of Lean theorem scope.
- Genuine paper assumptions:
  - Proposition 1 uses the source strict cross-tier top-prefix regime.
  - The formalized source is arXiv 1906.08160; the publication venue is HCOMP
    2019.
- Temporary certificate fields to discharge:
  - None for the source-facing finite-candidate theorem surface.
