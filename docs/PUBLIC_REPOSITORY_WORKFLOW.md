# Public Repository Workflow

This document records the intended public/private repository split for
EconCSLib.

## Repository Roles

- `EconCSLib-private`: private full-history incubator. This repository keeps
  reusable library development, completed papers, partially formalized papers,
  handoff notes, and full working history.
- `EconCSLib`: public release repository. This repository should contain the
  reusable `EconCSLib/` library, public tooling/docs, completed paper
  formalizations, and carefully documented partial formalizations whose
  remaining seams are useful public library work.

The private repository is the superset. The public repository is generated from
an allowlist and should not be made by changing the visibility of the private
repository.

For the current launch state and Pages activation sequence, see
[`docs/REPOSITORY_LAUNCH_PLAN.md`](REPOSITORY_LAUNCH_PLAN.md).

## Public Release Rule

Do not make the full-history private repository public. Git history is
reachable even after files are deleted from the tip, so removing partial paper
folders from `main` is not enough to hide them.

For public release, create a filtered repository that keeps only:

- core Lean/library files and project configuration;
- public scripts and documentation;
- completed paper folders;
- completed paper root modules under `papers/<Paper>.lean`; and
- explicitly approved public partial paper folders whose remaining assumptions
  are documented in their README, validation report, and `docs/PAPER_STATUS.md`.

Partially formalized papers remain private until their authors choose to publish
them. A partial paper can be public when the remaining gap is not hidden
paper-specific proof debt but a reusable external theorem or library seam that
contributors may reasonably want to inspect or help discharge.

## Completed Paper Imports

When a private paper becomes public-ready, preserve its development history by
filtering only that paper's paths from the private repository and merging that
filtered history into the public repository.

The filtered import should keep:

- `papers/<Paper>/`
- `papers/<Paper>.lean`
- any reusable library commits that are already public-safe

The resulting commit hashes will change because the commit trees are rewritten,
but commit order, authorship, messages, and paper-local diffs can be preserved
without exposing unrelated unfinished paper work.

## Public-Ready Paper Set

The initial public allowlist should be conservative. Papers marked partial,
waiting for stronger-model pickup, or otherwise not ready for public
work-in-progress review should stay private unless their remaining gap is
explicitly approved for public review.

Current public-ready candidates:

- `DSWG24DiscretizationBias`
- `GCG24UserItemFairness`
- `GN21DriverSurgePricing`
- `GS62CollegeAdmissions`
- `LG21TestOptionalPolicies`
- `MBJG25ProducerFairness`
- `MSVV07AdWords`
- `Roth82StableMatching`

Current public partial candidates:

- `GHW01DigitalGoods`, because its reusable auction primitives and many named
  endpoints are public-useful, while the remaining gap is explicit
  model-certificate discharge for Theorems 8.2 and 9.3.
- `LMMS04FairDivision`, because its open Theorem 3.3 PTAS/FPTAS runtime claim
  is isolated behind a fixed-dimension IP solver/complexity seam.
- `LOS02CombinatorialAuctions`, because its auction, greedy approximation,
  critical-price, and truthfulness endpoints are closed; the remaining Theorem
  6.1 consequences require reusable machine-level complexity and cited
  hardness infrastructure.

Other partial or in-progress paper work should remain in the private incubator
until it is ready for public review.
