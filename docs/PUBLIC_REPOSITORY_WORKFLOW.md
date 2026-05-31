# Public Repository Workflow

This document records the intended public/private repository split for
EconCSLib.

## Repository Roles

- `EconCSLib-private`: private full-history incubator. This repository keeps
  reusable library development, completed papers, partially verified papers,
  handoff notes, and full working history.
- `EconCSLib`: public release repository. This repository should contain the
  reusable `EconCSLib/` library, public tooling/docs, and completed paper
  formalizations only.

The private repository is the superset. The public repository is generated from
an allowlist and should not be made by changing the visibility of the private
repository.

## Public Release Rule

Do not make the full-history private repository public. Git history is
reachable even after files are deleted from the tip, so removing partial paper
folders from `main` is not enough to hide them.

For public release, create a filtered repository that keeps only:

- core Lean/library files and project configuration;
- public scripts and documentation;
- completed paper folders; and
- completed paper root modules under `papers/<Paper>.lean`.

Partially verified papers remain private until their authors choose to publish
them.

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
work-in-progress review should stay private.

Current public-ready candidates:

- `DSWG24DiscretizationBias`
- `GCG24UserItemFairness`
- `GHW01DigitalGoods`
- `GN21DriverSurgePricing`
- `GS62CollegeAdmissions`
- `LG21TestOptionalPolicies`
- `MBJG25ProducerFairness`
- `MSVV07AdWords`
- `Roth82StableMatching`

Current private/incubator candidates:

