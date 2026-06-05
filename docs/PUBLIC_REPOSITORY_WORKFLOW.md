# Public Repository Workflow

This document records the intended public/private repository split for
EconCSLib.

## Repository Roles

- `EconCSLib-private`: private incubator based on public `main`. This
  repository keeps reusable library development, completed papers, partially
  formalized papers, and handoff notes while preserving public ancestry for
  clean private-to-public PRs.
- `EconCSLib`: public release repository. This repository should contain the
  reusable `EconCSLib/` library, public tooling/docs, completed paper
  formalizations, and carefully documented partial formalizations whose
  remaining seams are useful public library work.

The active private repository is the working superset. The public repository is
the public release surface.

For the current launch state and Pages activation sequence, see
[`docs/REPOSITORY_LAUNCH_PLAN.md`](REPOSITORY_LAUNCH_PLAN.md).

## Public Release Rule

Do not make the full-history private repository public. Git history is
reachable even after files are deleted from the tip, so removing partial paper
folders from `main` is not enough to hide them.

For public release from an older standalone private history, create a filtered
repository that keeps only:

- core Lean/library files and project configuration;
- public scripts and documentation;
- completed paper folders;
- completed paper root modules under `papers/<Paper>.lean`; and
- explicitly approved public partial paper folders whose remaining assumptions
  are documented in their README, validation report, `papers/human_status.json`,
  and `docs/PAPER_STATUS.md`.

Partially formalized papers remain private until their authors choose to publish
them. A partial paper can be public when the remaining gap is not hidden
paper-specific proof debt but a reusable external theorem or library seam that
contributors may reasonably want to inspect or help discharge.

## Completed Paper Imports

When a paper in the active public-based private repository becomes
public-ready, prefer a topic branch forked from public `main` and open a normal
pull request against `EconCSLib`.

If the relevant work only exists in an older standalone private history,
preserve its development history by filtering only that paper's paths from the
archive and merging that filtered history into the public repository.

The filtered import should keep:

- `papers/<Paper>/`
- `papers/<Paper>.lean`
- any reusable library commits that are already public-safe

When applying work from the active private incubator, use an allowlisted patch
instead of merging the private branch. Include only the approved paper folder,
its root module, required reusable library paths, public workflow/tooling
changes, and regenerated public aggregate status/site files. Do not include
private paper folders, private-generated aggregate status rows, source-paper
PDF/text/source caches, dashboard caches, or LaTeX build artifacts other than
intentional rendered DAG PDFs.

If an older filtered-history import is used, the resulting commit hashes will
change because the commit trees are rewritten, but commit order, authorship,
messages, and paper-local diffs can be preserved without exposing unrelated
unfinished paper work.

## Public Paper Set

Do not maintain the public paper list by hand in this document. The public set,
statuses, review counts, interface metadata, and sparse status notes are
generated from paper-local `papers/<Paper>/status.json` files into
`papers/status.json`, `papers/human_status.json`, `docs/PAPER_STATUS.md`, the
root README status block, and the site status table.

Other partial or in-progress paper work should remain in the private incubator
until it is ready for public review.
