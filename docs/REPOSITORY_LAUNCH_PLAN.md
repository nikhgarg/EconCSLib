# Repository Launch Plan

This is the current maintainer plan for keeping the private and public
repositories aligned while preparing GitHub Pages.

## Current State

- `EconCSLib-private` is the private full-history incubator and remains the
  superset of paper work, handoff notes, partial formalizations, and reusable
  library development.
- `EconCSLib` is the public release repository. It is already public on GitHub,
  but broad announcement and GitHub Pages publication are still pending.
- The public `main` branch contains the public Lean library, public paper
  folders, contribution docs, status docs, and release checklist.
- The public `main` branch contains the static site source and Pages workflow.
  The workflow enables GitHub Pages through `actions/configure-pages` on the
  first successful deployment.

## Public/Private Rule

Do not make the private incubator public. Public releases should be produced by
allowlisting public-safe paths into `EconCSLib`, not by deleting private folders
from the private repository tip. Git history remains reachable after deletion.

Private or partially formalized papers should stay in private paper-specific
repositories when authors want to preserve paper-local development history for
future publication. A partial paper can still be public when its remaining gap
is explicit, documented, and useful for contributors to inspect. Once a paper
is public-ready, import the filtered history for that paper folder and any
public-safe reusable library changes.

## Pre-Announcement Checklist

1. Confirm `git status --short` is clean in `EconCSLib-private`,
   `EconCSLib-public`, and `2026_EconCSLibpaper`, or record intentional dirty
   paper edits separately.
2. Run `python3 scripts/audit_repository.py` in the public repository and
   resolve all errors.
3. Run `lake build EconCSLib` in the public repository from a clean checkout or
   clean worktree.
4. Run `python3 scripts/sync_paper_status.py --check` to confirm
   `papers/status.json`, `papers/human_status.json`, `docs/PAPER_STATUS.md`,
   `README.md`, and `site/index.html` list the same public papers and use only
   the status vocabulary in `docs/STATUS.md`.
5. Decide whether the reviewed workshop paper PDF should be linked externally
   or added as a final public artifact.
6. Decide and add the repository `LICENSE` before soliciting broad external
   code contributions.
7. Set the GitHub repository description. Set the homepage only after Pages is
   enabled and the first deployment succeeds.

## Pages Activation Sequence

1. Review `site/index.html` locally.
2. Push `main`.
3. Confirm the Pages workflow deploys from GitHub Actions.
4. Confirm the Pages URL serves the site.
5. Add the Pages URL to the repository homepage field.

## Public Partial Import Policy

LMMS04 and LOS02 are public as partial formalizations because their remaining
gaps are explicit and useful to expose. GHW01 has moved out of the partial
bucket: it is formalized using the journal version as the controlling source
where it refines the preliminary InterTrust/SODA text; Theorem 8.2 is the
journal monotone-auction statement, and Lean records the broader
technical-report wording as a refuted weak reading. LMMS04 needs
fixed-dimension integer-program runtime infrastructure; LOS02 needs
machine-level polynomial-time reductions, randomized complexity classes, and
cited Karp/Hastad-style hardness facts.

Other partial papers should stay private unless their remaining gap is similarly
explicit, reusable, documented in the paper README and validation report, and
useful for public contributors to inspect.
