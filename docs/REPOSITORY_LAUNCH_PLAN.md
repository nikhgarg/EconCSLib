# Repository Launch Plan

This is the current maintainer plan for keeping the private and public
repositories aligned after the initial public launch.

## Current State

- `EconCSLib-private` is the active private incubator, with history based on
  public `main` so private paper branches can become public PRs cleanly.
- `EconCSLib-private-archive-20260601` preserves the old standalone private
  repository history.
- `EconCSLib` is the public release repository. It is public on GitHub, has CI
  enabled, and publishes GitHub Pages from `main`.
  GitHub Pages is live at `https://gargnikhil.com/EconCSLib/`.
- The public `main` branch contains the public Lean library, public paper
  folders, contribution docs, status docs, and release checklist.
- The public `main` branch contains the static site source and Pages workflow.

## Public/Private Rule

Do not make the private incubator or archive public. Public releases should be
produced by scoped branches or filtered imports into `EconCSLib`, not by
changing private repository visibility.

Private or partially formalized papers should stay private until authors choose
to publish them. A partial paper can still be public when its remaining gap is
explicit, documented, and useful for contributors to inspect. Once a paper is
public-ready, use a branch based on public `main`; if the needed history only
exists in the archive, import the filtered history for that paper folder and
any public-safe reusable library changes.

## Pre-Announcement Checklist

As of 2026-06-03, the public repository is clean, `lake build EconCSLib`
passes, `python3 scripts/sync_paper_status.py --check` passes,
`python3 scripts/audit_repository.py` reports 0 errors, CI is green, Pages is
deployed, the repository description is set, and the homepage points to the
Pages URL.

For future public-release checkpoints:

1. Confirm `git status --short` is clean in `EconCSLib-private` and
   `EconCSLib`, or record intentional dirty paper edits separately.
2. Run `python3 scripts/audit_repository.py` in the public repository and
   resolve all errors.
3. Run `lake build EconCSLib` in the public repository from a clean checkout or
   clean worktree.
4. Run `python3 scripts/sync_paper_status.py --check`, then confirm
   `papers/human_status.json`, `docs/PAPER_STATUS.md`, `README.md`, and
   `site/index.html` list the same public papers and use only the status
   vocabulary in `docs/STATUS.md`.
5. Decide whether the reviewed workshop paper PDF should be linked externally
   or added as a final public artifact.
6. Confirm the public repository `LICENSE` and citation metadata before
   soliciting broad external code contributions.
7. Confirm the repository description and homepage URL.

The remaining pre-announcement decision is whether the reviewed workshop paper
PDF should be linked externally or added as a final public artifact.

## Pages Maintenance

1. Review `site/index.html` locally when making site changes.
2. Run `python3 scripts/sync_paper_status.py --check` when status rows or
   generated site rows change.
3. Push `main`.
4. Confirm the Pages workflow deploys from GitHub Actions.
5. Confirm `https://gargnikhil.com/EconCSLib/` serves the updated site.

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
