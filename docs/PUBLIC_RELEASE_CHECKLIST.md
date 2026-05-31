# Public Release Checklist

Use this checklist before announcing a public release or inviting broad
external contributions.

## Repository State

- [ ] `lake build EconCSLib` passes from a fresh clone.
- [ ] The top-level `README.md` describes the public repository, not the private
      incubator.
- [ ] `docs/PAPER_STATUS.md` matches the paper folders included in the public
      repository.
- [ ] Status labels use `Formalized`, `Formalized with caveat`, or
      `Partially formalized`; do not publish `Verified in Lean` as a separate
      status category.
- [ ] `python3 scripts/audit_repository.py` reports 0 errors. Public-release
      warnings for omitted source PDFs are acceptable when licensing requires
      source PDFs to stay out of the repository.
- [ ] `CONTRIBUTING.md` states the current contribution policy and contact
      email.
- [ ] `CITATION.cff` has the current repository title, author, and release date.
- [ ] A repository license has been chosen and added as `LICENSE` before
      soliciting broad external code contributions.

## Paper Folder Readiness

Each public paper folder should have:

- [ ] a paper-local `README.md`;
- [ ] `PaperInterface.lean` as the compact human-facing theorem surface;
- [ ] `FINAL_VALIDATION_REPORT.md` or an equivalent validation summary;
- [ ] `DependencyDAG.tex`, with rendered PDFs kept local unless intentionally
      published;
- [ ] a passing `lake build <PaperTarget>` command; and
- [ ] no tracked source PDFs, review-dashboard caches, or generated build
      artifacts.

## Importing A Completed Private Paper

- [ ] Confirm the paper is ready for public review.
- [ ] Decide whether paper-local development history should be preserved.
- [ ] Filter the private history to the completed paper folder and any reusable
      library changes that are public-safe.
- [ ] Merge the filtered history into the public repository.
- [ ] Update `README.md`, `docs/PAPER_STATUS.md`, and the relevant roadmap or
      release notes.

## GitHub Pages Readiness

- [ ] Rebuild the workshop paper PDF and refresh
      `site/assets/econcslib-workshop-draft.pdf`.
- [ ] Confirm the site status table matches `docs/PAPER_STATUS.md`.
- [ ] Keep `.github/workflows/pages.yml.disabled` disabled until the repository
      is ready to publish Pages.
