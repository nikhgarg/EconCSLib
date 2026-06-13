# Public Release Checklist

Use this checklist before announcing a public release or inviting broad
external contributions. Last checked on 2026-06-03.

## Repository State

- [x] The intended public branch is clear. Public release docs, the Pages site
      source, and the Pages workflow live on `main`.
- [x] The private incubator remains private and is not converted into the
      public repository.
- [x] `lake build EconCSLib` passes from a clean public checkout.
- [x] The top-level `README.md` describes the public repository, not the private
      incubator.
- [x] `docs/PAPER_STATUS.md` matches the paper folders included in the public
      repository.
- [x] Each public `papers/<PaperName>/status.json` is current, and
      `python3 scripts/sync_paper_status.py --check` confirms that the generated
      `papers/status.json`, `papers/human_status.json`, and
      `docs/PAPER_STATUS.md`, `README.md`, and `site/index.html` are in sync.
- [x] The generated `README.md`, `docs/PAPER_STATUS.md`, and site status tables
      summarize the same public paper set, statuses, review counts, Lean LOC,
      and sparse notes as `papers/human_status.json`.
- [x] Status labels use `Formalized`, `Formalized with caveat`, or
      `Partially formalized`; do not publish `Verified in Lean` as a separate
      status category.
- [x] `python3 scripts/audit_repository.py` reports 0 errors. Public-release
      warnings for omitted source PDFs are acceptable when licensing requires
      source PDFs to stay out of the repository.
- [x] `CONTRIBUTING.md` states the current contribution policy and contact
      email.
- [x] `CITATION.cff` has the current repository title, author, and release date.
- [x] A repository license has been chosen and added as `LICENSE` before
      soliciting broad external code contributions.
- [x] The GitHub repository description is set. The homepage field points to
      `https://gargnikhil.com/EconCSLib/`.

## Paper Folder Readiness

Each public paper folder should have:

- [ ] a paper-local `README.md`;
- [ ] `PaperInterface.lean` as the compact human-facing theorem surface;
- [ ] `Assumptions.lean` if any paper-facing theorem premise remains as an
      explicit source/model assumption;
- [ ] `FINAL_VALIDATION_REPORT.md` or an equivalent validation summary;
- [ ] `DependencyDAG.tex` and a rendered `DependencyDAG.pdf`;
- [ ] a current `status.json`, including human-review row counts,
      `review_surface` rows/slices, `assumption_names` for any paper-model
      assumptions, artifact paths, and any PaperInterface maintenance issue;
- [ ] `assumption_match_llm.json` whenever paper-facing theorem premises remain
      as source/model assumptions rather than derived Lean facts;
- [ ] a passing `lake build <PaperTarget>` command; and
- [ ] no tracked source PDFs, extracted source-paper text caches,
      review-dashboard caches, or generated build artifacts other than
      intentional `DependencyDAG.pdf` files.

## Importing A Completed Private Paper

- [ ] Confirm the paper is ready for public review.
- [ ] Decide whether paper-local development history should be preserved.
- [ ] Filter the private history to the completed paper folder and any reusable
      library changes that are public-safe.
- [ ] Merge the filtered history into the public repository.
- [ ] Update paper-local `status.json`, run `python3 scripts/sync_paper_status.py`,
      and then update surrounding README/site prose, roadmap, or release notes
      only if needed.

## GitHub Pages Readiness

- [ ] Decide whether the reviewed workshop paper PDF should be linked
      externally or added as a final public artifact.
- [x] Run `python3 scripts/sync_paper_status.py --check` to confirm the site
      status table matches `papers/human_status.json` and
      `docs/PAPER_STATUS.md`.
- [x] The Pages workflow is tracked as `.github/workflows/pages.yml`.
- [x] Confirm the Pages workflow completes and the Pages URL serves the site.
- [x] Enable HTTPS enforcement for GitHub Pages.
