# GitHub Pages Publishing Plan

This document records how to publish the project site when the paper and public
repository are ready.

## Current State

- The public GitHub repository `nikhgarg/EconCSLib` exists and is public.
- GitHub Pages is not configured for the repository as of 2026-05-31.
- The draft site lives on the local `pages-scaffold` branch under `site/`.
- The workflow file is intentionally disabled as
  `.github/workflows/pages.yml.disabled`.
- GitHub Pages is not enabled by this scaffold.
- No paper PDF is checked into this public repository yet.
- The default branch remains `main`; merge or fast-forward the scaffold only
  after the paper draft and public status table are ready to announce.

## Before Publishing

1. Decide whether the paper PDF should be linked externally or added as a final
   reviewed public artifact.
2. Review `site/index.html` for accurate paper status and contact text.
3. Confirm `papers/status.json`, `docs/PAPER_STATUS.md`, and the site status
   table describe the same papers, statuses, review counts, and interface
   maintenance notes.
4. Run `python3 scripts/audit_repository.py` and confirm there are 0 errors.
5. Preview the static site locally, for example:

   ```bash
   python3 -m http.server 8765 --directory site
   ```

   Then check the home page.
6. Rename `.github/workflows/pages.yml.disabled` to
   `.github/workflows/pages.yml`.
7. Push the branch or merge it into `main`.
8. In GitHub repository settings, set Pages to deploy from GitHub Actions.
9. Set the repository homepage URL to the Pages URL once the first deploy
    succeeds.

## Updating After Publication

Treat the site as a summary layer. The source of truth remains:

- `README.md` for the public repository overview;
- `docs/PAPER_STATUS.md` for paper-level status;
- paper-local `FINAL_VALIDATION_REPORT.md` files for detailed caveats; and
- `CONTRIBUTING.md` for the contribution policy.

When a paper status changes, update those files first, then update the site.
