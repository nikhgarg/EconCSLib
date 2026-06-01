# GitHub Pages Publishing Plan

This document records how to publish the project site when the paper and public
repository are ready.

## Current State

- The public GitHub repository `nikhgarg/EconCSLib` exists and is public.
- The workflow file is tracked as `.github/workflows/pages.yml` and deploys
  from `site/` on pushes to `main` that touch the site or workflow.
- The workflow uses `actions/configure-pages` with `enablement: true`, so the
  first successful deployment should configure Pages for GitHub Actions.
- No paper PDF is checked into this public repository yet.
- The default branch is `main`; broad announcement should wait until the first
  successful Pages deployment and final status review.

## Before Publishing

1. Decide whether the paper PDF should be linked externally or added as a final
   reviewed public artifact.
2. Review `site/index.html` for accurate paper status and contact text.
3. Run `python3 scripts/sync_paper_status.py --check`, then confirm
   `papers/status.json`, `docs/PAPER_STATUS.md`, and the site status table
   describe the same papers, statuses, review counts, and interface notes.
4. Run `python3 scripts/audit_repository.py` and confirm there are 0 errors.
5. Preview the static site locally, for example:

   ```bash
   python3 -m http.server 8765 --directory site
   ```

   Then check the home page.
6. Push the branch or merge it into `main`.
7. Confirm the Pages workflow deploys successfully.
8. Set the repository homepage URL to the Pages URL once the first deploy
    succeeds.

## Updating After Publication

Treat the site as a summary layer. The source of truth remains:

- paper-local `papers/<PaperName>/status.json` files for status and review
  metadata;
- generated `papers/status.json` for aggregate status;
- `README.md` and `docs/PAPER_STATUS.md` for human summaries;
- paper-local `FINAL_VALIDATION_REPORT.md` files for detailed caveats; and
- `CONTRIBUTING.md` for the contribution policy.

When a paper status changes, update the paper-local `status.json`, regenerate
the aggregate, then update the human summary layers.
